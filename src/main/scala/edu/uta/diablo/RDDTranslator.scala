/*
 * Copyright © 2020-2023 University of Texas at Arlington
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package edu.uta.diablo

import scala.annotation.tailrec

/* Translate RDD comprehensions to Spark Core API code */
object RDDTranslator {
  import AST._
  import Typechecker.{tuple=>_,_}
  import TensorTranslator._
  import SQLGenerator._
  import ComprehensionTranslator._

  /* general span for comprehensions; if a qualifier matches, split there and continue with cont */
  @tailrec
  def matchQ ( qs: List[Qualifier], filter: Qualifier => Boolean,
               cont: List[Qualifier] => Option[List[Qualifier]] ): Option[List[Qualifier]]
    = qs match {
        case q::r
          if filter(q)
          => cont(qs) match {
               case r@Some(s) => r
               case _ => matchQ(r,filter,cont)
             }
        case _::r
          => matchQ(r,filter,cont)
        case _ => None
    }

  /* Is this generator domain an RDD? Generator domains have been lifted by the Lifter */
  def isRDD ( e: Expr ): Boolean
    = e match {
        case Lift(name,_) if isBlockTensor(name) => true
        case Lift("rdd",_) => true
        case Lift("dataset",_) => true
        case Lift("block_map",_) => true
        case _ => false
      }

  def is_rdd_comprehension ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case Generator(p,u) => isRDD(u); case _ => false }

  def contains ( e: Expr, includes: Set[String], excludes: Set[String] ): Boolean = {
    val vars = freevars(e).toSet
    vars.intersect(includes).nonEmpty &&
      vars.intersect(excludes.diff(includes)).isEmpty
  }

  // for a lifted RDD storage, return the RDD collection
  def get_rdd ( e: Expr ): Expr
    = e match {
        case Lift("rdd",x) => x
        case Lift("dataset",x) => x
        case Lift(f,x)
          if isBlockTensor(f)
          => def no_rdd ( x: Expr ): Expr
               = x match { case Lift("rdd",z) => z; case _ => apply(x,no_rdd) }
             // force lifting to work on RDD directly without converting it to a list
             no_rdd(Lifting.lift(f,x))
        case Lift(f,x)
          => MethodCall(Var("spark_context"),
                        "parallelize",
                        List(Lifting.lift(f,x)))
        case _ => e
      }

  /* does e depend on vars in s? */
  def is_dependent ( s: Set[String], e: Expr ): Boolean
    = freevars(e).toSet.subsetOf(s)

  /* find all Let qualifiers in qs that depend on the variables in p */
  def dependencies ( p: Pattern, qs: List[Qualifier] ): (Set[String],List[Qualifier])
    = qs.foldLeft[(Set[String],List[Qualifier])] ((patvars(p).toSet,Nil)) {
         case ((s,r),q@LetBinding(pp,e))
           if is_dependent(s,e)
           => ( patvars(pp).toSet++s, q::r )
         case ((s,r),_) => (s,r)
      }

  /* find a dependent join ...,p1 <-e1,...,p2<-e2,... where e2 depends on p1 vars */
  def findDependentJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case (x@Generator(p1,e1))::r1
                    => val ds = patvars(p1).toSet
                       matchQ(r1,{ case Generator(_,e) if is_dependent(ds,e) => true; case _ => false },
                                 { case (y@Generator(p2,e2))::r2
                                     => val lets = dependencies(p1,r1.takeWhile(_!=y))._2
                                        Some(x::y::lets)
                                   case _ => None })
                  case _ => None })

  /* finds a sequence of predicates in qs that imply x=y */
  def findEqPred ( xs: Set[String], ys: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]] = {
    val qvars = qual_vars(qs)
    matchQ(qs,{ case Predicate(MethodCall(e1,"==",List(e2)))
                    => ((contains(e1,xs,qvars) && contains(e2,ys,qvars))
                        || (contains(e2,xs,qvars) && contains(e1,ys,qvars)))
                case _ => false },
              { case (p::s)
                  => findEqPred(xs,ys,s) match {
                          case None => Some(List(p))
                          case Some(r) => Some(p::r)
                     }
                case _ => None })
  }

  /* find the let-qualifiers that define some vars */
  def let_bindings ( vars: Set[String], qs: List[Qualifier] ): List[Qualifier]
    = qs.foldRight[(Set[String],List[Qualifier])] (vars,Nil) {
        case (q@LetBinding(p,e),(s,r))
          if patvars(p).toSet.intersect(s).nonEmpty
          => (s++freevars(e),q::r)
        case (_,(s,r)) => (s,r)
      }._2

  /* matches the equi-join ...,p1 <- e1,...,p2 <- e2,...,e3 == e4,...   */
  def findJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case (x@Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                                 { case (y@Generator(p2,e2))::r2
                                     => val lets = let_bindings(freevars(e2).toSet,
                                                                r1.takeWhile(_ != y))
                                        for { c <- findEqPred(patvars(p1).toSet,
                                                              patvars(p2).toSet,r2)
                                            } yield x::y::(c++lets)
                                   case _ => None })
                  case _ => None })

  def find_nested_term ( e: Expr, x: Qualifier, p1: Pattern,
                         r1: List[Qualifier] ): Option[List[Qualifier]]
    = e match {
        case Comprehension(h,qs)
          => matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                       { case (y@Generator(p2,e2))::r2
                           => val lets = let_bindings(freevars(e2).toSet,
                                                      r1.takeWhile(_ != y))
                              for { c <- findEqPred(patvars(p1).toSet,
                                                    patvars(p2).toSet,r2)
                                  } yield x::y::(c++lets)
                         case _ => None }).orElse(
                  accumulate[Option[List[Qualifier]]](e,find_nested_term(_,x,p1,r1),
                                                      (x,y) => x orElse y,None))
        case _ => accumulate[Option[List[Qualifier]]](e,find_nested_term(_,x,p1,r1),
                                                      (x,y) => x orElse y,None)
      }

  def find_nested_term ( x: Qualifier, p1: Pattern, r1: List[Qualifier] ): Option[List[Qualifier]]
    = r1.foldLeft[Option[List[Qualifier]]] (None) {
          case (r,Predicate(e))
            => find_nested_term(e,x,p1,r1) orElse r
          case (r,_) => r
      }

  def findNestedJoin ( head: Expr, qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case (x@Generator(p1,e1))::r1
                    => find_nested_term(x,p1,r1:+Predicate(head)) })

  /* matches the cross product ...,p1 <- e1,...,p2 <- e2,...   */
  def findCross ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case (x@Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                                 { case (y@Generator(p2,e2))::r2
                                     => val lets = let_bindings(freevars(e2).toSet,
                                                                r1.takeWhile(_ != y))
                                        Some(x::y::lets)
                                   case _ => None })
                  case _ => None })

  /* matches an RDD traversal */
  def findTraversal ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case q::_
                    => Some(q::qs.filter(_ != q))
                  case _ => None })

  def domain_size ( e: Expr ): Expr
    = e match {
        case Lift("rdd",Nth(x,3))
          => Call("array_size",List(Nth(x,1)))
        case _ => IntConst(0)
      }

  def translate_rdd_compr ( hs: Expr, qs: List[Qualifier], vars: List[String] ): Expr
    = qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
               case (r,GroupByQual(p,k)::s)        // RDD group-by becomes reduceByKey
                => val groupByVars = patvars(p)
                   // non-groupby variables used in head
                   val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val gs = rt.map(_._2)
                              .map{ case reduce(_,Var(v))
                                      => Var(v)
                                    case reduce(_,flatMap(Lambda(p,Seq(List(u))),Var(v)))
                                      => Apply(Lambda(p,u),Var(v))
                                    case e
                                      => Seq(List(e))
                                  }
                   // aggregation monoids
                   val ms = rt.map{ case (_,reduce(m,_)) => m
                                    case (_,_) => "++"
                                  }
                   // the reduceByKey merge function
                   val m = if (ms.length == 1)
                              Lambda(TuplePat(List(VarPat("_x"),VarPat("_y"))),
                                     mcall(ms.head,Var("_x"),Var("_y")))
                           else { val xs = rt.map(_ => newvar)
                                  val ys = rt.map(_ => newvar)
                                  Lambda(TuplePat(List(TuplePat(xs.map(VarPat)),
                                                       TuplePat(ys.map(VarPat)))),
                                         Tuple((ms zip (xs zip ys))
                                                 .map{ case (m,(x,y))
                                                         => mcall(m,Var(x),Var(y)) }))
                                }
                   val env = rt.map{ case (n,e) => (e,newvar) }
                   def lift ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => subst(from,Var(to),r) }
                   val Comprehension(nh,ns) = lift(yieldReductions(Comprehension(hs,s),usedVars))
                   val rtp = elemType(typecheck(Comprehension(Tuple(List(k,tuple(gs))),r)))
                   val red = MethodCall(Store("rdd",List(rtp),Nil,
                                              Comprehension(Tuple(List(k,tuple(gs))),r)),
                                        "reduceByKey",List(m,IntConst(number_of_partitions)))
                   translate_rdd_compr(nh,Generator(TuplePat(List(p,tuple(env.map(x => VarPat(x._2))))),
                                                    red)::ns,vars)
              case _
                => findJoin(qs) match {      // RDD join
                     case Some(Generator(p1,d1)::Generator(p2,d2)::rest)
                       => val qvars = qual_vars(qs)
                          val (cs,lets) = rest.span(_.isInstanceOf[Predicate])
                          val jt1 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (contains(e1,patvars(p1).toSet,qvars)) e1 else e2 })
                          val jt2 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (contains(e1,patvars(p2).toSet,qvars)) e1 else e2 })
                          val left = flatMap(Lambda(p1,Seq(List(Tuple(List(jt1,toExpr(p1)))))),
                                             get_rdd(d1))
                          val right = flatMap(Lambda(p2,Seq(List(Tuple(List(jt2,toExpr(p2)))))),
                                              get_rdd(d2))
                          val nright = lets.foldLeft[Expr](right) {
                                          case (r,LetBinding(p,e)) => Let(p,e,r)
                                          case (r,_) => r
                                       }
                          val join = if (use_map_join)
                                       Call("diablo_join",
                                            List(left,nright,domain_size(d1),domain_size(d2),
                                                 IntConst(number_of_partitions)))
                                     else MethodCall(left,"join",
                                                     List(nright,IntConst(number_of_partitions)))
                          val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("rdd",
                                                 flatMap(Lambda(TuplePat(List(VarPat("_k"),VarPat("_x"))),
                                                                Seq(List(Var("_x")))),
                                                         join)))
                          translate_rdd_compr(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z) // replace 1st generator with the join
                               case Generator(p,_) if p==p2 => Nil     // remove 2nd generator
                               case x => List(x)                       // don't remove join conditions
                              },vars)
             case _
                => findDependentJoin(qs) match {     // dependent join
                     case Some(qqs@(Generator(p1,d1)::Generator(p2,d2)::lets))
                       => val b = Seq(List(tuple(qual_vars(qqs).map(Var).toList)))
                          val pout = tuple(qual_vars(qqs).map(VarPat).toList)
                          val lb = lets.foldLeft[Expr](flatMap(Lambda(p2,b),d2)) {
                                      case (r,LetBinding(p,e)) => Let(p,e,r)
                                      case (r,_) => r
                                   }
                          val z = Generator(pout,
                                            Lift("rdd",
                                                 flatMap(Lambda(p1,lb),get_rdd(d1))))
                          val nqs = qs.flatMap {
                                      case Generator(p,_) if p==p1 => List(z) // replace 1st generator with the join
                                      case Generator(p,_) if p==p2 => Nil     // remove 2nd generator
                                      case x => List(x)
                                    }
                          translate_rdd_compr(hs,nqs,vars)
              case _
                => findNestedJoin(hs,qs) match {      // RDD dependent nested join
                     case Some(Generator(p1,d1)::(g2@Generator(p2,d2))::rest)
                       => val qvars = qual_vars(qs)
                          val (cs,lets) = rest.span(_.isInstanceOf[Predicate])
                          val jt1 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (contains(e1,patvars(p1).toSet,qvars)) e1 else e2 })
                          val jt2 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (contains(e1,patvars(p2).toSet,qvars)) e1 else e2 })
                          val left = flatMap(Lambda(p1,Seq(List(Tuple(List(jt1,toExpr(p1)))))),
                                             get_rdd(d1))
                          val right = flatMap(Lambda(p2,Seq(List(Tuple(List(jt2,toExpr(p2)))))),
                                              get_rdd(d2))
                          val nright = lets.foldLeft[Expr](right) {
                                          case (r,LetBinding(p,e)) => Let(p,e,r)
                                          case (r,_) => r
                                       }
                          val cg = if (use_map_join)
                                     Call("diablo_cogroup",
                                          List(left,nright,domain_size(d1),domain_size(d2),
                                               IntConst(number_of_partitions)))
                                   else MethodCall(left,"cogroup",
                                                   List(nright,IntConst(number_of_partitions)))
                          val ng = flatMap(Lambda(TuplePat(List(VarPat("k"),TuplePat(List(VarPat("ps"),VarPat("qs"))))),
                                                  flatMap(Lambda(VarPat("p"),Seq(List(Tuple(List(Var("p"),Var("qs")))))),
                                                          Var("ps"))),cg)
                          val p2s = newvar
                          val z = Generator(TuplePat(List(p1,VarPat(p2s))),
                                            Lift("rdd",ng))
                          def cont ( e: Expr, q: Qualifier ): Boolean
                            = e match {
                                case Comprehension(h,qs)
                                  => cont(h,q) || qs.contains(q) ||
                                        accumulate[Boolean](e,cont(_,q),_||_,false)
                                case _ => accumulate[Boolean](e,cont(_,q),_||_,false)
                              }
                          def subst ( q: Qualifier, nq: Qualifier, e: Expr ): Expr
                            = e match {
                                case Comprehension(h,qs)
                                  => Comprehension(subst(q,nq,h),
                                                   qs.map{ case x if x==q => nq
                                                           case Predicate(p)
                                                             => Predicate(subst(q,nq,p))
                                                           case x => x})
                                case _ => apply(e,subst(q,nq,_))
                              }
                          val nqs = qs.map {
                                       case Generator(p,_) if p==p1 => z
                                       case Predicate(pred) if cont(pred,g2)
                                         => Predicate(subst(g2,Generator(p2,Var(p2s)),pred))
                                       case x => x
                                    }
                          val nhs = if (cont(hs,g2))
                                      subst(g2,Generator(p2,Var(p2s)),hs)
                                    else hs
                          translate_rdd_compr(nhs,nqs,vars)
              case _
                => findCross(qs) match {     // RDD cross product
                     case Some(Generator(p1,d1)::Generator(p2,d2)::lets)
                       => val nright = lets.foldLeft[Expr](get_rdd(d2)) {
                                          case (r,LetBinding(p,e)) => Let(p,e,r)
                                          case (r,_) => r
                                       }
                          val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("rdd",
                                                 MethodCall(get_rdd(d1),
                                                            "cartesian",
                                                            List(nright))))
                          translate_rdd_compr(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z) // replace 1st generator with the cross
                               case Generator(p,_) if p==p2 => Nil     // remove 2nd generator
                               case x => List(x)
                              },vars)
             case _
               => findTraversal(qs) match {    // an RDD traversal
                     case Some(Generator(p,e)::nqs)
                       => flatMap(Lambda(p,translate_rdd_compr(hs,nqs,patvars(p)++vars)),
                                  get_rdd(e))
             case _ 
                => qs.foldRight[(Expr,List[String])] ((Seq(List(hs)),vars)) {
                      case (Generator(p,u),(r,s))
                        if isRDD(u)
                        => (flatMap(Lambda(p,r),get_rdd(u)),
                            patvars(p)++s)
                      case (Generator(p,u),(r,s))
                        => (flatMap(Lambda(p,r),u),
                            patvars(p)++s)
                      case (LetBinding(p,u),(r,s))
                        => (Let(p,u,r),
                            patvars(p)++s)
                      case (Predicate(p),(r,s))
                        => (IfE(p,r,Seq(Nil)),s)
                      case (_,(r,s)) => (r,s)
                   }._1
        } } } } }
    }

  def translate_rdd ( e: Expr, vars: List[String] ): Expr
    = e match {
        case Store("rdd",tps,args,Comprehension(hs,qs))
          if is_rdd_comprehension(qs)
          => val res = if (data_frames)
                         translate_sql(hs,qs)
                       else translate_rdd_compr(hs,qs,vars)
             if (res != e)
               translate_rdd(res,vars)
             else res
        case reduce(op,Comprehension(hs,qs))
          if is_rdd_comprehension(qs)
          => if (data_frames)
               translate_sql(hs,qs,op)
             else MethodCall(translate_rdd_compr(hs,qs,vars),
                             "reduce",
                             List(Lambda(TuplePat(List(VarPat("_x"),VarPat("_y"))),
                                         MethodCall(Var("_x"),op,List(Var("_y"))))))
        case Block(es)
          => Block(es.foldLeft[(List[Expr],List[String])] ((Nil,vars)) {
                       case ((r,s),e@VarDecl(v,u,x))
                         => (r:+translate_rdd(e,s),v::s)
                       case ((r,s),e)
                         => (r:+translate_rdd(e,s),s)
                   }._1)
        case _ => apply(e,(x:Expr) => translate_rdd(x,vars))
      }
}
