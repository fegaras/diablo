/*
 * Copyright © 2020-2021 University of Texas at Arlington
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
import scala.util.matching.Regex


object ComprehensionTranslator {
  import AST._
  import Typechecker._
  import Lifting.{store,lift}

  val ignore: Expr = Block(Nil)

  def zeroValue ( monoid: String, tp: Type ): Expr = {
    def error (): Expr = throw new Error("Wrong monoid "+monoid+" for type "+tp)
    if (tp == intType)
       monoid match { case "+" => IntConst(0); case "*" => IntConst(1); case _ => error() }
    else if (tp == longType)
       monoid match { case "+" => LongConst(0); case "*" => LongConst(1); case _ => error() }
    else if (tp == doubleType)
       monoid match { case "+" => DoubleConst(0.0); case "*" => DoubleConst(1.0); case _ => error() }
    else if (tp == boolType)
       monoid match { case "&&" => BoolConst(true); case "||" => BoolConst(false); case _ => error() }
    else error()
  }

  def optimize ( e: Expr ): Expr = Optimizer.optimizeAll(Normalizer.normalizeAll(e))

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

  def tuple ( s: List[Expr] ): Expr
    = s match { case List(x) => x; case _ => Tuple(s) }

  def tuple ( s: List[Pattern] ): Pattern
    = s match { case List(x) => x; case _ => TuplePat(s) }

  def tuple ( s: List[Type] ): Type
    = s match { case List(x) => x; case _ => TupleType(s) }

  val tensor_pat: Regex = """tensor_(\d+)_(\d+)""".r
  val bool_tensor_pat: Regex = """bool_tensor_(\d+)_(\d+)""".r

  def isTensor ( name: String ): Boolean
    = name match { case tensor_pat(_,_) => true
                   case bool_tensor_pat(_,_) => true
                   case _ => false }

  def isBoolTensor ( name: String ): Boolean
    = name match { case bool_tensor_pat(_,_) => true; case _ => false }

  def tensor_dims ( name: String ): (Int,Int)
    =  name match {
         case tensor_pat(dn,sn) => (dn.toInt,sn.toInt)
         case bool_tensor_pat(dn,sn) => (dn.toInt,sn.toInt)
         case _ => (0,0)
       }

  val block_tensor_pat: Regex = """block_tensor_(\d+)_(\d+)""".r
  val block_bool_tensor_pat: Regex = """block_bool_tensor_(\d+)_(\d+)""".r

  def isBlockTensor ( name: String ): Boolean
    = name match {
        case block_tensor_pat(_,_) => true
        case block_bool_tensor_pat(_,_) => true
        case _ => false
      }

  def comprVars ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
    }

  def isSparseTensor ( e: Expr ): Boolean
    = e match {
        case Lift(name,_)
          => name match {
                case tensor_pat(_,sn) => sn.toInt > 0
                case bool_tensor_pat(_,sn) => sn.toInt > 0
                case _ => false }
        case _ => false
      }

  /* default translator for list comprehensions with no group-by */
  def default_translator_nogb ( h: Expr, qs: List[Qualifier], vars: List[String] ): Expr
    = qs.foldRight[(Expr,List[String])]((Seq(List(translate(h,vars))),vars)) {
         case (Generator(p,u),(r,s))
           => (flatMap(Lambda(p,r),translate(u,s)),
               patvars(p)++s)
         case (LetBinding(p,u),(r,s))
           => (Let(p,translate(u,s),r),
               patvars(p)++s)
         case (Predicate(p),(r,s))
           => (IfE(translate(p,s),r,Seq(Nil)),s)
         case (AssignQual(d,u),(r,s))
           => (Block(List(Assign(d,Seq(List(u))),r)),s)
         case (_,(r,s)) => (r,s)
      }._1

  /* default translator for list comprehensions */
  def default_translator ( h: Expr, qs: List[Qualifier], vars: List[String] ): Expr
    = qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
               case (r,GroupByQual(p,k)::s)
                 => val groupByVars = patvars(p)
                    val usedVars = freevars(Comprehension(h,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                    val sv = newvar
                    val nr = default_translator(Tuple(List(k,tuple(usedVars.map(Var)))),r,vars)
                    val unzips = usedVars.map(v => LetBinding(VarPat(v),
                                                              flatMap(Lambda(tuple(usedVars.map(VarPat)),
                                                                             Seq(List(Var(v)))),
                                                                      Var(sv))))
                    default_translator(h,Generator(TuplePat(List(p,VarPat(sv))),
                                                   groupBy(nr))::(unzips++s),vars)
               case _ => default_translator_nogb(h,qs,vars)
             }

/*---------------------------- Generate tensor operations ------------------------------------------*/

  def yieldReductions ( e: Expr, vars: List[String] ): Expr
    = e match {
        case MethodCall(u@Var(v),"length",null)
          if vars.contains(v)
          => reduce("+",flatMap(Lambda(VarPat("x"),Seq(List(IntConst(1)))),u))
        case Project(u@Var(v),"length")
          if vars.contains(v)
          => reduce("+",flatMap(Lambda(VarPat("x"),Seq(List(IntConst(1)))),u))
        case _ => apply(e,yieldReductions(_,vars))
    }

  def findReducedTerms ( e: Expr, vars: List[String] ): List[(String,Expr)]
    = e match {
        case reduce(_,Var(v))
          if vars.contains(v)
          => List((v,e))
        case reduce(_,flatMap(_,Var(v)))
          if vars.contains(v)
          => List((v,e))
        case Var(v)
          if vars.contains(v)
          => List((v,e))
        case _ => accumulate[List[(String,Expr)]](e,findReducedTerms(_,vars),_++_,Nil)
      }

  /* translate a tensor comprehension with a group-by when the group-by key is equal to the head key */
  def tensor_groupby_eqkey ( tensor: String, tp: Type, dims: List[Expr], head: Expr, cqs: List[Qualifier] ): Expr = {
    val Tuple(List(key,body)) = head
    val (dn,sn) = tensor_dims(tensor)
    cqs.span{ case GroupByQual(p,k) => false; case _ => true } match {
              case (qs,GroupByQual(p,k)::ts)
                => assert(toExpr(p) == key,"The group-by key must be equal to the head key")
                   val groupByVars = patvars(p)
                   // non-groupby variables used in head
                   val usedVars = freevars(head,groupByVars).intersect(comprVars(qs)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(head,ts),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   // non-groupby variables that are used in a reduction in head
                   val reducedVars = reducedTerms.map(_._1)
                   // non-groupby variables used in head as is (not reduced)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   // the type of reduced terms
                   val reducedTermTypes = (reducedTerms.map{ case (v,u) => (v,typecheck(u)) }
                                           ++rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                               .map{ case (v,u) => (v,typecheck(u)) }).toMap
                   val ndims = dims.length
                   val vars = dims.map(x => newvar)
                   val xv = newvar    // the vector variable that contains the liftedVars values
                   // the map index in row-major format
                   val idx = dims.tail.zipWithIndex.foldLeft[Expr](Var("i1")) {
                                case (r,(e,i))
                                  => MethodCall(MethodCall(r,"*",List(e)),"+",List(Var("i"+(i+2))))
                             }
                   // the ith variable in liftedVars is computed from xv[idx].map(_.i)
                   val lvs = liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                     List(Generator(tuple(liftedVars.map(VarPat)),
                                                                    Index(Var(xv),List(idx)))))))
                   // vector values that compute all non-groupby variables in head
                   val env = reducedTerms.map{ case (v,t) => (t,Index(Var(v),List(idx))) } ++ lvs
                   // replace the reduced terms in head and ts with vector values using env
                   val Comprehension(ne,nts) = env.foldLeft(yieldReductions(Comprehension(body,ts),
                                                                            usedVars)) {
                                                   case (r,(from,to)) => AST.subst(from,to,r)
                                               }
                   // all vectors used in aggregations are vectors of size d1*d2*...
                   def vector_decl ( v: String, tp: Type )
                     = VarDecl(v,ArrayType(1,tp),
                               Seq(List(Call("array",List(dims.reduce[Expr] {
                                             case (x,y) => MethodCall(x,"*",List(y))
                                           })))))
                   // vector declarations; xv vector is not needed if the head is a single aggregation
                   val init = (if (liftedVars.isEmpty) Nil
                               else List(vector_decl(xv,TupleType(liftedVars.map(reducedTermTypes(_)))))) ++
                              reducedVars.map(v => vector_decl(v,reducedTermTypes(v)))
                   // append the lifted variables not reduced to xv[idx]
                   val xvincr = if (liftedVars.isEmpty) Nil
                                else List(AssignQual(Index(Var(xv),List(idx)),
                                                     MethodCall(Index(Var(xv),List(idx)),
                                                                ":+",
                                                                List(tuple(liftedVars.map(Var))))))
                   // one vector update for each reduction
                   val incr = reducedTerms.flatMap {
                                case (v,reduce(m,flatMap(Lambda(p,Seq(List(u))),x)))
                                  => List(AssignQual(Index(Var(v),List(idx)),
                                                     MethodCall(Index(Var(v),List(idx)),
                                                                m,
                                                                List(Apply(Lambda(p,u),x)))))
                                case (v,reduce(m,x))
                                  => List(AssignQual(Index(Var(v),List(idx)),
                                                     MethodCall(Index(Var(v),List(idx)),
                                                                m,
                                                                List(x))))
                                case _ => Nil
                              }
                   // the traversal indices are i1, i2, ... with i1<d1, i2<d2, ...
                   val conds = dims.zipWithIndex.map {
                                  case (d,i) => Predicate(MethodCall(Var("i"+(i+1)),"<",List(d)))
                               }
                   val nqs = qs++(LetBinding(tuple(1.to(ndims).map(i => VarPat("i"+i)).toList),k)::
                                  conds++xvincr++incr)
                   val b = ne match {
                             case Index(Var(v),_)
                               if reducedVars.contains(v) && ts.isEmpty
                               => Block(init ++ List(Comprehension(ignore,nqs++nts),
                                                     Var(reducedVars.head)))
                             case _
                               // when there are more qualifiers after group-by
                               // or the head value is not a simple aggregation
                               => val rv = newvar   // vector rv holds head value
                                  val rs = dims.zipWithIndex.map {   // range over all indices
                                              case (d,i) => Generator(VarPat("i"+(i+1)),
                                                                 Range(IntConst(0),
                                                                       MethodCall(d,"-",List(IntConst(1))),
                                                                       IntConst(1)))
                                           }
                                  Block(VarDecl(rv,ArrayType(1,tp),
                                                Seq(List(Call("array",List(dims.reduce[Expr] {
                                                       case (x,y) => MethodCall(x,"*",List(y))
                                                     })))))::
                                        init ++ List(Comprehension(ignore,nqs),
                                                     Comprehension(Assign(Index(Var(rv),List(idx)),ne),
                                                                   rs++nts),
                                                     Var(rv)))
                           }
                   val res = if (sn == 0)
                               tuple(dims:+b)    // the result is a dense tensor
                             else { val vv = newvar
                                    val iv = newvar
                                    val ivars = tuple(1.to(ndims).map(i => Var("i"+i)).toList)
                                    val pvars = tuple(1.to(ndims).map(i => VarPat("i"+i)).toList)
                                    // copy the dense result to a sparse tensor
                                    Block(List(VarDecl(vv,StorageType(s"tensor_${ndims}_0",List(tp),dims),
                                                       Seq(List(tuple(dims:+b)))),
                                               Store(tensor,List(tp),dims,
                                                     Comprehension(Tuple(List(ivars,Var(iv))),
                                                             List(Generator(TuplePat(List(pvars,
                                                                                     VarPat(iv))),
                                                                            Lift(s"tensor_${ndims}_0",
                                                                                 Var(vv))))))))
                                  }
                   translate(res,vars)
              case _ => default_translator(head,cqs,Nil)
            }
    }

  /* translate a tensor comprehension with a group-by when the group-by key is NOT equal to the head key */
  def tensor_groupby_neqkey ( tensor: String, tp: Type, dims: List[Expr], head: Expr, cqs: List[Qualifier] ): Expr = {
    val Tuple(List(key,body)) = head
    val result_keys = key match { case Tuple(ks) => ks; case _ => List(key) }
    val (dn,sn) = tensor_dims(tensor)
    cqs.span{ case GroupByQual(p,k) => false; case _ => true } match {
              case (qs,GroupByQual(p,k)::ts)
                => val groupByVars = patvars(p)
                   // non-groupby variables used in head
                   val usedVars = freevars(head,groupByVars).intersect(comprVars(qs)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(head,ts),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   // non-groupby variables that are used in a reduction in head
                   val reducedVars = reducedTerms.map(_._1)
                   // non-groupby variables used in head as is (not reduced)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   // the type of reduced terms
                   val reducedTermTypes = (reducedTerms.map{ case (v,u) => (v,typecheck(u)) }
                                           ++rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                               .map{ case (v,u) => (v,typecheck(u)) }).toMap
                   val ndims = dims.length
                   val vars = dims.map(x => newvar)
                   val xv = newvar    // the vector variable that contains the liftedVars values
                   // the map index in row-major format
                   val idx = dims.tail.zipWithIndex.foldLeft[Expr](Var("i1")) {
                                case (r,(e,i))
                                  => MethodCall(MethodCall(r,"*",List(e)),"+",List(Var("i"+(i+2))))
                             }
                   // the ith variable in liftedVars is computed from xv[idx].map(_.i)
                   val lvs = liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                     List(Generator(tuple(liftedVars.map(VarPat)),
                                                                    MapAccess(Var(xv),idx))))))
                   // vector values that compute all non-groupby variables in head
                   val env = reducedTerms.map{ case (v,t) => (t, MapAccess(Var(v),idx)) } ++ lvs
                   // replace the reduced terms in head with vector values using env
                   val Comprehension(ne,nts) = env.foldLeft(yieldReductions(Comprehension(body,ts),
                                                                            usedVars)) {
                                                   case (r,(from,to)) => AST.subst(from,to,r)
                                               }
                   // all collections used in aggregations are Maps
                   def map_decl ( v: String, tp: Type )
                     = VarDecl(v,MapType(intType,tp),Seq(List(Call("map",Nil))))
                   // map declarations; xv vector is not needed if the head is a single aggregation
                   val init = (if (liftedVars.isEmpty) Nil
                               else List(map_decl(xv,TupleType(liftedVars.map(reducedTermTypes(_)))))) ++
                              reducedVars.map(v => map_decl(v,reducedTermTypes(v)))
                   // append the lifted variables not reduced to xv[idx]
                   val xvincr = if (liftedVars.isEmpty) Nil
                                else List(AssignQual(MapAccess(Var(xv),idx),
                                                     IfE(MethodCall(Var(xv),"contains",List(idx)),
                                                         MethodCall(MapAccess(Var(xv),idx),
                                                                    ":+",
                                                                    List(tuple(liftedVars.map(Var)))),
                                                         Seq(List(tuple(liftedVars.map(Var)))))))
                   // one vector update for each reduction
                   val incr = reducedTerms.flatMap {
                                case (v,reduce(m,flatMap(Lambda(p,Seq(List(u))),x)))
                                  => List(AssignQual(MapAccess(Var(v),idx),
                                                     IfE(MethodCall(Var(v),"contains",List(idx)),
                                                         MethodCall(MapAccess(Var(v),idx),
                                                                    m,
                                                                    List(Apply(Lambda(p,u),x))),
                                                         Apply(Lambda(p,u),x))))
                                case (v,reduce(m,x))
                                  => List(AssignQual(MapAccess(Var(v),idx),
                                                     IfE(MethodCall(Var(v),"contains",List(idx)),
                                                         MethodCall(MapAccess(Var(v),idx),
                                                                    m,
                                                                    List(x)),
                                                         x)))
                                case _ => Nil
                              }
                   // the new comprehension qualifiers
                   val nqs = qs++(LetBinding(tuple(1.to(ndims).map(i => VarPat("i"+i)).toList),key)::
                                  xvincr++incr)
                   val rv = newvar
                   val rs = dims.zipWithIndex.map {   // range over all indices
                               case (d,i) => Generator(VarPat("i"+(i+1)),
                                                       Range(IntConst(0),
                                                             MethodCall(d,"-",List(IntConst(1))),
                                                             IntConst(1)))
                                             }
                   val conds = reducedTerms.map {
                                  case (v,t)
                                    => Predicate(MethodCall(Var(v),"contains",List(idx)))
                               }
                   val b = Block(VarDecl(rv,ArrayType(1,tp),
                                                Seq(List(Call("array",List(dims.reduce[Expr] {
                                                       case (x,y) => MethodCall(x,"*",List(y))
                                                     })))))::
                                        init ++ List(Comprehension(ignore,nqs),
                                                     Comprehension(Assign(Index(Var(rv),List(idx)),ne),
                                                                   rs++conds++nts),
                                                     Var(rv)))
                   val res = if (sn == 0)
                               tuple(dims:+b)    // the result is already a dense tensor
                             else { val vv = newvar
                                    val iv = newvar
                                    val ivars = tuple(1.to(ndims).map(i => Var("i"+i)).toList)
                                    val pvars = tuple(1.to(ndims).map(i => VarPat("i"+i)).toList)
                                    // copy the dense result to a sparse tensor
                                    Block(List(VarDecl(vv,StorageType(s"tensor_${ndims}_0",List(tp),dims),
                                                       Seq(List(tuple(dims:+b)))),
                                               Store(tensor,List(tp),dims,
                                                     Comprehension(Tuple(List(ivars,Var(iv))),
                                                             List(Generator(TuplePat(List(pvars,
                                                                                     VarPat(iv))),
                                                                            Lift(s"tensor_${ndims}_0",
                                                                                 Var(vv))))))))
                                  }
                   translate(res,vars)
              case _ => default_translator(head,cqs,Nil)
            }
    }

/*---------------------------- Generate RDD operations ------------------------------------------*/

  /* Is this generator domain an RDD? Generator domains have been lifted by the Lifter */
  def isRDD ( e: Expr ): Boolean
    = e match {
        case Lift(name,_) if isBlockTensor(name) => true
        case Lift("rdd",_) => true
        case _ => false
      }

  def is_rdd_comprehension ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case Generator(p,u) => isRDD(u); case _ => false }

  def subsetOrEq ( e: Expr, s: Set[String] ): Boolean = {
    val r = freevars(e).toSet
    r == s || r.subsetOf(s)
  }

  // for a lifted RDD storage, return the RDD collection
  def get_rdd ( e: Expr ): Expr
    = e match {
        case Lift(block_tensor_pat(dn,sn),x)
          => Nth(x,dn.toInt+sn.toInt+1)
        case Lift(block_bool_tensor_pat(dn,sn),x)
          => Nth(x,dn.toInt+sn.toInt+1)
        case Lift("rdd",x) => x
        case _ => e
      }

  def block_arrays_to_rdds ( qs: List[Qualifier] ): List[Qualifier]
    = qs.flatMap {
               case Generator(p,Lift(f@block_tensor_pat(dn,sn),x))
                 => List(Generator(p,lift(f,x)))
               case Generator(p,Lift(f@block_bool_tensor_pat(dn,sn),x))
                 => List(Generator(p,lift(f,x)))
               case q => List(q)
             }

  /* finds a sequence of predicates in qs that refer to the pattern variables xs */
  def findFilterPred ( xs: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Predicate(e)
                    => subsetOrEq(e,xs)
                  case _ => false },
                { case (p::s)
                    => findFilterPred(xs,s) match {
                          case None => Some(List(p))
                          case Some(r) => Some(p::r)
                       }
                  case _ => None })

  def findFilter ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case (Generator(p,e))::r
                    => findFilterPred(patvars(p).toSet,r) match {
                         case Some(ps)
                           => Some(Generator(p,get_rdd(e))::ps)
                         case _ => None }
                  case _ => None })

  /* finds a sequence of predicates in qs that imply x=y */
  def findEqPred ( xs: Set[String], ys: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Predicate(MethodCall(e1,"==",List(e2)))
                    => ((subsetOrEq(e1,xs) && subsetOrEq(e2,ys))
                        || (subsetOrEq(e2,xs) && subsetOrEq(e1,ys)))
                  case _ => false },
                { case (p::s)
                    => findEqPred(xs,ys,s) match {
                          case None => Some(List(p))
                          case Some(r) => Some(p::r)
                       }
                  case _ => None })

  /* matches the equi-join ...,p1 <- e1,...,p2 <- e2,...,e3 == e4,...   */
  def findJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case Generator(p1,e1)::r1
                    => matchQ(r1,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                                 { case (Generator(p2,e2))::r2
                                     => for { c <- findEqPred(patvars(p1).toSet,
                                                              patvars(p2).toSet,r2)
                                            } yield Generator(p1,e1)::Generator(p2,e2)::c
                                  case _ => None })
                  case _ => None })

  /* matches the cross product ...,p1 <- e1,...,p2 <- e2,...   */
  def findCross ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case Generator(p1,Lift(_,e1))::r1
                    => matchQ(r1,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                                 { case Generator(p2,Lift(_,e2))::r2
                                     => Some(List(Generator(p1,e1),
                                                  Generator(p2,e2)))
                                  case _ => None })
                  case _ => None })

  @tailrec
  def translate_rdd ( hs: Expr, qs: List[Qualifier], vars: List[String] ): Expr
    = findFilter(qs) match {
        case Some(Generator(p,e)::ps)
          if false   // disabled
          => val pred = ps.flatMap{ case Predicate(p) => List(p); case _ => Nil }
                          .reduce{ (x,y) => MethodCall(x,"&&",List(y)) }
             val z = Generator(p,Lift("rdd",MethodCall(e,"filter",List(Lambda(p,pred)))))
             translate_rdd(hs,qs.flatMap {
                               case Generator(np,_) if np==p => List(z)
                               case x => if (ps.contains(x)) Nil else List(x)
                              },vars)
        case _
          => qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
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
                              Lambda(TuplePat(List(VarPat("x"),VarPat("y"))),
                                     MethodCall(Var("x"),ms.head,List(Var("y"))))
                           else { val xs = rt.map(_ => newvar)
                                  val ys = rt.map(_ => newvar)
                                  Lambda(TuplePat(List(TuplePat(xs.map(VarPat)),
                                                       TuplePat(ys.map(VarPat)))),
                                         Tuple((ms zip (xs zip ys))
                                                 .map{ case (m,(x,y))
                                                         => MethodCall(Var(x),m,List(Var(y))) }))
                                }
                   val env = rt.map{ case (n,e) => (e,newvar) }
                   def lift ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,Var(to),r) }
                   val Comprehension(nh,ns) = lift(Comprehension(hs,s))
                   val red = MethodCall(Store("rdd",Nil,Nil,
                                              Comprehension(Tuple(List(toExpr(p),tuple(gs))),r)),
                                        "reduceByKey",List(m))
                   translate_rdd(nh,Generator(TuplePat(List(p,tuple(env.map(x => VarPat(x._2))))),
                                                      red)::ns,vars)
              case _
                => findJoin(qs) match {      // RDD join
                     case Some((Generator(p1,d1))::(Generator(p2,d2))::cs)
                       => val jt1 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (subsetOrEq(e1,patvars(p1).toSet)) e1 else e2 })
                          val jt2 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (subsetOrEq(e1,patvars(p2).toSet)) e1 else e2 })
                          val left = flatMap(Lambda(p1,Seq(List(Tuple(List(jt1,toExpr(p1)))))),
                                             get_rdd(d1))
                          val right = flatMap(Lambda(p2,Seq(List(Tuple(List(jt2,toExpr(p2)))))),
                                              get_rdd(d2))
                          val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("rdd",
                                                 flatMap(Lambda(TuplePat(List(VarPat("_k"),VarPat("x"))),
                                                                Seq(List(Var("x")))),
                                                         MethodCall(left,"join",List(right)))))
                          translate_rdd(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z) // replace 1st generator with the join
                               case Generator(p,_) if p==p2 => Nil     // remove 2nd generator
                               case x => List(x)                       // don't remove join conditions
                              },vars)
              case _
                => findCross(qs) match {     // RDD cross product
                     case Some(List(Generator(p1,d1),Generator(p2,d2)))
                       => val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("rdd",
                                                 MethodCall(get_rdd(d1),
                                                            "cartesian",
                                                            List(get_rdd(d2)))))
                          translate_rdd(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z) // replace 1st generator with the cross
                               case Generator(p,_) if p==p2 => Nil     // remove 2nd generator
                               case x => List(x)
                              },vars)
                     case _ 
                       => qs.foldRight[(Expr,List[String])]((Seq(List(translate(hs,vars))),vars)) {
                             case (Generator(p,u),(r,s))
                               => (flatMap(Lambda(p,r),get_rdd(u)),
                                   patvars(p)++s)
                             case (LetBinding(p,u),(r,s))
                               => (Let(p,translate(u,vars),r),
                                   patvars(p)++s)
                             case (Predicate(p),(r,s))
                               => (IfE(translate(p,s),r,Seq(Nil)),s)
                             case (_,(r,s)) => (r,s)
                          }._1
                   }
                }
          }
    }

/*---------------------------- Distributed Arrays as Tiled RDDs ------------------------------------------*/

  /* Is this generator domain a Tiled RDD? Generator domains have been lifted by the Lifter */
  def isTiled ( e: Expr ): Boolean
    = e match {
        case Lift(name,_) if isBlockTensor(name) => true
        case _ => false
      }

  def is_tiled_comprehension ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case Generator(p,u) => isTiled(u); case _ => false }

  def hasGroupBy ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case GroupByQual(_,_) => true; case _ => false }

  def hasGroupByKey ( qs: List[Qualifier], key: Expr ): Boolean
    = qs.exists{ case GroupByQual(p,_) => key == toExpr(p); case _ => false }

  def preserves_tiling ( hs: List[Expr], qs: List[Qualifier] ): Boolean
    = hs match {
        case List(Tuple(List(k,_)))
          if hasGroupByKey(qs,k)
          => true
        case List(Tuple(List(p,_)))
          if !hasGroupBy(qs)
          => val indices = tile_indices(qs)
             freevars(p).forall(indices.contains(_))
        case _ => false
      }

  def tile_indices ( p: Pattern ): List[String]
    = p match {
        case TuplePat(List(VarPat(v),_))
          => List(v)
        case TuplePat(List(TuplePat(ps),_))
          if ps.forall(_.isInstanceOf[VarPat])
          => ps.flatMap{ case VarPat(v) => List(v); case _ => Nil }
        case TuplePat(ps)
          => ps.flatMap(tile_indices)
        case _ => Nil
      }

  def tile_indices ( qs: List[Qualifier] ): List[String]
    = qs.flatMap{ case Generator(p,u) if isTiled(u) => tile_indices(p); case _ => Nil }

  def tile_values ( p: Pattern ): List[String]
    = p match {
        case TuplePat(List(VarPat(_),p))
          => patvars(p)
        case TuplePat(List(TuplePat(ps),p))
          if ps.forall(_.isInstanceOf[VarPat])
          => patvars(p)
        case TuplePat(ps)
          => ps.flatMap(tile_values)
        case _ => Nil
      }

  def tile_values ( qs: List[Qualifier] ): List[String]
    = qs.flatMap{ case Generator(p,u) if isTiled(u) => tile_values(p); case _ => Nil }

  def usc ( p: Pattern ): Pattern
    = p match {
        case VarPat(v)
          => VarPat("_"+v)
        case _ => apply(p,usc)
      }

  def uscv ( p: Pattern ): Pattern
    = p match {
        case TuplePat(List(VarPat(_),p))
          => usc(p)
        case TuplePat(List(TuplePat(ps),p))
          if ps.forall(_.isInstanceOf[VarPat])
          => usc(p)
        case TuplePat(ps)
          => tuple(ps.map(uscv))
        case _ => p
      }

  def usciv ( p: Pattern ): Pattern
    = p match {
        case TuplePat(List(i@VarPat(_),p))
          => TuplePat(List(i,usc(p)))
        case TuplePat(List(i@TuplePat(ps),p))
          if ps.forall(_.isInstanceOf[VarPat])
          => TuplePat(List(i,usc(p)))
        case TuplePat(ps)
          => TuplePat(ps.map(usciv))
        case _ => p
      }

  def tile_type ( block: String ): String
    = block match {
        case block_tensor_pat(dn,sn)
          => s"tensor_${dn}_$sn"
        case block_bool_tensor_pat(dn,sn)
          => "bool_tensor_${dn}_$sn"
      }

  def tile_type ( block: String, tp: Type ): String = {
    val isBool = tp == boolType
    block match {
        case block_tensor_pat(dn,sn)
          => if (isBool)
               s"bool_tensor_${dn}_$sn"
              else s"tensor_${dn}_$sn"
        case block_bool_tensor_pat(dn,sn)
          => if (isBool)
               s"bool_tensor_${dn}_$sn"
              else s"tensor_${dn}_$sn"
      }
  }

  def tile_generators ( block: String, p: Pattern ): List[Qualifier]
    = p match {
        case TuplePat(List(VarPat(_),VarPat(v)))
          => List(Generator(p,Lift(block,Var("_"+v))))
        case TuplePat(List(TuplePat(List(VarPat(_),VarPat(_))),VarPat(v)))
          => List(Generator(p,Lift(block,Var("_"+v))))
        case TuplePat(ps)
          => ps.flatMap(tile_generators(block,_))
        case _ => Nil
      }

  def local_expr ( e: Expr, vars: List[String] ): Boolean
    = freevars(e,vars).isEmpty

  def tile_qualifiers ( qs: List[Qualifier], vars: List[String] ): List[Qualifier]
    = qs.foldLeft[(List[Qualifier],List[String])] ((Nil,vars)) {
          case ((r,s),Generator(p,Lift(block,_)))
            if isBlockTensor(block)
            => (r++tile_generators(tile_type(block),p),
                s++patvars(p))
          case ((r,s),q@LetBinding(p,e))
            if local_expr(e,s)
            => (r:+q,s++patvars(p))
          case ((r,s),q@Predicate(e))
            if local_expr(e,s)
            => (r:+q,s)
          case ((r,s),_) => (r,s)
      }._1

  def rdd_qualifiers ( qs: List[Qualifier], vars: List[String] ): List[Qualifier]
    = qs.foldLeft[(List[Qualifier],List[String])] ((Nil,vars)) {
          case ((r,s),Generator(p,Lift(block_tensor_pat(dn,sn),e)))
            => (r:+Generator(usciv(p),Lift("rdd",Nth(e,dn.toInt+sn.toInt+1))),
                s++tile_indices(p))
          case ((r,s),Generator(p,Lift(block_bool_tensor_pat(dn,sn),e)))
            => (r:+Generator(usciv(p),Lift("rdd",Nth(e,dn.toInt+sn.toInt+1))),
                s++tile_indices(p))
          case ((r,s),q@Generator(p,Lift("rdd",_)))
            => (r:+q,s++patvars(p))
          case ((r,s),q@LetBinding(p,e))
            if local_expr(e,s)
            => (r:+q,s++patvars(p))
          case ((r,s),q@Predicate(e))
            if local_expr(e,s)
            => (r:+q,s)
          case ((r,s),_) => (r,s)
      }._1

  def tiles_var ( p: Pattern ): String
    = "_"+tile_values(p).mkString("_")

  def tile_qualifiers_shuffle ( qs: List[Qualifier], vars: List[String] ): List[Qualifier]
    = qs.foldLeft[(List[Qualifier],List[String])] ((Nil,vars)) {
          case ((r,s),Generator(p,Lift(block,_)))
            if isBlockTensor(block)
            => ((r:+Generator(usc(p),Var(tiles_var(p))))
                ++tile_generators(tile_type(block),p),
                s++patvars(p))
          case ((r,s),q@LetBinding(p,e))
            if local_expr(e,s)
            => (r:+q,s++patvars(p))
          case ((r,s),q@Predicate(e))
            if local_expr(e,s)
            => (r:+q,s)
          case ((r,s),_) => (r,s)
      }._1

  def rdd_qualifiers_shuffle ( qs: List[Qualifier], vars: List[String] ): List[Qualifier]
    = qs.foldLeft[(List[Qualifier],List[String])] ((Nil,vars)) {
          case ((r,s),Generator(p,e@Lift(block,_)))
            if isBlockTensor(block)
            => (r++List(Generator(usciv(p),e),
                        LetBinding(VarPat(tiles_var(p)),toExpr(usciv(p)))),
                s++tile_indices(p))
          case ((r,s),q@Generator(p,Lift("rdd",_)))
            => (r:+q,s++patvars(p))
          case ((r,s),q@LetBinding(p,e))
            if local_expr(e,s)
            => (r:+q,s++patvars(p))
          case ((r,s),q@Predicate(e))
            if local_expr(e,s)
            => (r:+q,s)
          case ((r,s),_) => (r,s)
      }._1

  /* shuffle the tiles of a tiled comprehension */
  def shuffle_tiles ( block: String, hs: Expr, qs: List[Qualifier], group_by: Boolean,
                      vars: List[String], tp: Type, dims: List[Expr], tile_dims: List[Expr] ): Expr
    = hs match {
        case Tuple(List(Tuple(ks),h))
          => val N = IntConst(blockSize)
             val range = Range(IntConst(0),IntConst(blockSize-1),IntConst(1))
             val fs = tile_indices(qs)
             val vs = ks.map{ _ => newvar }
             def gkeys ( op: String ): List[Expr]
               = (ks zip vs).map {
                      case (k,vk)
                        => val is = freevars(k,Nil).intersect(fs)
                           val gk = is.map{ v => (v,MethodCall(MethodCall(Var("_"+v),"*",List(N)),
                                                               "+",List(Var(v)))) }
                           MethodCall(gk.foldLeft[Expr](k){ case (r,(v,e)) => subst(v,e,r) },
                                      op,List(N))
                      }
             val tiles = (ks zip vs zip gkeys("/")).map {
                            case ((Var(v),vk),_)
                              => LetBinding(VarPat(vk),Var("_"+v))
                            case ((k,vk),gkey)
                              => val is = freevars(k,Nil).intersect(fs)
                                 Generator(VarPat(vk),
                                           Comprehension(Var(vk),
                                                         is.map{ v => Generator(VarPat(v),range) }:+
                                                            GroupByQual(VarPat(vk),gkey)))
                         }
             val rqs = rdd_qualifiers_shuffle(qs,vars)++tiles:+
                               GroupByQual(TuplePat(vs.map(VarPat)),
                                           Tuple(vs.map(Var)))
             val tqs = if (group_by)
                         List(GroupByQual(TuplePat(ks.map{ case Var(v) => VarPat(v); case _ => VarPat("") }),
                                          Tuple(ks)))
                       else (vs zip gkeys("/")).map {
                               case (vk,gkey)
                                 => Predicate(MethodCall(Var(vk),"==",List(gkey)))
                            }
             val guards = (ks zip vs zip tile_dims).flatMap {
                            case ((k,vk),d)
                              if !group_by
                              => val is = freevars(k,Nil).intersect(fs)
                                 is.map{ v => Predicate(MethodCall(MethodCall(MethodCall(Var("_"+v),"*",List(N)),
                                                                              "+",List(Var(v))),
                                                                   "<",List(d))) }
                            case _ => Nil
                          }
             val tile = Store(tile_type(block,tp),List(tp),tile_dims,
                              Comprehension(Tuple(List(Tuple(if (group_by) ks else gkeys("%")),h)),
                                            tile_qualifiers_shuffle(qs,vars)++guards++tqs))
             val rdd = translate_rdd(Tuple(List(Tuple(vs.map(Var)),tile)),rqs,vars)
             translate(Tuple(dims:+rdd),vars)
    }

  /* a group-by on tiled arrays */
  def groupBy_tiles ( block: String, hs: Expr, qs: List[Qualifier], vars: List[String],
                      tp: Type, dims: List[Expr], tile_dims: List[Expr] ): Expr
    = hs match {
        case Tuple(List(kp,head))
          => qs.span{ case GroupByQual(gp,_) => toExpr(gp) != kp; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val tileType = tile_type(block,tp)
                   val ndims = dims.length
                   val groupByVars = patvars(p)
                   // non-groupby variables used in head
                   val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val h = yieldReductions(head,usedVars)
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
                   val ms = rt.map{ case (_,reduce(m,_)) => m
                                    case (_,_) => "++"
                                  }
                   val msTypes = rt.map{ case (v,u) => typecheck(u) }
                   def nvar ( s: String ) = 1.to(ndims).map(i => Var(s+i)).toList
                   def nvarp ( s: String ) = 1.to(ndims).map(i => VarPat(s+i)).toList
                   def combine ( x: String, y: String, m: String, tp: Type ): Expr = {
                     val tileType =  tile_type(block,tp)
                     val cb = Store(tileType,List(tp),tile_dims,
                             Comprehension(Tuple(List(tuple(nvar("i")),
                                                      MethodCall(Var("v"),m,List(Var("w"))))),
                                           List(Generator(TuplePat(List(tuple(nvarp("i")),
                                                                        VarPat("v"))),
                                                          Lift(tileType,Var(x))),
                                                Generator(TuplePat(List(tuple(nvarp("j")),
                                                                        VarPat("w"))),
                                                          Lift(tileType,Var(y))))
                                           ++1.to(ndims).map(i => Predicate(MethodCall(Var("j"+i),
                                                                         "==",List(Var("i"+i)))))))
                     val ctp = TupleType((1 to ndims).map(i => intType).toList:+ArrayType(1,tp))
                     typecheck(cb,Map(x->ctp,y->ctp))  // needed to set array type
                     cb
                   }
                   val md = h match {
                              case reduce(_,_)
                                => Lambda(TuplePat(List(VarPat("x"),VarPat("y"))),
                                          combine("x","y",ms.head,msTypes.head))
                              case _
                                => { val xs = rt.map(_ => newvar)
                                     val ys = rt.map(_ => newvar)
                                     Lambda(TuplePat(List(TuplePat(xs.map(VarPat)),
                                                          TuplePat(ys.map(VarPat)))),
                                            Tuple((ms zip msTypes zip (xs zip ys))
                                                      .map{ case ((m,tp),(x,y))
                                                              => combine(x,y,m,tp) } ))
                                   }
                            }
                   val rqs = rdd_qualifiers(qs,vars)
                   val tiles = (rt zip msTypes).map {
                                 case ((_,u),tp)
                                   => val tileType =  tile_type(block,tp)
                                      Store(tileType,List(tp),tile_dims,
                                            Comprehension(Tuple(List(toExpr(p),u)),
                                                          (tile_qualifiers(r,vars):+GroupByQual(p,k))
                                                          ++s))
                               }
                   val rdd =  MethodCall(translate_rdd(Tuple(List(k,tuple(tiles))),rqs,vars),
                                         "reduceByKey",List(md))
                   val env = rt.map{ case (n,e) => (e,newvar) }
                   def liftExpr ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,Var(to+"_"),r) }
                   val liftedTile
                     = liftExpr(h) match {
                         case Var(v)
                           => Var(v.dropRight(1))
                         case nh
                         => Store(tileType,List(tp),tile_dims,
                                  Comprehension(Tuple(List(tuple(nvar("i0_")),nh)),
                               env.map(_._2).zip(msTypes).zipWithIndex.flatMap {
                                  case ((v,tp),i)
                                    => val tileType =  tile_type(block,tp)
                                       Generator(TuplePat(List(tuple(nvarp("i"+i+"_")),
                                                               VarPat(v+"_"))),
                                                 Lift(tileType,Var(v)))::
                                       (if (i > 0)
                                          1.to(ndims).map(j => Predicate(MethodCall(Var("i"+i+"_"+j),
                                                                   "==",List(Var("i0_"+j))))).toList
                                        else Nil)
                               }))
                     }
                   val res = translate_rdd(Tuple(List(kp,liftedTile)),
                                           List(Generator(TuplePat(List(p,tuple(env.map(x => VarPat(x._2))))),
                                                          rdd)),vars)
                   translate(Tuple(dims:+res),vars)
            case _ => throw new Error("")
          }
    }

  def findJoinGBKeys ( xs: Set[String], ys: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Predicate(MethodCall(e1,"==",List(e2)))
                    => ((subsetOrEq(e1,xs) && subsetOrEq(e2,ys))
                        || (subsetOrEq(e2,xs) && subsetOrEq(e1,ys)))
                  case GroupByQual(p,Tuple(List(gx,gy)))
                    if ((subsetOrEq(gx,xs) && subsetOrEq(gy,ys))
                        || (subsetOrEq(gy,xs) && subsetOrEq(gx,ys)))
                    => true
                  case _ => false },
                { case (p@Predicate(MethodCall(e1,"==",List(e2))))::s
                    => findJoinGBKeys(xs,ys,s) match {
                          case None => None
                          case Some(l) => Some(p::l)
                       }
                  case (g@GroupByQual(p,Tuple(List(gx,gy))))::_
                    => Some(List(g))
                  case _::_ => None
                })

  def findGroupByJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = if (qs.map{ case Generator(_,u) if isTiled(u) => 1; case _ => 0 }.sum != 2) None
      else matchQ(qs,{ case Generator(_,e1) if isTiled(e1) => true; case _ => false },
                { case (g1@Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e2) if isTiled(e2) => true; case _ => false },
                                 { case (g2@Generator(p2,e2))::r2
                                     => findJoinGBKeys(patvars(p1).toSet,patvars(p2).toSet,r2) match {
                                           case Some(l) => Some(g1::g2::l)
                                           case _ => None
                                        }
                                  case _ => None })
                  case _ => None })


  /* matches the equi-join ...,p1 <- e1,...,p2 <- e2,...,e3 == e4,...   */
  def findTileJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                { case (Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                                 { case (Generator(p2,e2))::r2
                                     => for { c <- findEqPred(patvars(p1).toSet,patvars(p2).toSet,r2)
                                            } yield Generator(p1,e1)::Generator(p2,e2)::c
                                  case _ => None })
                  case _ => None })

  /* matches the cross product ...,p1 <- e1,...,p2 <- e2,...   */
  def findTileCross ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                { case (Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                                 { case (Generator(p2,e2))::r2
                                     => Some(List(Generator(p1,e1),Generator(p2,e2)))
                                  case _ => None })
                  case _ => None })

  var QLcache: Option[List[Qualifier]] = None

  def translate_tiled ( block: String, hs: Expr, qs: List[Qualifier], vars: List[String],
                        tp: Type, dims: List[Expr] ): Expr = {
    val N = Math.pow(blockSize,1.0/(dims.length)).toInt
    val tile_dims = 1.to(dims.length).map(i => IntConst(N)).toList
    hs match {
      case Tuple(List(p,_))   // a tiled comprehension that preserves tiling
        if !hasGroupBy(qs)
           && { val indices = tile_indices(qs)      // TODO: all other indices must be ==
                indices.nonEmpty && freevars(p).forall(indices.contains(_)) }
        => val tile = Store(tile_type(block,tp),List(tp),tile_dims,
                            Comprehension(hs,tile_qualifiers(qs,vars)))
           tuple(dims:+translate_rdd(Tuple(List(p,tile)),rdd_qualifiers(qs,vars),vars))
        case Tuple(List(Tuple(ks),_))   // a tiled comprehension that doesn't preserve tiling
          if !hasGroupBy(qs) && tile_indices(qs).nonEmpty
          => shuffle_tiles(block,hs,qs,false,vars,tp,dims,tile_dims)
        case _
          if groupByJoin && { QLcache = findGroupByJoin(qs); QLcache.nonEmpty }
          => QLcache match {          // group-by join
               case Some((g1@Generator(p1,d1))::(g2@Generator(p2,d2))
                             ::(cs:+(g@GroupByQual(p,k@Tuple(List(gx,gy))))))
                 => val jt1 = cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                              => if (subsetOrEq(e1,patvars(p1).toSet)) e1 else e2
                                            case _ => d1 }
                    val jt2 = cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                              => if (subsetOrEq(e1,patvars(p2).toSet)) e1 else e2
                                            case _ => d1 }
                    val (ngx,ngy) = if (subsetOrEq(gx,patvars(p1).toSet)) (gx,gy) else (gy,gx)
                    val (r,_::s) = qs.span(_ != g)
                    val groupByVars = patvars(p)
                    val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                          .intersect(comprVars(r)).distinct
                    val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                              usedVars)
                    val c = Comprehension(Tuple(List(toExpr(p),tuple(rt.map(_._2)))),
                                          List(Generator(TuplePat(List(VarPat("k1"),
                                                              tuple(tile_values(p1).map(v => VarPat("_"+v))))),
                                                         Var("__v1")),
                                               Generator(TuplePat(List(VarPat("k2"),
                                                              tuple(tile_values(p2).map(v => VarPat("_"+v))))),
                                                         Var("__v2")),
                                               Predicate(MethodCall(Var("k1"),"==",List(Var("k2")))))++
                                          tile_qualifiers(r,vars):+g)
                    val tile = Store(tile_type(block,tp),List(tp),tile_dims,c)
                    def num_of_tiles ( size: Expr )
                      = MethodCall(MethodCall(MethodCall(size,"+",List(IntConst(N-1))),
                                   "/",List(IntConst(N))),"-",List(IntConst(1)))
                    val kv = newvar
                    val left_size::right_size::_ = dims
                    val left = translate_rdd(Tuple(List(Tuple(List(ngx,Var(kv))),
                                                        Tuple(List(tuple(jt1),
                                                                   tuple(tile_values(p1).map(Var)))))),
                                             List(Generator(p1,d1),
                                                  Generator(VarPat(kv),
                                                            Range(IntConst(0),
                                                                  num_of_tiles(right_size),
                                                                  IntConst(1)))),vars)
                    val right = translate_rdd(Tuple(List(Tuple(List(Var(kv),ngy)),
                                                         Tuple(List(tuple(jt2),
                                                                    tuple(tile_values(p2).map(Var)))))),
                                              List(Generator(p2,d2),
                                                   Generator(VarPat(kv),
                                                             Range(IntConst(0),
                                                                   num_of_tiles(left_size),
                                                                   IntConst(1)))),vars)
                    val nq = Generator(TuplePat(List(p,TuplePat(List(VarPat("__v1"),VarPat("__v2"))))),
                                       Lift("rdd",MethodCall(left,"cogroup",List(right))))
                    val rdd = translate_rdd(Tuple(List(toExpr(p),tile)),
                                            rdd_qualifiers(qs.flatMap( q => if ((g::g2::cs).contains(q)) Nil
                                                                            else if (q==g1) List(nq) else List(q) ),
                                                           vars),vars)
                    tuple(dims:+rdd)
               case _ => throw new Error("Unexpected error in groupByJoin")
             }
       case Tuple(List(kp,_))   // group-by tiled comprehension with group-by-key == comprehension key
         if hasGroupByKey(qs,kp)
         => qs.span{ case GroupByQual(p,_) => toExpr(p) != kp; case _ => true } match {
                     case (r,GroupByQual(p,k)::s)
                       => // a tiled comprehension with a group-by
                          groupBy_tiles(block,hs,qs,vars,tp,dims,tile_dims)
                     case _ => throw new Error("Unexpected error in tiled groupBy")
                   }
       case Tuple(List(kp,u)) // group-by tiled comprehension with group-by-key != comprehension key
         if hasGroupBy(qs)
         => qs.span{ case GroupByQual(p,_) => false; case _ => true } match {
                     case (r,gb@GroupByQual(p,k)::s)
                       => val nhs = Tuple(List(toExpr(p),u))
                          val sgb = translate(Store("block_map",List(typecheck(kp),typecheck(u)),Nil,
                                                    Comprehension(hs,qs)),vars)
                          val nv = newvar
                          val nk = newvar
                          translate(Store(block,List(tp),dims,
                                          Comprehension(Tuple(List(Var(nk),Var(nv))),
                                                        List(Generator(TuplePat(List(VarPat(nk),VarPat(nv))),sgb)))),
                                    vars)
                     case _ => throw new Error("Unexpected error in tiled groupBy")
                   }
       case Tuple(List(kp,_)) // group-by tiled comprehension with group-by-key != comprehension key
         if hasGroupBy(qs)
         => throw new Error("Cannot translate group-by tiled comprehension with group-by-key != comprehension key")
        case _
          => findTileJoin(qs) match {
                // join between tile collections
                case Some((Generator(p1,d1))::(Generator(p2,d2))::cs)
                  => val jt1 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                               => if (subsetOrEq(e1,patvars(p1).toSet)) e1 else e2 })
                     val jt2 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                               => if (subsetOrEq(e1,patvars(p2).toSet)) e1 else e2 })
                     val left = flatMap(Lambda(p1,Seq(List(Tuple(List(jt1,toExpr(p1)))))),
                                        get_rdd(d1))
                     val right = flatMap(Lambda(p2,Seq(List(Tuple(List(jt2,toExpr(p2)))))),
                                         get_rdd(d2))
                     val z = Generator(TuplePat(List(p1,p2)),
                                       Lift("rdd",
                                            flatMap(Lambda(TuplePat(List(VarPat("_k"),
                                                                         TuplePat(List(VarPat("x"),VarPat("y"))))),
                                                           Seq(List(Tuple(List(Var("x"),Var("y")))))),
                                                    MethodCall(left,"join",List(right)))))
                     val rdd = translate_rdd(hs,qs.flatMap {
                          case Generator(p,_) if p==p1 => List(z)
                          case Generator(p,_) if p==p2 => Nil
                          case x => List(x) // if (cs.contains(x)) Nil else List(x)  don't remove join condition
                         },vars)
                     tuple(dims:+rdd)
              case _
                => findTileCross(qs) match {
                     case Some(List(Generator(p1,d1),Generator(p2,d2)))
                       => val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("rdd",
                                                 MethodCall(d1,"cartesian",List(d2))))
                          val rdd = translate_rdd(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z)
                               case Generator(p,_) if p==p2 => Nil
                               case x => List(x)
                              },vars)
                          tuple(dims:+rdd)
                     case _
                             => qs.foldRight[(Expr,List[String])]((Seq(List(translate(hs,vars))),vars)) {
                                   case (Generator(p,Lift(block,u)),(r,s))
                                     if isBlockTensor(block)
                                     => (flatMap(Lambda(p,r),u),
                                         patvars(p)++s)
                                   case (Generator(p,u),(r,s))
                                     => (flatMap(Lambda(p,r),translate(u,s)),
                                         patvars(p)++s)
                                   case (LetBinding(p,u),(r,s))
                                     => (Let(p,translate(u,s),r),
                                         patvars(p)++s)
                                   case (Predicate(p),(r,s))
                                     => (IfE(translate(p,s),r,Seq(Nil)),s)
                                   case (_,(r,s)) => (r,s)
                                }._1
                   }
          }
    }}

/*----------------------------------------------------------------------------------------------------*/

  /** Translate comprehensions to optimized algebra */
  def translate ( e: Expr, vars: List[String] ): Expr = {
    e match {
      case Store("rdd",tps,args,Comprehension(hh,qqs))
        => val Comprehension(h,qs) = optimize(Comprehension(hh,block_arrays_to_rdds(qqs)))
           translate(if (is_rdd_comprehension(qs))
                       // special rules for RDD comprehensions
                       translate_rdd(h,qs,vars)
                     else optimize(store("rdd",tps,args,Comprehension(h,qs))),vars)
      case Store(block,tps,dims,c@Comprehension(_,_))
        if isBlockTensor(block)
        => val Comprehension(h,qs) = optimize(c)
           translate(if (is_tiled_comprehension(qs)) {
                       val tp = tps match { case List(tp) => tp; case _ => boolType }
                       translate_tiled(block,h,qs,vars,tp,dims) // special rules for block array comprehensions
                     } else optimize(store(block,tps,dims,Comprehension(h,qs))),vars)
      case Store(array,Nil,dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // boolean array comprehension with a group-by (when group-by key is equal to the comprehension key)
        if isBoolTensor(array)
           && hasGroupByKey(qqs,key)
        => tensor_groupby_eqkey(array,boolType,dims,head,qqs)
      case Store(array,Nil,dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // boolean array comprehension with a group-by (when group-by key is NOT equal to the comprehension key)
        if isBoolTensor(array)
           && hasGroupBy(qqs)
        => tensor_groupby_neqkey(array,boolType,dims,head,qqs)
      case Store(array,List(tp),dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // array comprehension with a group-by (when group-by key is equal to the comprehension key)
        if isTensor(array)
           && hasGroupByKey(qqs,key)
        => tensor_groupby_eqkey(array,tp,dims,head,qqs)
      case Store(array,List(tp),dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // array comprehension with a group-by (when group-by key is NOT equal to the comprehension key)
        if isTensor(array)
           && hasGroupBy(qqs)
        => tensor_groupby_neqkey(array,tp,dims,head,qqs)
      case reduce(op,x@Comprehension(h,qs))
        // total aggregation
        => val nv = newvar
           val nr = qs:+AssignQual(Var(nv),MethodCall(Var(nv),op,List(h)))
           val etp = typecheck(h)
           val zero = zeroValue(op,etp)
           translate(Block(List(VarDecl(nv,etp,Seq(List(zero))),
                                Comprehension(ignore,nr),Var(nv))),vars)
/*
      case Store(array,tps@List(tp),args,c@Comprehension(_,qs))
        if isTensor(array) && is_rdd_comprehension(qs)
        => val rtp = TupleType(List(tuple(args.map( i => intType )),tp))
           val rdd = translate(Store("rdd",List(rtp),Nil,c))
           rdd.tpe = typecheck(c)
           translate(store(array,tps,args,MethodCall(rdd,"collect",null)))
*/
      case Store(f,tps,args,u)
        // if no special rule applies, return storage of u: inv(u)
        => val su = optimize(store(f,tps,args,u))
           translate(su,vars)
      case Lift(f,x)
        // if no special rule applies, lift x: map(x)
        => translate(optimize(lift(f,x)),vars)
      case Comprehension(h,qs)
        => val nqs = qs.span{ case Generator(_,e) => !isSparseTensor(e); case _ => true } match {
                              case (r,Generator(p,e@Lift(f,u))::s)
                                if isSparseTensor(e)  // first sparse generator can be compiled to faster code
                                => val ne = lift(f,u,true)   // uses first_tensor_*
                                   Generator(p,ne)::r++s
                              case _ => qs
                            }
           val lqs = nqs.map {  // lift generator domains
                        case Generator(p,Lift(f,x))
                          => Generator(p,lift(f,x))
                        case q => q
                     }
           val Comprehension(nh,s) = optimize(Comprehension(h,lqs))
           translate(default_translator(nh,s,vars),vars)
      case Block(es)
        => Block(es.foldLeft[(List[Expr],List[String])]((Nil,vars)) {
                     case ((r,s),e@VarDecl(v,u,x))
                       => (r:+translate(e,s),v::s)
                     case ((r,s),e)
                       => (r:+translate(e,s),s)
                 }._1)
      case _ => apply(e,x => translate(x,vars))
    }
  }

  def translate ( e: Expr ): Expr = translate(e,Nil)

  def has_side_effects ( e: Expr ): Boolean
    = e match {
        case MethodCall(_,op,_)
          if List("+=","append","update").contains(op)
          => true
        case Assign(MapAccess(_,_),_)   // Map is not thread-safe
          => true
        case _ => accumulate[Boolean](e,has_side_effects,_||_,false)
      }

  /* parallelize first range flatMap */
  def parallelize ( e: Expr ): Expr
    = e match {
          case flatMap(f@Lambda(_,b),u@Range(n,m,s))
            if !has_side_effects(b)
            => MethodCall(flatMap(f,MethodCall(u,"par",null)),"toList",null)
          case _ => apply(e,parallelize)
      }
}
