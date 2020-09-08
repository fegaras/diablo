/*
 * Copyright © 2020 University of Texas at Arlington
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


object ComprehensionTranslator {
  import AST._

  val ignore = Block(Nil)

  var datasetClassPath = ""   // must be set to DistributedCodeGenerator.datasetClassPath

  val arrayClassName = "Array"

  var datasetClass = ""

  /* general span for comprehensions; if a qualifier matches, split there and continue with cont */
  @tailrec
  def matchQ(qs: List[Qualifier], filter: Qualifier => Boolean,
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

  def comprVars ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
      }

  def yieldReductions ( e: Expr, vars: List[String] ): Expr
    = e match {
        case MethodCall(Var(v),"length",null)
          if vars.contains(v)
          => reduce("+",MethodCall(Var(v),"map",List(Lambda(VarPat("x"),IntConst(1)))))
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
        case reduce(_,MethodCall(Var(v),f,_))
          if List("map","flatMap").contains(f) && vars.contains(v)
          => List((v,e))
        case Var(v)
          if vars.contains(v)
          => List((v,e))
        case _ => accumulate[List[(String,Expr)]](e,findReducedTerms(_,vars),_++_,Nil)
      }

  @scala.annotation.tailrec
  def translate_groupbys ( h: Expr, qs: List[Qualifier] ): (Expr,List[Qualifier]) = {
    qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val usedVars = freevars(Comprehension(h,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(h,s),usedVars),
                                             usedVars)
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   val reducedVars = reducedTerms.map(_._1)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   val lp = liftedVars match {
                              case List(v)
                                => VarPat(v)
                              case _
                                => TuplePat(liftedVars.map(VarPat))
                            }
                   val kv = newvar
                   val xv = newvar
                   val env = reducedTerms.map{ case (v,t) => (t,MapAccess(Var(v),Var(kv))) } ++
                                       liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                   List(Generator(lp,MapAccess(Var(xv),Var(kv)))))))
                   val le = liftedVars match {
                              case List(v)
                                => Var(v)
                              case _
                                => Tuple(liftedVars.map(Var))
                            }
                   def lift ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,to,r) }
                   val Comprehension(nh,ns) = lift(yieldReductions(Comprehension(h,s),usedVars))
                   val init = (if (liftedVars.isEmpty) Nil else List(VarDef(xv,Call("Map",Nil)))) ++
                                    reducedVars.map(v => VarDef(v,Call("Map",Nil)))
                   val incr = (if (liftedVars.isEmpty) Nil else List(AssignQual(MapAccess(Var(xv),Var(kv)),
                                                IfE(MethodCall(Var(xv),"contains",List(Var(kv))),
                                                    MethodCall(MapAccess(Var(xv),Var(kv)),
                                                               ":+",
                                                               List(le)),
                                                    Seq(List(le)))))) ++
                                    reducedTerms.map {
                                       case (v,reduce(m,MethodCall(e,"map",List(f))))
                                         => AssignQual(MapAccess(Var(v),Var(kv)),
                                                       IfE(MethodCall(Var(v),"contains",List(Var(kv))),
                                                           MethodCall(MapAccess(Var(v),Var(kv)),
                                                                      m,
                                                                      List(Apply(f,e))),
                                                           Apply(f,e)))
                                       case (v,reduce(m,e))
                                         => AssignQual(MapAccess(Var(v),Var(kv)),
                                                       IfE(MethodCall(Var(v),"contains",List(Var(kv))),
                                                           MethodCall(MapAccess(Var(v),Var(kv)),
                                                                      m,
                                                                      List(e)),
                                                           e))
                                       case _ => Predicate(BoolConst(true))
                                    }
                   val nqs = r++List(LetBinding(VarPat(kv),k))++incr
                   val rv = if (liftedVars.isEmpty && reducedVars.nonEmpty)
                               Var(reducedVars.head)
                            else Var(xv)
                   translate_groupbys(nh,init
                                         ++ List(Predicate(Comprehension(BoolConst(true),nqs)),
                                                 Generator(VarPat(kv),MethodCall(rv,"keys",null)),
                                                 LetBinding(p,Var(kv)))
                                         ++ ns)
              case _ => (h,qs)
    }
  }

/*---------------------------- Generate RDD operations ------------------------------------------*/

  /* Is this generator domain an RDD? Generator domains have been lifted by the Lifter */
  def isRDD ( e: Expr ): Boolean
    = e match {
        case Call("lifted",StringConst("rdd")::_) => true
        case _ => false
      }

  def seq ( e: Expr, s: Set[String] ): Boolean = {
    val r = freevars(e).toSet
    r == s || r.subsetOf(s)
  }

  /* finds a sequence of predicates in qs that imply x=y */
  def findEqPred ( xs: Set[String], ys: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Predicate(MethodCall(e1,"==",List(e2)))
                    => ((seq(e1,xs) && seq(e2,ys)) || (seq(e2,xs) && seq(e1,ys)))
                  case _ => false },
                { case (p::s)
                    => findEqPred(xs,ys,s) match {
                          case None => Some(List(p))
                          case Some(r) => Some(p::r)
                       }
                  case _ => None })

  /* matches ...,p1 <- e1,...,p2 <- e2,...,e3 == e4,...   */
  def findJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case (Generator(p1,Call(_,List(_,e1,_))))::r1
                    => matchQ(r1,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                                 { case (Generator(p2,Call(_,List(_,e2,_))))::r2
                                     => for { c <- findEqPred(patvars(p1).toSet,patvars(p2).toSet,r2)
                                            } yield Generator(p1,e1)::Generator(p2,e2)::c
                                  case _ => None })
                  case _ => None })

  @scala.annotation.tailrec
  def derive_rdd_operations ( hs: Expr, qs: List[Qualifier] ): (Expr,List[Qualifier])
    = qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                             usedVars)
                   val gs = rt.map(_._2)
                              .map{ case reduce(_,Var(v))
                                      => Var(v)
                                    case reduce(_,flatMap(Lambda(p,Seq(List(u))),Var(v)))
                                      => Apply(Lambda(p,u),Var(v))
                                    case reduce(_,MethodCall(Var(v),"flatMap",List(Lambda(p,Seq(List(u))))))
                                      => Apply(Lambda(p,u),Var(v))
                                    case reduce(_,MethodCall(Var(v),"map",List(g)))
                                      => Apply(g,Var(v))
                                    case e
                                      => Seq(List(e))
                                  }
                   val ms = rt.map{ case (_,reduce(m,_)) => m
                                    case (_,_) => "++"
                                  }
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
                   val red = MethodCall(Call("rdd",List(Comprehension(Tuple(List(toExpr(p),Tuple(gs))),r))),
                                        "reduceByKey",List(m))
                   derive_rdd_operations(nh,Generator(TuplePat(List(p,TuplePat(env.map(x => VarPat(x._2))))),
                                                       red)::ns)
              case _
                => findJoin(qs) match {
                     case Some((Generator(p1,d1))::(Generator(p2,d2))::cs)
                       => val jt1 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (seq(e1,patvars(p1).toSet)) e1 else e2
                                                  case _ => d1 })
                          val jt2 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (seq(e1,patvars(p2).toSet)) e1 else e2
                                                  case _ => d1 })
                          val left = flatMap(Lambda(p1,Seq(List(Tuple(List(jt1,toExpr(p1)))))),d1)
                          val right = flatMap(Lambda(p2,Seq(List(Tuple(List(jt2,toExpr(p2)))))),d2)
                          val z = Generator(TuplePat(List(p1,p2)),
                                            Call("lifted",List(StringConst("rdd"),
                                                               flatMap(Lambda(TuplePat(List(VarPat("_k"),VarPat("x"))),
                                                                              Seq(List(Var("x")))),
                                                                       MethodCall(left,"join",List(right))),
                                                               IntConst(0))))
                          derive_rdd_operations(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z)
                               case Generator(p,_) if p==p2 => Nil
                               case x => if (cs.contains(x)) Nil else List(x)
                              })
                     case _ 
                       => (hs,qs)
                   }
    }

/*---------------------------- Matrices as Tiled RDDs ------------------------------------------*/

  /* Is this generator domain a Tiled RDD? Generator domains have been lifted by the Lifter */
  def isTiled ( e: Expr ): Boolean
    = e match {
        case Call("lifted",StringConst("tiled")::_) => true
        case _ => false
      }

  def tiled_indexes ( qs: List[Qualifier] ): List[String]
    = qs.foldLeft[List[String]](Nil) {
          case (r,Generator(TuplePat(List(p,_)),_))
            => r++patvars(p)
          case (r,_) => r
      }

  def has_groupby ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case GroupByQual(_,_) => true; case _ => false }

  def preserves_tiling ( hs: List[Expr], qs: List[Qualifier] ): Boolean
    = hs match {
        case List(Tuple(List(k,_)))
          if qs.exists{ case GroupByQual(gk,_) => toExpr(gk) == k; case _ => false }
          => true
        case List(Tuple(List(Tuple(ks),_)))
          if !has_groupby(qs)
          => val indexes = tiled_indexes(qs)
             ks.forall{ case Var(v) => indexes.contains(v); case _ => false }
        case _ => false
      }

  def lift_tile ( e: Expr ): Expr = {
    val i = newvar
    val j = newvar
    val gs = List(i -> Generator(VarPat(i),
                                 MethodCall(IntConst(0),"until",
                                            List(IntConst(tileSize)))),
                  j -> Generator(VarPat(j),
                                 MethodCall(IntConst(0),"until",
                                            List(IntConst(tileSize)))))
    val is = Tuple(gs.map(x => Var(x._1)))
    val mas = MapAccess(e,MethodCall(MethodCall(Var(i),"*",List(IntConst(tileSize))),
                                     "+",List(Var(j))))
    Call("lifted",List(StringConst("tile"),
                       Comprehension(Tuple(List(is,mas)),
                                     gs.map(_._2)),
                       e))
  }

  def tiled_variables ( qs: List[Qualifier] ): List[String]
    = qs.foldLeft[List[String]](Nil) {
          case (r,Generator(TuplePat(List(k,VarPat(v))),e))
            if isTiled(e)
            => r++patvars(k)
          case (r,_) => r
      }

  def all_tiled_variables ( qs: List[Qualifier] ): List[String]
    = qs.foldLeft[List[String]](Nil) {
          case (r,Generator(p,e))
            if isTiled(e)
            => r++patvars(p)
          case (r,LetBinding(p,e))
            if freevars(e,r).isEmpty
            => r++patvars(p)
          case (r,_) => r
      }

  def get_tile_qualifiers ( qs: List[Qualifier] ): List[Qualifier] = {
    val tvs = all_tiled_variables(qs)
    qs.foldLeft[List[Qualifier]] (Nil) {
          case (r,Generator(TuplePat(List(k,VarPat(v))),e))
            if isTiled(e)
            => r:+Generator(TuplePat(List(k,VarPat(v))),
                            lift_tile(Var("_"+v)))
          case (r,LetBinding(p,e))
            if freevars(e,tvs).isEmpty
            => r:+LetBinding(p,e)
          case (r,Predicate(e))
            if freevars(e,tvs).isEmpty
            => r:+Predicate(e)
          case (r,_) => r
      }
  }

  def rdd_index_variables ( qs: List[Qualifier] ): List[String]
    = qs.foldLeft[List[String]](Nil) {
          case (r,Generator(TuplePat(List(k,_)),e))
            if isRDD(e) || isTiled(e)
            => r++patvars(k)
          case (r,LetBinding(p,e))
            if freevars(e,r).isEmpty
            => r++patvars(p)
          case (r,_) => r
      }

  def rdd_qualifiers ( qs: List[Qualifier] ): List[Qualifier] = {
    val rvs = rdd_index_variables(qs)
    qs.foldLeft[List[Qualifier]] (Nil) {
          case (r,q@Generator(_,e))
            if isTiled(e) || isRDD(e)
            => r:+q
          case (r,q@LetBinding(p,e))
            if false && freevars(e,rvs).isEmpty
            => r:+q
          case (r,q@Predicate(e))
            if freevars(e,rvs).isEmpty
            => r:+q
          case (r,_) => r
      }
  }

  def get_rdd_qualifiers ( qs: List[Qualifier] ): List[Qualifier] = {
    val rvs = rdd_index_variables(qs)
    qs.foldLeft[List[Qualifier]] (Nil) {
          case (r,Generator(TuplePat(List(k,VarPat(v))),
                            e@Call("lifted",List(_,_,te))))
            if isTiled(e)
            => r:+Generator(TuplePat(List(k,VarPat("_"+v))),
                            Call("lifted",List(StringConst("rdd"),
                                               Nth(te,3),Nth(te,3))))
          case (r,Generator(p,e@Call("lifted",List(_,re,_))))
            if isRDD(e)
            => r:+Generator(p,e)
          case (r,Predicate(e))
            if freevars(e,rvs).isEmpty
            => r:+Predicate(e)
          case (r,_) => r
      }
  }

  def get_rdd_qualifiers_general ( qs: List[Qualifier] ): List[Qualifier] = {
    val rvs = rdd_index_variables(qs)
    qs.foldLeft[List[Qualifier]] (Nil) {
          case (r,Generator(TuplePat(List(k,VarPat(v))),
                            e@Call("lifted",List(_,_,te))))
            if isTiled(e)
            => r++List(Generator(TuplePat(List(usc(k),VarPat("_"+v))),
                                 Call("lifted",List(StringConst("rdd"),
                                                    Nth(te,3),Nth(te,3)))),
                       LetBinding(VarPat("__"+v),Tuple(List(toExpr(usc(k)),Var("_"+v)))))
          case (r,Generator(p,e@Call("lifted",List(_,re,_))))
            if isRDD(e)
            => r:+Generator(p,e)
          case (r,Predicate(e))
            if freevars(e,rvs).isEmpty
            => r:+Predicate(usc(e))
          case (r,_) => r
      }
  }

  def usc ( e: Expr ): Expr
    = e match {
        case Var(v)
          => Var("_"+v)
        case _ => apply(e,usc)
      }

  def usc ( p: Pattern ): Pattern
    = p match {
        case VarPat(v)
          => VarPat("_"+v)
        case _ => apply(p,usc)
      }

  def get_tile_qualifiers_general ( qs: List[Qualifier] ): List[Qualifier] = {
    val tvs = all_tiled_variables(qs)
    qs.foldLeft[List[Qualifier]] (Nil) {
          case (r,Generator(TuplePat(List(k,VarPat(v))),e))
            if isTiled(e)
            => r++List(Generator(TuplePat(List(usc(k),VarPat("_"+v))),
                                 Var("__"+v)),
                       Generator(TuplePat(List(k,VarPat(v))),
                                 lift_tile(Var("_"+v))))
          case (r,LetBinding(p,e))
            if freevars(e,tvs).isEmpty
            => r:+LetBinding(p,e)
          case (r,Predicate(e))
            if freevars(e,tvs).isEmpty
            => r:+Predicate(e):+Predicate(usc(e))
          case (r,_) => r
      }
  }

  def shuffle_tiles ( hs: Expr, qs: List[Qualifier], group_by: Boolean, dims: List[Expr] ): Expr
    = hs match {
        case Tuple(List(Tuple(ks),h))
          => val N = IntConst(tileSize)
             val range = MethodCall(IntConst(0),"until",List(N))
             val fs = tiled_variables(qs)
             val vs = ks.map{ _ => newvar }
             def gkeys ( op: String )
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
             val rqs = get_rdd_qualifiers_general(qs)++tiles:+
                               GroupByQual(TuplePat(vs.map(VarPat)),
                                           Tuple(vs.map(Var)))
             val tqs = if (group_by)
                         List(GroupByQual(TuplePat(ks.map{ case Var(v) => VarPat(v); case _ => VarPat("") }),
                                          Tuple(ks)))
                       else (vs zip gkeys("/")).map {
                               case (vk,gkey)
                                 => Predicate(MethodCall(Var(vk),"==",List(gkey)))
                            }
             val guards = (ks zip vs zip dims).flatMap {
                            case ((k,vk),d)
                              if !group_by
                              => val is = freevars(k,Nil).intersect(fs)
                                 is.map{ v => Predicate(MethodCall(MethodCall(MethodCall(Var("_"+v),"*",List(N)),
                                                                              "+",List(Var(v))),
                                                                   "<",List(d))) }
                            case _ => Nil
                          }
             val tile = Call("tile",List(Tuple(Nil),
                                         Comprehension(Tuple(List(Tuple(if (group_by) ks else gkeys("%")),h)),
                                                       get_tile_qualifiers_general(qs)++guards++tqs)))
             val rdd = Call("rdd",List(Comprehension(Tuple(List(Tuple(vs.map(Var)),tile)),
                                                     rqs)))
             //println("??? "+Pretty.print(rdd.toString))
             translate(rdd)
    }

  def groupBy_tiles ( hs: Expr, qs: List[Qualifier] ): Expr
    = hs match {
        case Tuple(List(kp@Tuple(ks),h))
          => qs.span{ case GroupByQual(gp,_) => toExpr(gp) != kp; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                             usedVars)
                   val gs = rt.map(_._2)
                              .map{ case reduce(_,Var(v))
                                      => Var(v)
                                    case reduce(_,flatMap(Lambda(p,Seq(List(u))),Var(v)))
                                      => Apply(Lambda(p,u),Var(v))
                                    case reduce(_,MethodCall(Var(v),"flatMap",List(Lambda(p,Seq(List(u))))))
                                      => Apply(Lambda(p,u),Var(v))
                                    case reduce(_,MethodCall(Var(v),"map",List(g)))
                                      => Apply(g,Var(v))
                                    case e
                                      => Seq(List(e))
                                  }
                   val ms = rt.map{ case (_,reduce(m,_)) => m
                                    case (_,_) => "++"
                                  }
                   def combine ( x: String, y: String, m: String ): Expr
                     = Call("tile",List(Tuple(Nil),
                              Comprehension(Tuple(List(Tuple(List(Var("i"),Var("j"))),
                                                       MethodCall(Var("a"),m,List(Var("b"))))),
                                   List(Generator(TuplePat(List(TuplePat(List(VarPat("i"),VarPat("j"))),
                                                                VarPat("a"))),
                                                  lift_tile(Var(x))),
                                        Generator(TuplePat(List(TuplePat(List(VarPat("ii"),VarPat("jj"))),
                                                                VarPat("b"))),
                                                  lift_tile(Var(y))),
                                        Predicate(MethodCall(Var("ii"),"==",List(Var("i")))),
                                        Predicate(MethodCall(Var("jj"),"==",List(Var("j"))))))))
                   val m = if (ms.length == 1)
                             Lambda(TuplePat(List(VarPat("x"),VarPat("y"))),
                                    combine("x","y",ms.head))
                           else { val xs = rt.map(_ => newvar)
                                  val ys = rt.map(_ => newvar)
                                  Lambda(TuplePat(List(TuplePat(xs.map(VarPat)),
                                                       TuplePat(ys.map(VarPat)))),
                                         Tuple((ms zip (xs zip ys))
                                                 .map{ case (m,(x,y)) => combine(x,y,m) } ))
                                }
                   val rqs = get_rdd_qualifiers(qs)
                   val tiles = rt.map {
                                 case (_,u)
                                   => Call("tile",List(Tuple(Nil),
                                             Comprehension(Tuple(List(kp,u)),
                                                get_tile_qualifiers(qs):+GroupByQual(p,k)))) }
                   val rdd =  MethodCall(Call("rdd",List(Comprehension(Tuple(List(kp,tuple(tiles))),
                                                                       rqs))),
                                         "reduceByKey",List(m))
                   val env = rt.map{ case (n,e) => (e,newvar) }
                   def lift ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,Var(to+"_"),r) }
                   val liftedTile
                     = lift(h) match {
                         case Var(v) => Var(v.dropRight(1))
                         case nh
                         => Call("tile",List(Tuple(Nil),
                         Comprehension(Tuple(List(Tuple(List(Var("i0"),Var("j0"))),nh)),
                           env.map(_._2).zipWithIndex.flatMap {
                              case (v,i)
                                 => Generator(TuplePat(List(TuplePat(List(VarPat("i"+i),VarPat("j"+i))),
                                                            VarPat(v+"_"))),
                                              lift_tile(Var(v)))::
                                    (if (i > 0)
                                       List(Predicate(MethodCall(Var("i"+i),"==",List(Var("i0")))),
                                            Predicate(MethodCall(Var("j"+i),"==",List(Var("j0")))))
                                     else Nil)
                           }))) }
                   val Comprehension(nh,ns) = lift(Comprehension(hs,s))
                   val res = Comprehension(Tuple(List(kp,liftedTile)),
                                           Generator(TuplePat(List(p,tuple(env.map(x => VarPat(x._2))))),
                                                     rdd)::ns)
                   //println("??? "+Pretty.print(res.toString))
                   translate(res)
              case _ => Comprehension(hs,qs)
          }
    }

  def findJoinGBKeys ( xs: Set[String], ys: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Predicate(MethodCall(e1,"==",List(e2)))
                    => ((seq(e1,xs) && seq(e2,ys)) || (seq(e2,xs) && seq(e1,ys)))
                  case GroupByQual(p,Tuple(List(gx,gy)))
                    if ((seq(gx,xs) && seq(gy,ys)) || (seq(gy,xs) && seq(gx,ys)))
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

  def tile2RDD ( e: Expr ): Expr
    = e match {
        case Call("lifted",List(_,_,u))
          => Call("lifted",List(StringConst("rdd"),
                                Nth(u,3),Nth(u,3)))
        case _ => e
      }

  def findGroupByJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e1) if isTiled(e1) => true; case _ => false },
                { case (g1@Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e2) if isTiled(e2) => true; case _ => false },
                                 { case (g2@Generator(p2,e2))::r2
                                     => findJoinGBKeys(patvars(p1).toSet,patvars(p2).toSet,r2) match {
                                           case Some(l) => Some(g1::g2::l)
                                           case _ => None
                                        }
                                  case _ => None })
                  case _ => None })

  var QLcache: Option[List[Qualifier]] = None

  def translate_tiled ( hs: Expr, qs: List[Qualifier], n: Expr, m: Expr ): Expr
    = hs match {
        case Tuple(List(Tuple(ks),_))   // a tiled comprehension that preserves tiling
          if !has_groupby(qs)
             && { val indexes = tiled_indexes(qs)
                  ks.forall{ case Var(v) => indexes.contains(v); case _ => false } }
          => val tile = Call("tile",List(Tuple(Nil),Comprehension(hs,get_tile_qualifiers(qs))))
             val rdd = Call("rdd",List(Comprehension(Tuple(List(Tuple(ks),tile)),
                                                     get_rdd_qualifiers(qs))))
             translate(rdd)
        case Tuple(List(Tuple(ks),_))   // a tiled comprehension that doesn't preserve tiling
          if !has_groupby(qs)
          => shuffle_tiles(hs,qs,false,List(n,m))
        case _
          if groupByJoin && { QLcache = findGroupByJoin(qs); QLcache.nonEmpty }
          => QLcache match {          // group-by join
        case Some((g1@Generator(p1@TuplePat(List(i1,v1)),d1))::(g2@Generator(p2@TuplePat(List(i2,v2)),d2))
                      ::(cs:+(g@GroupByQual(p,k@Tuple(List(gx,gy))))))
          => val jt1 = cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                       => if (seq(e1,patvars(p1).toSet)) e1 else e2
                                     case _ => d1 }
             val jt2 = cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                       => if (seq(e1,patvars(p2).toSet)) e1 else e2
                                     case _ => d1 }
             val (ngx,ngy) = if (seq(gx,patvars(i1).toSet)) (gx,gy) else (gy,gx)
             val (r,_::s) = qs.span(_ != g)
             val groupByVars = patvars(p)
             val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                   .intersect(comprVars(r)).distinct
             val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                       usedVars)
             val c = Comprehension(Tuple(List(k,tuple(rt.map(_._2)))),
                                   List(Generator(TuplePat(List(VarPat("k1"),usc(v1))),
                                                  toExpr(usc(usc(v1)))),
                                        Generator(TuplePat(List(VarPat("k2"),usc(v2))),
                                                  toExpr(usc(usc(v2)))),
                                        Predicate(MethodCall(Var("k1"),"==",List(Var("k2")))))++
                                   get_tile_qualifiers(r):+g)
             val tile = Call("tile",List(Tuple(Nil),c))
             def tiles ( e: Expr )
               = MethodCall(MethodCall(e,"+",List(IntConst(tileSize-1))),
                            "/",List(IntConst(tileSize)))
             val kv = newvar; val av = newvar; val bv = newvar
             val left = Comprehension(Tuple(List(Tuple(List(ngx,Var(kv))),
                                                 Tuple(List(Tuple(jt1),Var(av))))),
                                      List(Generator(TuplePat(List(i1,VarPat(av))),
                                                     tile2RDD(d1)),
                                           Generator(VarPat(kv),
                                                     MethodCall(IntConst(0),"until",List(tiles(n))))))
             val right = Comprehension(Tuple(List(Tuple(List(Var(kv),ngy)),
                                                  Tuple(List(Tuple(jt2),Var(bv))))),
                                       List(Generator(TuplePat(List(i2,VarPat(bv))),
                                                      tile2RDD(d2)),
                                            Generator(VarPat(kv),
                                                      MethodCall(IntConst(0),"until",List(tiles(m))))))
             val nq = Generator(TuplePat(List(p,TuplePat(List(usc(usc(v1)),usc(usc(v2)))))),
                                Call("lifted",List(StringConst("rdd"),
                                                   MethodCall(left,"cogroup",List(right)),
                                                   IntConst(0))))
              //println("@@@ "+Pretty.print(Comprehension(Tuple(List(k,tile)),
              //               rdd_qualifiers(qs.flatMap( q => if ((g::g2::cs).contains(q)) Nil
              //                                else if (q==g1) List(nq) else List(q)))).toString))
             translate(Comprehension(Tuple(List(k,tile)),
                                     rdd_qualifiers(qs.flatMap( q => if ((g::g2::cs).contains(q)) Nil
                                                                     else if (q==g1) List(nq) else List(q)))))
            case _ => Comprehension(hs,qs)
          }
        case Tuple(List(kp,_))        // a tiled comprehension with a group-by
          => qs.span{ case GroupByQual(p,_) if kp == toExpr(p) => false; case _ => true } match {
                case (r,GroupByQual(p,k)::s)
                  => //shuffle_tiles(hs,r,true,List(n,m))
                     groupBy_tiles(hs,qs)
                case _ => Comprehension(hs,qs)
            }
        case _ => Comprehension(hs,qs)
    }

  def translate ( e: Expr ): Expr = {
    def hasGroupByKey ( qqs: List[Qualifier], key: Expr )
      = qqs.exists{ case GroupByQual(p,k) => key == toExpr(p); case _ => false }
    def opt ( e: Expr ): Expr
      = Normalizer.normalizeAll(Optimizer.optimizeAll(Normalizer.normalizeAll(e)))
    e match {
      case Call("rdd",List(c@Comprehension(_,_)))
        => val Comprehension(h,qs) = opt(c)
           val (nh,nqs) = derive_rdd_operations(h,qs)
           return apply(Comprehension(nh,nqs),(x:Expr)=>translate(x))
      case Call("tiled",List(Tuple(List(n,m)),c@Comprehension(_,_))) 
        => val Comprehension(h,qs) = opt(c)
           val ne = translate_tiled(h,qs,n,m)
           return Tuple(List(n,m,apply(ne,translate)))
      case Call(array,List(Tuple(d),Comprehension(result@Tuple(List(key,u)),qqs)))
        if List("array","matrix","tile").contains(array) && hasGroupByKey(qqs,key)
        => qqs.span{ case GroupByQual(p,k) => key != toExpr(p); case _ => true } match {
              case (qs,GroupByQual(p,k)::ts)
        => val groupByVars = patvars(p)
           val usedVars = freevars(result,groupByVars).intersect(comprVars(qs)).distinct
           val rt = findReducedTerms(yieldReductions(result,usedVars),usedVars)
           val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                .map(x => (newvar,x._2))
           val reducedVars = reducedTerms.map(_._1)
           val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                              .map(_._1).distinct
           val lp = liftedVars match {
                              case List(v)
                                => VarPat(v)
                              case _
                                => TuplePat(liftedVars.map(VarPat))
                            }
           val kv = newvar; val kw = newvar
           val kve = if (array == "tile")
                       MethodCall(MethodCall(Var(kv),"*",List(IntConst(tileSize))),
                                  "+",List(Var(kw)))
                     else Var(kv)
           val xv = newvar
           val env = reducedTerms.map{ case (v,t) => (t,MapAccess(Var(v),kve)) } ++
                               liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                      List(Generator(lp,MapAccess(Var(xv),kve))))))
           val le = liftedVars match {
                              case List(v)
                                => Var(v)
                              case _
                                => Tuple(liftedVars.map(Var))
                            }
           def lift ( x: Expr ): Expr
             = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,to,r) }
           val ne = lift(yieldReductions(u,usedVars))
           val init = (if (liftedVars.isEmpty) Nil else List(VarDecl(xv,AnyType(),Call(array,d)))) ++
                                    reducedVars.map(v => VarDecl(v,AnyType(),Call(array,d)))
           val xvinit = if (liftedVars.isEmpty) Nil
                        else List(AssignQual(MapAccess(Var(xv),kve),
                                             MethodCall(MapAccess(Var(xv),kve),
                                                        ":+",
                                                        List(le))))
           val incr = xvinit ++ reducedTerms.flatMap {
                               case (v,reduce(m,MethodCall(x,"map",List(f))))
                                 => List(AssignQual(MapAccess(Var(v),kve),
                                                    MethodCall(MapAccess(Var(v),kve),
                                                               m,
                                                               List(Apply(f,x)))))
                               case (v,reduce(m,x))
                                 => List(AssignQual(MapAccess(Var(v),kve),
                                                    MethodCall(MapAccess(Var(v),kve),
                                                               m,
                                                               List(x))))
                               case _ => Nil
                           }
           val nqs = if (array == "tile")
                       qs++List(LetBinding(TuplePat(List(VarPat(kv),VarPat(kw))),k))++incr++ts
                     else qs++List(LetBinding(VarPat(kv),k))++incr++ts
           translate(ne match {
             case MapAccess(Var(v),Var(k))
               if reducedVars.contains(v) && k == kv
               => Block(init ++ List(Comprehension(ignore,nqs),Var(reducedVars.head)))
             case _ if array == "tile"
               => Block(init ++ List(Comprehension(ignore,nqs),Var(reducedVars.head)))
             case _
              => val rv = newvar
                 Block(VarDecl(rv,AnyType(),Call(array,d))::init
                              ++ List(Comprehension(ignore,
                                          nqs :+ AssignQual(MapAccess(Var(rv),kve),ne)),Var(rv)))
           })
         case _ => e
        }
      case Call("array",List(Lambda(VarPat(nv),c@Comprehension(h,qs)),u))
        => val k = newvar
           val v = newvar
           val nr = qs :+ LetBinding(TuplePat(List(VarPat(k),VarPat(v))),h) :+
                                AssignQual(MapAccess(Var(nv),Var(k)),Var(v))
           translate(Block(List(VarDecl(nv,AnyType(),MethodCall(u,"clone",null)),
                                Comprehension(ignore,nr),Var(nv))))
      case Call("array",List(Lambda(VarPat(nv),c@Comprehension(h,qs)),u))
        => val k = newvar
           val v = newvar
           val nr = qs++List(LetBinding(TuplePat(List(VarPat(k),VarPat(v))),h),
                             AssignQual(MapAccess(Var(nv),Var(k)),Var(v)))
           translate(Block(List(VarDecl(nv,AnyType(),MethodCall(u,"clone",null)),
                                Comprehension(ignore,nr),Var(nv))))
      case reduce(op,Comprehension(h,qs))
        => val nv = newvar
           val nr = qs:+AssignQual(Var(nv),MethodCall(Var(nv),op,List(h)))
           val zero = op match { case "+" => IntConst(0); case "*" => IntConst(1)
                                 case "&&" => BoolConst(true); case "||" => BoolConst(false) }
           translate(Block(List(VarDecl(nv,AnyType(),zero),
                                Comprehension(ignore,nr),Var(nv))))
      case Call("tile",List(Tuple(Nil),Comprehension(h,qs)))
        => val nv = newvar
           val (kx,ky,v) = (newvar,newvar,newvar)
           val nr = qs ++ List(LetBinding(TuplePat(List(TuplePat(List(VarPat(kx),VarPat(ky))),VarPat(v))),h),
                               AssignQual(MapAccess(Var(nv),
                                                    MethodCall(MethodCall(Var(kx),"*",List(IntConst(tileSize))),
                                                               "+",List(Var(ky)))),
                                          Var(v)))
           translate(Block(List(VarDecl(nv,AnyType(),Call("tile",Nil)),
                                Comprehension(ignore,nr),Var(nv))))
      case Call(array,List(Tuple(d),Comprehension(h,qs)))
        if List("array","matrix").contains(array)
        => val nv = newvar
           val kv = newvar
           val v = newvar
           val nr = qs ++ List(LetBinding(TuplePat(List(VarPat(kv),VarPat(v))),h),
                               AssignQual(MapAccess(Var(nv),Var(kv)),Var(v)))
           translate(Block(List(VarDecl(nv,AnyType(),Call(array,d)),
                                Comprehension(ignore,nr),Var(nv))))
      case Comprehension(h,qs)
        => apply(Comprehension(h,qs),translate)
      case Call("lifted",List(_,x,_)) => x
      case _ => apply(e,translate)
    }
  }
}
