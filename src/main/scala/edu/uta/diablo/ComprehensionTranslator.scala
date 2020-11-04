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
  import Typechecker.{intType,longType,doubleType,boolType}
  import Lifting.{store,lift}

  val ignore: Expr = Block(Nil)

  def zeroValue ( monoid: String, tp: Type ): Expr = {
    def error (): Expr = { throw new Error("Wrong monoid "+monoid+" for type "+tp) }
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

  def optimize ( e: Expr ): Expr
    = Optimizer.optimizeAll(Normalizer.normalizeAll(e))

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

  def comprVars ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
    }

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
             case _
               => qs.foldRight[(Expr,List[String])]((Seq(List(translate(h,vars))),vars)) {
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
    }

  def yieldReductions ( e: Expr, vars: List[String] ): Expr
    = e match {
        case MethodCall(Var(v),"length",null)
          if vars.contains(v)
          => reduce("+",flatMap(Lambda(VarPat("x"),Seq(List(IntConst(1)))),Var(v)))
        case Project(Var(v),"length")
          if vars.contains(v)
          => reduce("+",flatMap(Lambda(VarPat("x"),Seq(List(IntConst(1)))),Var(v)))
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

  @tailrec
  def translate_groupbys ( h: Expr, qs: List[Qualifier] ): (Expr,List[Qualifier]) = {
    qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val usedVars = freevars(Comprehension(h,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(h,s),usedVars),
                                             usedVars)
                   assert(rt.length > 0,"Expected aggregations in a group-by comprehension")
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   val reducedVars = reducedTerms.map(_._1)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   val kv = newvar
                   val xv = newvar
                   val env = reducedTerms.map{ case (v,t) => (t,MapAccess(Var(v),Var(kv))) } ++
                                       liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                   List(Generator(tuple(liftedVars.map(VarPat)),
                                                                  MapAccess(Var(xv),Var(kv)))))))
                   val le = tuple(liftedVars.map(Var))
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
                                       case (v,reduce(m,flatMap(Lambda(p,Seq(List(u))),e)))
                                         => AssignQual(MapAccess(Var(v),Var(kv)),
                                                       IfE(MethodCall(Var(v),"contains",List(Var(kv))),
                                                           MethodCall(MapAccess(Var(v),Var(kv)),
                                                                      m,
                                                                      List(Apply(Lambda(p,u),e))),
                                                           Apply(Lambda(p,u),e)))
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
        case Lift("rdd",_) => true
        case Lift("tiled",_) => true
        case _ => false
      }

  def is_rdd_comprehension ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case Generator(p,u) => isRDD(u); case _ => false }

  def subsetOrEq ( e: Expr, s: Set[String] ): Boolean = {
    val r = freevars(e).toSet
    r == s || r.subsetOf(s)
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
                           => Some(Generator(p,lifted_rdd(e))::ps)
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

  def lifted_rdd ( e: Expr ): Expr
    = e match {
        case Lift("rdd",x) => x
        case Lift("tiled",x) => Nth(x,3)
        case _ => e
      }

  /* matches the equi-join ...,p1 <- e1,...,p2 <- e2,...,e3 == e4,...   */
  def findJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case Generator(p1,e1)::r1
                    => matchQ(r1,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                                 { case (Generator(p2,e2))::r2
                                     => for { c <- findEqPred(patvars(p1).toSet,patvars(p2).toSet,r2)
                                            } yield Generator(p1,lifted_rdd(e1))::
                                                        Generator(p2,lifted_rdd(e2))::c
                                  case _ => None })
                  case _ => None })

  /* matches the cross product ...,p1 <- e1,...,p2 <- e2,...   */
  def findCross ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case Generator(p1,Lift(_,e1))::r1
                    => matchQ(r1,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                                 { case Generator(p2,Lift(_,e2))::r2
                                     => Some(List(Generator(p1,lifted_rdd(e1)),
                                                  Generator(p2,lifted_rdd(e2))))
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
                   val red = MethodCall(Store("rdd",Nil,Nil,
                                              Comprehension(Tuple(List(toExpr(p),tuple(gs))),r)),
                                        "reduceByKey",List(m))
                   translate_rdd(nh,Generator(TuplePat(List(p,tuple(env.map(x => VarPat(x._2))))),
                                                      red)::ns,vars)
              case _
                => findJoin(qs) match {
                     case Some((Generator(p1,d1))::(Generator(p2,d2))::cs)
                       => val jt1 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (subsetOrEq(e1,patvars(p1).toSet)) e1 else e2
                                                  case _ => d1 })
                          val jt2 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (subsetOrEq(e1,patvars(p2).toSet)) e1 else e2
                                                  case _ => d1 })
                          val left = flatMap(Lambda(p1,Seq(List(Tuple(List(jt1,toExpr(p1)))))),d1)
                          val right = flatMap(Lambda(p2,Seq(List(Tuple(List(jt2,toExpr(p2)))))),d2)
                          val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("rdd",
                                                   flatMap(Lambda(TuplePat(List(VarPat("_k"),VarPat("x"))),
                                                                  Seq(List(Var("x")))),
                                                           MethodCall(left,"join",List(right)))))
                          translate_rdd(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z)
                               case Generator(p,_) if p==p2 => Nil
                               case x => List(x) // if (cs.contains(x)) Nil else List(x) don't remove join condition
                              },vars)
              case _
                => findCross(qs) match {
                     case Some(List(Generator(p1,d1),Generator(p2,d2)))
                       => val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("rdd",MethodCall(d1,"cartesian",List(d2))))
                          translate_rdd(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z)
                               case Generator(p,_) if p==p2 => Nil
                               case x => List(x)
                              },vars)
                     case _ 
                       => qs.foldRight[(Expr,List[String])]((Seq(List(translate(hs,vars))),vars)) {
                             case (Generator(p,Lift("rdd",u)),(r,s))
                               => (flatMap(Lambda(p,r),u),
                                   patvars(p)++s)
                             case (Generator(p,Lift("tiled",u)),(r,s))
                               => (flatMap(Lambda(p,r),Nth(u,3)),
                                   patvars(p)++s)
                             case (Generator(p,u),(r,s))
                               => (flatMap(Lambda(p,r),translate(u,vars)),
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

/*---------------------------- Matrices as Tiled RDDs ------------------------------------------*/

  /* Is this generator domain a Tiled RDD? Generator domains have been lifted by the Lifter */
  def isTiled ( e: Expr ): Boolean
    = e match {
        case Lift("tiled",_) => true
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
          => val indexes = tile_indexes(qs)
             freevars(p).forall(indexes.contains(_))
        case _ => false
      }

  def tile_indexes ( p: Pattern ): List[String]
    = p match {
        case TuplePat(List(TuplePat(List(VarPat(i),VarPat(j))),_))
          => List(i,j)
        case TuplePat(ps)
          => ps.flatMap(tile_indexes)
        case _ => Nil
      }

  def tile_indexes ( qs: List[Qualifier] ): List[String]
    = qs.flatMap{ case Generator(p,u) if isTiled(u) => tile_indexes(p); case _ => Nil }

  def tile_values ( p: Pattern ): List[String]
    = p match {
        case TuplePat(List(TuplePat(List(VarPat(_),VarPat(_))),p))
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
        case TuplePat(List(TuplePat(List(VarPat(_),VarPat(_))),p))
          => usc(p)
        case TuplePat(ps)
          => tuple(ps.map(uscv))
        case _ => p
      }

  def usciv ( p: Pattern ): Pattern
    = p match {
        case TuplePat(List(i@TuplePat(List(VarPat(_),VarPat(_))),p))
          => TuplePat(List(i,usc(p)))
        case TuplePat(ps)
          => TuplePat(ps.map(usciv))
        case _ => p
      }

  def tile_generators ( p: Pattern ): List[Qualifier]
    = p match {
        case TuplePat(List(TuplePat(List(VarPat(_),VarPat(_))),VarPat(v)))
          => List(Generator(p,Lift("tile",Var("_"+v))))
        case TuplePat(ps)
          => ps.flatMap(tile_generators)
        case _ => Nil
      }

  def local_expr ( e: Expr, vars: List[String] ): Boolean
    = freevars(e,vars).isEmpty

  def tile_qualifiers ( qs: List[Qualifier], vars: List[String] ): List[Qualifier]
    = qs.foldLeft[(List[Qualifier],List[String])] ((Nil,vars)) {
          case ((r,s),Generator(p,Lift("tiled",u)))
            => (r++tile_generators(p),
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
          case ((r,s),Generator(p,e@Lift("tiled",_)))
            => (r:+Generator(usciv(p),e),
                s++tile_indexes(p))
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
          case ((r,s),Generator(p,Lift("tiled",u)))
            => ((r:+Generator(usc(p),Var(tiles_var(p))))++tile_generators(p),
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
          case ((r,s),Generator(p,e@Lift("tiled",_)))
            => (r++List(Generator(usciv(p),e),
                        LetBinding(VarPat(tiles_var(p)),toExpr(usciv(p)))),
                s++tile_indexes(p))
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
  def shuffle_tiles ( hs: Expr, qs: List[Qualifier], group_by: Boolean,
                      vars: List[String], tp: Type, n: Expr, m: Expr ): Expr
    = hs match {
        case Tuple(List(Tuple(ks),h))
          => val N = IntConst(tileSize)
             val range = Range(IntConst(0),IntConst(tileSize-1),IntConst(1))
             val fs = tile_indexes(qs)
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
             val guards = (ks zip vs zip List(n,m)).flatMap {
                            case ((k,vk),d)
                              if !group_by
                              => val is = freevars(k,Nil).intersect(fs)
                                 is.map{ v => Predicate(MethodCall(MethodCall(MethodCall(Var("_"+v),"*",List(N)),
                                                                              "+",List(Var(v))),
                                                                   "<",List(d))) }
                            case _ => Nil
                          }
             val tile = Store("tile",List(tp),Nil,
                              Comprehension(Tuple(List(Tuple(if (group_by) ks else gkeys("%")),h)),
                                            tile_qualifiers_shuffle(qs,vars)++guards++tqs))
             val rdd = translate_rdd(Tuple(List(Tuple(vs.map(Var)),tile)),rqs,vars)
             translate(Tuple(List(n,m,rdd)),vars)
    }

  /* a group-by on tiled matrices */
  def groupBy_tiles ( hs: Expr, qs: List[Qualifier], vars: List[String], tp: Type, n: Expr, m: Expr ): Expr
    = hs match {
        case Tuple(List(kp,h))
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
                                    case e
                                      => Seq(List(e))
                                  }
                   val ms = rt.map{ case (_,reduce(m,_)) => m
                                    case (_,_) => "++"
                                  }
                   def combine ( x: String, y: String, m: String ): Expr
                     = Store("tile",List(tp),Nil,
                             Comprehension(Tuple(List(Tuple(List(Var("i"),Var("j"))),
                                                      MethodCall(Var("a"),m,List(Var("b"))))),
                                           List(Generator(TuplePat(List(TuplePat(List(VarPat("i"),VarPat("j"))),
                                                                        VarPat("a"))),
                                                          Lift("tile",Var(x))),
                                                Generator(TuplePat(List(TuplePat(List(VarPat("ii"),VarPat("jj"))),
                                                                        VarPat("b"))),
                                                          Lift("tile",Var(y))),
                                                Predicate(MethodCall(Var("ii"),"==",List(Var("i")))),
                                                Predicate(MethodCall(Var("jj"),"==",List(Var("j")))))))
                   val md = if (ms.length == 1)
                             Lambda(TuplePat(List(VarPat("x"),VarPat("y"))),
                                    combine("x","y",ms.head))
                           else { val xs = rt.map(_ => newvar)
                                  val ys = rt.map(_ => newvar)
                                  Lambda(TuplePat(List(TuplePat(xs.map(VarPat)),
                                                       TuplePat(ys.map(VarPat)))),
                                         Tuple((ms zip (xs zip ys))
                                                 .map{ case (m,(x,y)) => combine(x,y,m) } ))
                                }
                   val rqs = rdd_qualifiers(qs,vars)
                   val tiles = rt.map {
                                 case (_,u)
                                   => Store("tile",List(tp),Nil,
                                            Comprehension(Tuple(List(toExpr(p),u)),
                                                          tile_qualifiers(qs,vars):+GroupByQual(p,k)))
                   }
                   val rdd =  MethodCall(translate_rdd(Tuple(List(k,tuple(tiles))),rqs,vars),
                                         "reduceByKey",List(md))
                   val env = rt.map{ case (n,e) => (e,newvar) }
                   def liftExpr ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,Var(to+"_"),r) }
                   val liftedTile
                     = liftExpr(h) match {
                         case Var(v) => Var(v.dropRight(1))
                         case nh
                         => Store("tile",List(tp),Nil,
                                  Comprehension(Tuple(List(Tuple(List(Var("i0"),Var("j0"))),nh)),
                               env.map(_._2).zipWithIndex.flatMap {
                                  case (v,i)
                                    => Generator(TuplePat(List(TuplePat(List(VarPat("i"+i),VarPat("j"+i))),
                                                               VarPat(v+"_"))),
                                                 Lift("tile",Var(v)))::
                                       (if (i > 0)
                                          List(Predicate(MethodCall(Var("i"+i),"==",List(Var("i0")))),
                                               Predicate(MethodCall(Var("j"+i),"==",List(Var("j0")))))
                                        else Nil)
                               }))
                     }
                   val Comprehension(nh,ns) = liftExpr(Comprehension(hs,s))
                   val res = translate_rdd(Tuple(List(kp,liftedTile)),
                                           Generator(TuplePat(List(p,tuple(env.map(x => VarPat(x._2))))),
                                                     rdd)::ns,vars)
                   translate(Tuple(List(n,m,res)),vars)
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

  def tile2RDD ( e: Expr ): Expr
    = e match {
        case Lift(_,u)
          => Lift("rdd",Nth(u,3))
        case _ => e
      }

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
                { case (Generator(p1,Lift(_,e1)))::r1
                    => matchQ(r1,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                                 { case (Generator(p2,Lift(_,e2)))::r2
                                     => for { c <- findEqPred(patvars(p1).toSet,patvars(p2).toSet,r2)
                                            } yield Generator(p1,e1)::Generator(p2,e2)::c
                                  case _ => None })
                  case _ => None })

  /* matches the cross product ...,p1 <- e1,...,p2 <- e2,...   */
  def findTileCross ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                { case (Generator(p1,Lift(_,e1)))::r1
                    => matchQ(r1,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                                 { case (Generator(p2,Lift(_,e2)))::r2
                                     => Some(List(Generator(p1,e1),Generator(p2,e2)))
                                  case _ => None })
                  case _ => None })

  var QLcache: Option[List[Qualifier]] = None

  @tailrec
  def translate_tiled(hs: Expr, qs: List[Qualifier], vars: List[String], tp: Type, n: Expr, m: Expr ): Expr = {
    hs match {
        case Tuple(List(p,_))   // a tiled comprehension that preserves tiling
          if !hasGroupBy(qs) && tile_indexes(qs).nonEmpty
             && { val indexes = tile_indexes(qs)
                  freevars(p).forall(indexes.contains(_)) }
          => val tile = Store("tile",List(tp),Nil,
                              Comprehension(hs,tile_qualifiers(qs,vars)))
             val rdd = translate_rdd(Tuple(List(p,tile)),rdd_qualifiers(qs,vars),vars)
             translate(Tuple(List(n,m,rdd)),vars)
        case Tuple(List(Tuple(ks),_))   // a tiled comprehension that doesn't preserve tiling
          if !hasGroupBy(qs) && tile_indexes(qs).nonEmpty
          => shuffle_tiles(hs,qs,false,vars,tp,n,m)
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
                    val tile = Store("tile",List(tp),Nil,c)
                    def tiles ( e: Expr )
                      = MethodCall(MethodCall(MethodCall(e,"+",List(IntConst(tileSize-1))),
                                   "/",List(IntConst(tileSize))),"-",List(IntConst(1)))
                    val kv = newvar
                    val left = translate_rdd(Tuple(List(Tuple(List(ngx,Var(kv))),
                                                        Tuple(List(tuple(jt1),tuple(tile_values(p1).map(Var)))))),
                                             List(Generator(p1,d1),
                                                  Generator(VarPat(kv),
                                                            Range(IntConst(0),tiles(n),IntConst(1)))),vars)
                    val right = translate_rdd(Tuple(List(Tuple(List(Var(kv),ngy)),
                                                         Tuple(List(tuple(jt2),tuple(tile_values(p2).map(Var)))))),
                                              List(Generator(p2,d2),
                                                   Generator(VarPat(kv),
                                                             Range(IntConst(0),tiles(m),IntConst(1)))),vars)
                    val nq = Generator(TuplePat(List(p,TuplePat(List(VarPat("__v1"),VarPat("__v2"))))),
                                       Lift("rdd",MethodCall(left,"cogroup",List(right))))
                    val rdd = translate_rdd(Tuple(List(toExpr(p),tile)),
                                  rdd_qualifiers(qs.flatMap( q => if ((g::g2::cs).contains(q)) Nil
                                                                  else if (q==g1) List(nq) else List(q)),vars),vars)
                    Tuple(List(n,m,rdd))
               case _ => throw new Error("Unexpected error in groupByJoin")
             }
        case _
          => findTileJoin(qs) match {
                // join between tile collections
                case Some((Generator(p1,d1))::(Generator(p2,d2))::cs)
                  => val jt1 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                               => if (subsetOrEq(e1,patvars(p1).toSet)) e1 else e2
                                             case _ => d1 })
                     val jt2 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                               => if (subsetOrEq(e1,patvars(p2).toSet)) e1 else e2
                                             case _ => d1 })
                     val left = flatMap(Lambda(p1,Seq(List(Tuple(List(jt1,toExpr(p1)))))),
                                        Nth(d1,3))
                     val right = flatMap(Lambda(p2,Seq(List(Tuple(List(jt2,toExpr(p2)))))),
                                         Nth(d2,3))
                     val z = Generator(TuplePat(List(p1,p2)),
                                       Lift("tiled",
                                            Tuple(List(n,m,flatMap(Lambda(TuplePat(List(VarPat("_k"),VarPat("x"))),
                                                                          Seq(List(Var("x")))),
                                                                   MethodCall(left,"join",List(right)))))))
                     translate_tiled(hs,qs.flatMap {
                          case Generator(p,_) if p==p1 => List(z)
                          case Generator(p,_) if p==p2 => Nil
                          case x => List(x) // if (cs.contains(x)) Nil else List(x)  don't remove join condition
                         },vars,tp,n,m)
              case _
                => findTileCross(qs) match {
                     case Some(List(Generator(p1,d1),Generator(p2,d2)))
                       => val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("tiled",Tuple(List(n,m,MethodCall(d1,"cartesian",List(d2))))))
                          translate_tiled(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z)
                               case Generator(p,_) if p==p2 => Nil
                               case x => List(x)
                              },vars,tp,n,m)
                     case _ 
                       => hs match {
                           case Tuple(List(kp,_))
                             if hasGroupByKey(qs,kp)
                             => qs.span{ case GroupByQual(p,_) if kp == toExpr(p) => false; case _ => true } match {
                                   case (r,GroupByQual(p,k)::s)
                                     => // a tiled comprehension with a group-by
                                        groupBy_tiles(hs,qs,vars,tp,n,m)
                                   case _ => throw new Error("Unexpected error in tiled groupBy")
                                }
                           case _
                             => qs.foldRight[(Expr,List[String])]((Seq(List(translate(hs,vars))),vars)) {
                             case (Generator(p,Lift("tiled",u)),(r,s))
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
    }}}

  /* Translate comprehensions to optimized algebra */
  def translate ( e: Expr, vars: List[String] ): Expr = {
    e match {
      case Store("rdd",tps,args,c@Comprehension(_,_))
        => val Comprehension(h,qs) = optimize(c)
           translate(if (is_rdd_comprehension(qs))
                       translate_rdd(h,qs,vars)  // special rules for RDD comprehensions
                     else optimize(store("rdd",tps,args,Comprehension(h,qs))),vars)
      case Store("tiled",tps@List(tp),args@List(n,m),c@Comprehension(_,_))
        => val Comprehension(h,qs) = optimize(c)
           translate(if (is_tiled_comprehension(qs))
                       translate_tiled(h,qs,vars,tp,n,m) // special rules for tiled comprehensions
                     else optimize(store("tiled",tps,args,Comprehension(h,qs))),vars)
      case Store(array,List(tp),d,Comprehension(result@Tuple(List(key,u)),qqs))
        // array comprehension with a group-by (when group-by key is equal to the comprehension key)
        if List("vector","matrix","tile").contains(array)
           && hasGroupByKey(qqs,key)
        => qqs.span{ case GroupByQual(p,k) => key != toExpr(p); case _ => true } match {
              case (qs,GroupByQual(p,k)::ts)
                => val groupByVars = patvars(p)
                   val usedVars = freevars(result,groupByVars).intersect(comprVars(qs)).distinct
                   val rt = findReducedTerms(yieldReductions(result,usedVars),usedVars)
                   assert(rt.length > 0,"Expected aggregations in a group-by comprehension")
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   val reducedVars = reducedTerms.map(_._1)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   val kv = newvar; val kw = newvar
                   val kve = if (array == "tile")
                               MethodCall(MethodCall(Var(kv),"*",List(IntConst(tileSize))),
                                          "+",List(Var(kw)))
                             else if (array == "matrix")
                               MethodCall(MethodCall(Var(kv),"*",List(d.head)),
                                          "+",List(Var(kw)))
                             else Var(kv)
                   val xv = newvar
                   val env = reducedTerms.map{ case (v,t) => (t,Index(Var(v),List(kve))) } ++
                                       liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                              List(Generator(tuple(liftedVars.map(VarPat)),
                                                                             Index(Var(xv),List(kve)))))))
                   def liftExpr ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,to,r) }
                   val ne = liftExpr(yieldReductions(u,usedVars))
                   val atp = ArrayType(1,tp)
                   val array_constructor = array match {
                           case "vector" => Call("array",d)
                           case "matrix" => Call("array",List(MethodCall(d.head,"*",List(d.tail.head))))
                           case _ => Call(array,d)
                        }
                   val init = (if (liftedVars.isEmpty) Nil
                               else List(VarDecl(xv,atp,Seq(List(array_constructor))))) ++
                                            reducedVars.map(v => VarDecl(v,atp,Seq(List(array_constructor))))
                   val xvinit = if (liftedVars.isEmpty) Nil
                                else List(AssignQual(Index(Var(xv),List(kve)),
                                                     MethodCall(Index(Var(xv),List(kve)),
                                                                ":+",
                                                                List(tuple(liftedVars.map(Var))))))
                   val incr = xvinit ++ reducedTerms.flatMap {
                                       case (v,reduce(m,flatMap(Lambda(p,Seq(List(u))),x)))
                                         => List(AssignQual(Index(Var(v),List(kve)),
                                                            MethodCall(Index(Var(v),List(kve)),
                                                                       m,
                                                                       List(Apply(Lambda(p,u),x)))))
                                       case (v,reduce(m,x))
                                         => List(AssignQual(Index(Var(v),List(kve)),
                                                            MethodCall(Index(Var(v),List(kve)),
                                                                       m,
                                                                       List(x))))
                                       case _ => Nil
                                   }
                   val conds = if (array == "matrix")
                                 List(Predicate(MethodCall(Var(kv),"<",List(d.head))),
                                      Predicate(MethodCall(Var(kw),"<",List(d.tail.head))))
                               else if (array == "tile")
                                 List(Predicate(MethodCall(Var(kv),"<",List(IntConst(tileSize)))),
                                      Predicate(MethodCall(Var(kw),"<",List(IntConst(tileSize)))))
                               else List(Predicate(MethodCall(Var(kv),"<",List(d.head))))
                   val nqs = if (array == "tile" || array == "matrix")
                               qs++List(LetBinding(TuplePat(List(VarPat(kv),VarPat(kw))),k))++conds++incr++ts
                             else qs++List(LetBinding(VarPat(kv),k))++conds++incr++ts
                   val res = ne match {
                             case Index(Var(v),List(Var(k)))
                               if reducedVars.contains(v) && k == kv
                               => Block(init ++ List(Comprehension(ignore,nqs),Var(reducedVars.head)))
                             case _ if array == "tile" || array == "matrix"
                               => Block(init ++ List(Comprehension(ignore,nqs),Var(reducedVars.head)))
                             case _
                              => val rv = newvar
                                 Block(VarDecl(rv,atp,Seq(List(array_constructor)))::init
                                              ++ List(Comprehension(ignore,
                                                            nqs :+ AssignQual(Index(Var(rv),List(kve)),ne)),
                                                      Var(rv)))
                           }
                   if (array == "matrix")
                      translate(tuple(d:+res),vars)
                   else translate(res,vars)
              case _ => e
           }
      case Store(array,List(tp),d,Seq(List(Comprehension(h,qs))))
        // array comprehension with a group-by on a key different from the header key
        if List("vector","matrix","tile").contains(array)
           && hasGroupBy(qs)
        => val (nh,nqs) = translate_groupbys(h,qs)
           translate(Comprehension(nh,nqs),vars)
      case reduce(op,x@Comprehension(h,qs))
        // total aggregation
        => val nv = newvar
           val nr = qs:+AssignQual(Var(nv),MethodCall(Var(nv),op,List(h)))
           val zero = zeroValue(op,x.tpe)
           translate(Block(List(VarDecl(nv,x.tpe,zero),
                                Comprehension(ignore,nr),Var(nv))),vars)
      case Store(f,tps,args,u)
        // if no special rule applies, return storage of u: inv(u)
        => val su = optimize(store(f,tps,args,u))
           translate(su,vars)
      case Lift(f,x)
        // if no special rule applies, lift x: map(x)
        => x.tpe = null; translate(optimize(lift(f,x)),vars)
      case Comprehension(h,qs)
        => val nqs = qs.map {  // lift generator domains
                        case Generator(p,Lift(f,x))
                          => Generator(p,lift(f,x))
                        case q => q
                     }
           val Comprehension(nh,s) = optimize(Comprehension(h,nqs))
           default_translator(nh,s,vars)
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

  /* parallelize first range flatMap */
  def parallelize ( e: Expr ): Expr
    = e match {
          case flatMap(f,u@Range(n,m,s))
            => MethodCall(flatMap(f,MethodCall(u,"par",null)),"toList",null)
          case _ => apply(e,parallelize)
      }
}
