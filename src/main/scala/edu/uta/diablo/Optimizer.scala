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

object Optimizer {
  import AST._
  import Normalizer._

  /* general span for comprehensions; if a qualifier matches, split there and continue with cont */
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

  /* matches ...,i<-_.until(_),...,j<-_.until(_),...,i==j,... */
  def findRangeGen ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(VarPat(_),MethodCall(_,"until",_)) => true; case _ => false },
                { case (ig@Generator(VarPat(i),MethodCall(_,"until",_)))::r
                    => matchQ(r,{ case Generator(VarPat(_),MethodCall(_,"until",_)) => true; case _ => false },
                                { case (jg@Generator(VarPat(j),MethodCall(_,"until",_)))::s
                                    => matchQ(s,{ case Predicate(MethodCall(Var(v),"==",List(Var(w))))
                                                    => (v==i && w==j) || (v==j && w==i)
                                                  case _ => false },
                                              { case c::_
                                                  => Some(List(ig,jg,c))
                                                case _ => None })
                                  case _ => None })
                  case _ => None })

  /* finds a sequence of predicates in qs that imply x=y */
  def findEqPred ( x: String, y: String, qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Predicate(MethodCall(Var(v1),"==",List(Var(v2))))
                    => v1==x || v1==y || v2==x || v2==y
                  case _ => false },
                { case (p@Predicate(MethodCall(Var(v1),"==",List(Var(v2)))))::s
                    => (if ((v1==x && v2==y) || (v2==x && v1==y))
                           Some(Nil)
                        else if (v1==x) findEqPred(v2,y,s)
                        else if (v1==y) findEqPred(x,v2,s)
                        else if (v2==x) findEqPred(v1,y,s)
                        else findEqPred(x,v1,s)).map(p::_)
                  case _ => None })

  /* matches ...,(i1,x1)<-e,...,(i2,x2)<-e,...,i1=i2,...
   * or      ...,((i1,j1),x1)<-e,...,((i2,j2),x2)<-e,...,i1=i2,...,j1=j2,...   */
  def findEqGen ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,x) => true; case _ => false },
                { case (g1@Generator(TuplePat(List(VarPat(i1),_)),x))::r
                    => matchQ(r,{ case Generator(_,y) if x==y => true; case _ => false },
                                { case (g2@Generator(TuplePat(List(VarPat(i2),_)),y))::s
                                    => for { p <- findEqPred(i1,i2,s)
                                           } yield g1::g2::p
                                  case _ => None })
                  case (g1@Generator(TuplePat(List(TuplePat(List(VarPat(i1),VarPat(j1))),_)),x))::r
                    => matchQ(r,{ case Generator(_,y) if x==y => true; case _ => false },
                                { case (g2@Generator(TuplePat(List(TuplePat(List(VarPat(i2),VarPat(j2))),_)),x))::s
                                    => for { p1 <- findEqPred(i1,i2,s)
                                             p2 <- findEqPred(j1,j2,s)
                                           } yield g1::g2::(p1++p2)
                                  case _ => None })
                  case _ => None })

  def findBoundRange ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(VarPat(_),MethodCall(_,"until",_)) => true; case _ => false },
                { case (g1@Generator(VarPat(v),MethodCall(_,"until",_)))::s
                    => matchQ(s,{ case Predicate(MethodCall(Var(v1),"==",List(e))) => v==v1; case _ => false },
                                { case g2::_ => Some(List(g1,g2))
                                  case _ => None })
                  case _ => None })

  def findLetBound ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Predicate(MethodCall(Var(v),"==",List(e))) => true; case _ => false },
                { case (c@Predicate(MethodCall(_,_,List(e))))::s
                    => matchQ(s,{ case LetBinding(p,u) => u == e; case _ => false },
                                { case lb::_ => Some(List(c,lb))
                                  case _ => None })
                  case _ => None })

  /* true if the group-by key is a constant; then there will be just one group */
  def constantKey ( key: Expr ): Boolean
    = key match {
         case Tuple(ts) => ts.forall(constantKey)
         case IntConst(_) => true
         case LongConst(_) => true
         case DoubleConst(_) => true
         case BoolConst(_) => true
         case CharConst(_) => true
         case StringConst(_) => true
         case _ => false
      }

  /* true if the group-by key is unique, then the groups are singletons */
  def uniqueKey ( key: Expr, qs: List[Qualifier] ): Boolean = {
     val is = qs.takeWhile(!_.isInstanceOf[GroupByQual])
                .flatMap {
                  case Generator(VarPat(i),MethodCall(_,"until",_))
                    => List(i)
                  case Generator(_,_)
                    => return false
                  case _ => Nil
              }
     def comps ( k: Expr ): List[String]
       = k match {
            case Tuple(ts) => ts.flatMap(comps)
            case Var(i) => List(i)
            case Nth(u,_) => comps(u)
            case MethodCall(u,op,List(c))
              if List("+","-","*").contains(op) && constantKey(c)
              => comps(u)
            case MethodCall(c,op,List(u))
              if List("+","-","*").contains(op) && constantKey(c)
              => comps(u)
            case _ => List("%") // will fail to match
         }
     comps(key).toSet.equals(is.toSet)
  }

  private def replace[T] ( x: T, y: T, s: List[T] )
    = s.map{ i => if (i == x) y else i }

  var QLcache: Option[List[Qualifier]] = None

  def max ( x: Expr, y: Expr ): Expr
    = (x,y) match {
        case (IntConst(n),IntConst(m))
          => IntConst(Math.max(n,m))
        case _ => MethodCall(Var("Math"),"max",List(x,y))
    }

  def min ( x: Expr, y: Expr ): Expr
    = (x,y) match {
        case (IntConst(n),IntConst(m))
          => IntConst(Math.min(n,m))
        case _ => MethodCall(Var("Math"),"min",List(x,y))
    }

  def optimize ( e: Expr ): Expr =
    e match {
      case Comprehension(h,qs)
        if { QLcache = findRangeGen(qs); QLcache.nonEmpty }
        => // eliminate a range generator
           QLcache match {
             case Some(List( ig@Generator(VarPat(i),MethodCall(n1,"until",List(n2))),
                             jg@Generator(VarPat(j),MethodCall(n3,"until",List(n4))), c ))
                => val mx = max(n1,n3)
                   val mn = min(n2,n4)
                   val nqs = if (freevars(n4,freevars(e)) == Nil)
                               replace(c,Predicate(BoolConst(true)),
                                     replace(jg,LetBinding(VarPat(j),Var(i)),
                                             replace(ig,Generator(VarPat(i),MethodCall(mx,"until",List(mn))),
                                                     qs)))
                             else replace(c,Predicate(MethodCall(Var(i),"<",List(n4))),
                                     replace(jg,LetBinding(VarPat(j),Var(i)),
                                             replace(ig,Generator(VarPat(i),MethodCall(mx,"until",List(n2))),
                                                     qs)))
                   optimize(Normalizer.normalize(Comprehension(h,nqs)))
             case _ => apply(e,optimize)
           }
      case Comprehension(h,qs)
        if { QLcache = findEqGen(qs); QLcache.nonEmpty }
        => // eliminate duplicate generators over arrays that have equal index value
           QLcache match {
             case Some( (g1@Generator(p1,_))::(g2@Generator(p2,_))::c )
               => val nqs = replace(g2,LetBinding(p2,toExpr(p1)),qs)
                  optimize(Comprehension(h,nqs))
             case _ => apply(e,optimize)
           }
      case Comprehension(h,qs)
        if { QLcache = findBoundRange(qs); QLcache.nonEmpty }
        => // eliminate bound range generators
           QLcache match {
             case Some(List(g@Generator(p,_),c@Predicate(MethodCall(Var(v1),"==",List(ev)))))
               => val nqs = replace(c,Predicate(BoolConst(true)),replace(g,LetBinding(p,ev),qs))
                  optimize(Comprehension(h,nqs))
             case _ => apply(e,optimize)
           }
      case Comprehension(h,qs)
        if { QLcache = findLetBound(qs); QLcache.nonEmpty }
        => // simplify let-binding using an equality condition
           QLcache match {
             case Some(List(Predicate(MethodCall(Var(v),"==",List(e))),
                            lb@LetBinding(p,w)))
               => val nqs = replace(lb,LetBinding(p,Var(v)),qs)
                  optimize(Comprehension(h,nqs))
             case _ => apply(e,optimize)
           }
      case Comprehension(h,qs)
        => qs.span{ case GroupByQual(p,k) if constantKey(k) => false; case _ => true } match {
              case (r,GroupByQual(VarPat(k),u)::s)
                => // a group-by on a constant key can be eliminated
                   val vs = comprVars(r).map(v => LetBinding(VarPat(v),Comprehension(Var(v),r)))
                   val bs = LetBinding(VarPat(k),u)::vs
                   Comprehension(h,bs++s)
              case _
                => qs.span{ case GroupByQual(p,k) if uniqueKey(k,qs) => false; case _ => true } match {
                      case (r,GroupByQual(VarPat(k),u)::s)
                        => // a group-by on a unique key can be eliminated after lifting each var v to {v}
                           val vs = comprVars(r).map(v => LetBinding(VarPat(v),Seq(List(Var(v)))))
                           val bs = LetBinding(VarPat(k),u)+:vs
                           Comprehension(h,r++bs++s)
                      case _
                        => // a group-by on a unique key
                           qs.span{ case Generator(TuplePat(List(k,v)),u)
                                      if ComprehensionTranslator.isTiled(u)
                                      => false
                                    case _ => true } match {
                             case (r,(x@Generator(TuplePat(List(k,v)),u))::(s:+GroupByQual(p,gk)))
                               if toExpr(k) == gk
                               => val groupByVars = patvars(p)
                                  val liftedVars = freevars(Comprehension(h,Nil),groupByVars)
                                                      .intersect(comprVars((r:+x)++s))
                                  val lp = liftedVars match {
                                              case List(v)
                                                => VarPat(v)
                                              case _
                                                => TuplePat(liftedVars.map(VarPat))
                                           }
                                  val bs = List(LetBinding(lp,Comprehension(toExpr(lp),s)),
                                                LetBinding(p,gk))
                                  normalizeAll(Comprehension(h,(r:+x)++bs))
                             case _ => apply(e,optimize)
                           }
                }
           }
      case _ => apply(e,optimize)
    }

  def optimizeAll ( e: Expr ): Expr = {
    var olde = e
    var ne = e
    do { olde = ne
         ne = normalizeAll(optimize(ne))
       } while (olde != ne)
    ne
  }
}
