/*
 * Copyright © 2020-2022 University of Texas at Arlington
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

object Normalizer {
  import AST._

  val debug = false

  /** rename the variables in the lambda abstraction to prevent name capture */
  def renameVars ( f: Lambda ): Lambda =
    f match {
      case Lambda(p,b)
        => val m = patvars(p).map((_,newvar))
           Lambda(m.foldLeft(p){ case (r,(from,to)) => subst(from,to,r) },
                  m.foldLeft(b){ case (r,(from,to)) => subst(from,Var(to),r) })
    }

  def isSimple ( e: Expr ): Boolean =
    e match {
      case Var(_) => true
      case StringConst(_) => true
      case CharConst(_) => true
      case IntConst(_) => true
      case LongConst(_) => true
      case DoubleConst(_) => true
      case BoolConst(_) => true
      case Nth(u,_)
        => isSimple(u)
      case Project(u,_)
        => isSimple(u)
      case Index(u,is)
        => isSimple(u) && is.forall(isSimple)
      case Tuple(cs)
        => cs.isEmpty || cs.forall(isSimple)
      case Record(cs)
        => cs.isEmpty || cs.values.forall(isSimple)
      case Seq(cs)
        => cs.isEmpty || cs.forall(isSimple)
      case Merge(x,y)
        => isSimple(x) && isSimple(y)
      case MethodCall(x,op,xs)  // arithmetic operations are simple
        if List("+","*","/","%").contains(op)
        => isSimple(x) && xs.forall(isSimple)
      case _ => false
    }

  def isConstant ( e: Expr ): Boolean =
    e match {
      case Var(_) => true
      case StringConst(_) => true
      case CharConst(_) => true
      case IntConst(_) => true
      case LongConst(_) => true
      case DoubleConst(_) => true
      case BoolConst(_) => true
      case _ => false
    }

  def freeEnv ( p: Pattern, env: Map[String,Expr] ): Map[String,Expr]
    = env.filter(x => !capture(x._1,p))

  def bindEnv ( p: Pattern, e: Expr ): Map[String,Expr] =
    (p,e) match {
      case (TuplePat(ps),Tuple(ts))
        => (ps zip ts).map{ case (q,x) => bindEnv(q,x) }.reduce(_++_)
      case (TuplePat(ps),u)
        => ps.zipWithIndex.map{ case (q,i) => bindEnv(q,Nth(u,i+1)) }.reduce(_++_)
      case (VarPat(v),_)
        => Map(v->e)
      case _ => Map()
    }

  def substE ( e: Expr, env: Map[String,Expr] ): Expr
    = env.foldLeft[Expr](e) { case (r,(v,u)) => subst(v,u,r) }

  def substP ( p: Pattern, env: Map[String,String] ): Pattern
    = p match {
        case VarPat(v)
          => if (env.contains(v)) VarPat(env(v)) else p
        case TuplePat(ts)
          => TuplePat(ts.map(substP(_,env)))
        case _ => p
      }

  def comprVars ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case VarDef(v,_,_) => List(v)
        case _ => Nil
      }

  def notGrouped ( qs: List[Qualifier] ): Boolean
    = qs.forall{ case GroupByQual(_,_) => false; case _ => true }

  @tailrec
  def notGrouped ( p: Pattern, head: Expr, qs: List[Qualifier] ): Boolean
    = qs match {
        case GroupByQual(gp,ge)::r
          if gp == p
          => notGrouped(p,head,r)
        case GroupByQual(gp,_)::r
          => patvars(p).map( s => occurrences(s,Comprehension(head,r)) ).sum == 0
        case _::r => notGrouped(p,head,r)
        case Nil => true
      }

  def has_side_effects ( e: Expr ): Boolean
    = e match {
        case Call(_,_) => true   // any call has potentially side-effects
        case _ => accumulate[Boolean](e,has_side_effects,_||_,false)
      }

  def renameVars ( e: Comprehension ): Comprehension
    = e match {
        case Comprehension(h,qs)
          => def fresh ( p: Pattern): Map[String,String]
               = p match { case VarPat(v) => Map(v->newvar)
                           case TuplePat(ps) => ps.map(fresh).reduce(_++_)
                           case _ => Map() }
             def substS ( e: Expr, env: Map[String,String] ): Expr
               = substE(e,env.mapValues(Var).toMap)
// for Scala 2.13:               = substE(e,env.view.mapValues(Var).toMap)
             val (env,nqs)
               = qs.foldLeft[(Map[String,String],List[Qualifier])] ((Map(),Nil)) {
                    case ((r,s),Generator(p,u))
                      => val nr = fresh(p)++r
                         (nr,s:+Generator(substP(p,nr),substS(u,r)))
                    case ((r,s),LetBinding(p,u))
                      => val nr = fresh(p)++r
                         (nr,s:+LetBinding(substP(p,nr),substS(u,r)))
                    case ((r,s),GroupByQual(p,k))
                      => val nr = fresh(p)++r
                         (nr,s:+GroupByQual(substP(p,nr),substS(k,r)))
                    case ((r,s),Predicate(u))
                      => (r,s:+Predicate(substS(u,r)))
                    case ((r,s),VarDef(v,t,u))
                      => (r,s:+VarDef(if (r.contains(v)) r(v) else v,t,substS(u,r)))
                    case ((r,s),AssignQual(d,v))
                      => (r,s:+AssignQual(substS(d,r),substS(v,r)))
                 }
             Comprehension(substS(h,env),nqs)
      }

  val inverses = Map( "+"->"-", "*"->"/", "-"->"+" )

  /* for dst=e(src), find g such that src=g(dst) */
  @tailrec
  def inverse ( e: Expr, src: String, dst: Expr ): Option[Expr]
    = e match {
        case Var(v)
          if v == src
          => Some(dst)
        case MethodCall(x,op,List(y))
          if inverses.contains(op) && freevars(x).contains(src) && !freevars(y).contains(src)
          => inverse(x,src,MethodCall(dst,inverses(op),List(y)))
        case MethodCall(y,op,List(x))
          if inverses.contains(op) && freevars(x).contains(src) && !freevars(y).contains(src)
          => if (op == "-")
               inverse(x,src,MethodCall(y,op,List(dst)))
             else inverse(x,src,MethodCall(dst,inverses(op),List(y)))
        case _ => None
      }

  /** Normalize a comprehension */
  def normalize ( head: Expr, qs: List[Qualifier], env: Map[String,Expr], opts: Map[String,Expr] ): List[Qualifier] =
    qs match {
      case Nil
        => List(LetBinding(VarPat("@result"),normalize(substE(head,env))))
      case Generator(p,c@Comprehension(_,s))::r
        if notGrouped(s)
        => val Comprehension(h,s) = renameVars(c)
           normalize(head,(s:+LetBinding(p,h))++r,env,opts)
      case Generator(p,Seq(List(u)))::r
        => normalize(head,LetBinding(p,u)::r,env,opts)
      case Generator(_,Seq(Nil))::r
        => Nil
      case Generator(p@VarPat(v),u@Var(w))::r
        if (u.tpe match { case ParametricType("option",_) => true; case _ => false })
        => if (opts.contains(w))
             normalize(head,r,freeEnv(p,env)+((v,opts(w))),opts)
           else Generator(p,substE(u,env))::normalize(head,r,freeEnv(p,env),opts+(w->Var(v)))
      case Generator(p,Let(q,x,u))::r
        => normalize(head,LetBinding(q,x)::Generator(p,u)::r,env,opts)
      case Generator(p,u)::r
        => Generator(p,normalize(substE(u,env)))::normalize(head,r,freeEnv(p,env),opts)
      case LetBinding(TuplePat(ps),Tuple(es))::r
        => normalize(head,(ps zip es).map{ case (p,e) => LetBinding(p,e) }++r,env,opts)
      case LetBinding(p@VarPat(v),u)::r
        => if (notGrouped(p,head,r) && ((isSimple(u) || occurrences(v,Comprehension(head,r)) <= 1)
                                        && !isRepeated(v,head)))
             normalize(head,r,bindEnv(p,normalize(substE(u,env)))++freeEnv(p,env),opts)
           else LetBinding(p,normalize(substE(u,env)))::normalize(head,r,env,opts)
      case LetBinding(p,u)::r
        => LetBinding(p,normalize(substE(u,env)))::normalize(head,r,env,opts)
      case Predicate(BoolConst(false))::r
        => Nil
      case Predicate(BoolConst(true))::r
        => normalize(head,r,env,opts)
      case Predicate(u)::r
        => Predicate(normalize(substE(u,env)))::normalize(head,r,env,opts)
      case GroupByQual(p,u)::r
        => // lift all env vars except the group-by pattern vars
           val nenv = freeEnv(p,env).map{ case (v,x) => (v,Seq(List(x))) }
           GroupByQual(p,normalize(substE(u,env)))::normalize(head,r,nenv,Map())
      case AssignQual(d,u)::r
        => AssignQual(substE(d,env),substE(u,env))::normalize(head,r,env,opts)
      case VarDef(v,t,u)::r
        => VarDef(v,t,substE(u,env))::normalize(head,r,env,opts)
      case q::r => q::normalize(head,r,env,opts)
    }

  def isRepeated ( v: String, h: Expr, qs: List[Qualifier], first: Boolean ): Boolean = {
      def f ( e: Expr ): Boolean = if (first) isRepeated(v,e) else occurrences(v,e) >= 1
      qs match {
         case Generator(p,u)::r
           => f(u) || (if (patvars(p).contains(v)) false else isRepeated(v,h,r,false))
         case Predicate(u)::r
           => f(u) || isRepeated(v,h,r,first)
         case GroupByQual(p,u)::r
           => f(u) || (if (patvars(p).contains(v)) false else isRepeated(v,h,r,false))
         case LetBinding(p,u)::r
           => f(u) || (if (patvars(p).contains(v)) false else isRepeated(v,h,r,false))
         case Nil => f(h)
         case _ => false
      }
  }

  def isRepeated ( v: String, e: Expr ): Boolean
    = e match {
        case flatMap(Lambda(p,b),u)
          if patvars(p).contains(v)
          => isRepeated(v,u)
        case flatMap(Lambda(p,b),u)
          => occurrences(v,b) >= 1 || isRepeated(v,b) || isRepeated(v,u)
        case Comprehension(h,gs)
          => isRepeated(v,h,gs,true)
        case _ => accumulate[Boolean](e,isRepeated(v,_),_||_,false)
      }

  /** normalize an expression */
  def normalize ( e: Expr ): Expr =
    e match {
//      case MethodCall(_,"parallelize",List(MethodCall(MethodCall(x,"collect",null),"toList",null)))
//        => normalize(x)
      case Apply(Lambda(p,b),u)
        => normalize(Let(p,u,b))
      case Let(VarPat(v),u,b)   // if v appears in a flatMap body, don't subst
        if isSimple(u) || (occurrences(v,b) <= 1 && !isRepeated(v,b))
        => normalize(subst(Var(v),u,b))
      case Let(VarPat(v),u,b)
        if freevars(u).contains(v) // dependency
        => val nv = newvar
           Let(VarPat(nv),u,subst(v,Var(nv),b))
      case Let(TuplePat(ps),Tuple(us),b)
        => normalize((ps zip us).foldLeft(b){ case (r,(p,u)) => Let(p,u,r) })
      case Comprehension(h,List())
        => Seq(List(normalize(h)))
      case Comprehension(h,Predicate(p)::qs)
        => IfE(p,Comprehension(h,qs),Seq(Nil))
      case Comprehension(h,Generator(p,c@Comprehension(_,_))::qs)
        => val Comprehension(h2,s) = renameVars(c)
           normalize(Comprehension(h,(s:+LetBinding(p,h2))++qs))
      case Comprehension(h,qs)
        => normalize(h,qs,Map(),Map()) match {
             case nqs:+LetBinding(VarPat("@result"),nh)
               => val nc = Comprehension(nh,nqs)
                  if (nc == e)
                     apply(nc,normalize)
                  else normalize(nc)
             case _ => Seq(Nil)
           }
      case flatMap(Lambda(p@VarPat(i),IfE(MethodCall(ie,"==",List(v)),b,nb)),
                   Range(n1,n2,n3))
        // eliminate a flatMap over a range that is bound to a value
        if inverse(ie,i,v).isDefined
        => val Some(nv) = inverse(ie,i,v)
           Let(p,nv,IfE(Call("inRange",List(Var(i),n1,n2,n3)),b,nb))
      case flatMap(Lambda(p@VarPat(i),IfE(MethodCall(v,"==",List(ie)),b,nb)),
                   Range(n1,n2,n3))
        // eliminate a flatMap over a range that is bound to a value
        if inverse(ie,i,v).isDefined
        => val Some(nv) = inverse(ie,i,v)
           Let(p,nv,IfE(Call("inRange",List(Var(i),n1,n2,n3)),b,nb))
      case flatMap(Lambda(p,Seq(List(u))),x)
        if toExpr(p) == u
        => normalize(x)
/*
      case flatMap(Lambda(VarPat(v),Seq(List(Var(w)))),x)
        if v == w
        => normalize(x)
*/
      case flatMap(Lambda(VarPat(v),Let(p,Var(w),b)),x)
        if v == w && occurrences(v,b) == 0
        => normalize(flatMap(Lambda(p,b),x))
      case flatMap(Lambda(TuplePat(List(k,VarPat(v))),Let(p,Var(w),b)),x)
        if v == w && occurrences(v,b) == 0
        => normalize(flatMap(Lambda(TuplePat(List(k,p)),b),x))
      case flatMap(Lambda(p1,Let(p2,d,b)),x)
        if occurrences(patvars(p1),d) == 0
        => normalize(Let(p2,d,flatMap(Lambda(p1,b),x)))
      case flatMap(f,Block(es:+u))
        => val env = es.foldLeft[List[(String,String)]](Nil) {
                         case (r,VarDecl(v,_,_)) => (v,newvar)::r
                         case (r,_) => r
                     }.toMap
           val nes = es.map{ case VarDecl(v,tp,b) => VarDecl(env(v),tp,b); case x => x }
           // need to avoid variable capture
           val Block(ns:+nu) = env.foldLeft[Expr](Block(nes:+u)){ case (r,(v,n)) => subst(v,Var(n),r) }
           normalize(Block(ns:+flatMap(f,nu)))
      case flatMap(f,flatMap(g,x))
        => val Lambda(p,b) = renameVars(g)
           normalize(flatMap(Lambda(p,flatMap(f,b)),x))
      case flatMap(Lambda(_,_),x@Seq(Nil))
        => x
      case flatMap(Lambda(p@VarPat(v),b),Seq(List(Var(w))))
        => normalize(subst(Var(v),Var(w),b))
      case flatMap(Lambda(p@VarPat(v),b),Seq(List(x)))
        => normalize(if (occurrences(v,b) <= 1)
                        subst(Var(v),x,b)
                     else Let(p,x,b))
      case flatMap(Lambda(TuplePat(ps),b),Seq(List(Tuple(es))))
        => normalize((ps zip es).foldLeft(b){ case (r,(p,e)) => Let(p,e,r) })
      case flatMap(Lambda(p,b),Seq(List(x)))
        => normalize(Let(p,x,b))
      case flatMap(f,Let(p,d,b))
        => normalize(Let(p,d,flatMap(f,b)))
      case flatMap(Lambda(p,IfE(c,u,Seq(Nil))),b)
        if occurrences(patvars(p),c) == 0 && !has_side_effects(c)
        => normalize(IfE(c,flatMap(Lambda(p,u),b),Seq(Nil)))
      case flatMap(f,IfE(c,e1,e2))
        => normalize(IfE(c,flatMap(f,e1),flatMap(f,e2)))
      case groupBy(x@Seq(List()))
        => x
      case groupBy(groupBy(x))
        => val nv = newvar
           val kv = newvar
           normalize(flatMap(Lambda(TuplePat(List(VarPat(kv),VarPat(nv))),
                                    Seq(List(Tuple(List(Var(kv),Seq(List(Var(nv)))))))),
                             groupBy(x)))
      case reduce(m,Seq(List(x)))
        => normalize(x)
      case reduce(m,Seq(Nil))
        => Seq(Nil)
      case IfE(BoolConst(true),e1,_)
        => normalize(e1)
      case IfE(BoolConst(false),_,e2)
        => normalize(e2)
      case Call(a,List(Tuple(s)))
        => val pat = """_(\d+)""".r
           a match {
             case pat(x) if x.toInt <= s.length
               => normalize(s(x.toInt-1))
             case _ => Call(a,List(Tuple(s.map(normalize))))
           }
      case MethodCall(x,"==",List(y))
        if x==y
        => BoolConst(true)
      case MethodCall(MethodCall(x,"||",List(y)),"!",Nil)
        => normalize(MethodCall(MethodCall(x,"!",null),"&&",List(MethodCall(y,"!",null))))
      case MethodCall(MethodCall(x,"&&",List(y)),"!",null)
        => normalize(MethodCall(MethodCall(x,"!",null),"||",List(MethodCall(y,"!",null))))
      case MethodCall(MethodCall(x,"!",null),"!",null)
        => normalize(x)
      case MethodCall(MethodCall(x,"!=",List(y)),"!",null)
        => normalize(MethodCall(x,"==",List(y)))
      case MethodCall(BoolConst(b),"&&",List(x))
        => if (b) normalize(x) else BoolConst(false)
      case MethodCall(x,"&&",List(BoolConst(b)))
        => if (b) normalize(x) else BoolConst(false)
      case MethodCall(BoolConst(b),"||",List(x))
        => if (b) BoolConst(true) else normalize(x)
      case MethodCall(x,"||",List(BoolConst(b)))
        => if (b) BoolConst(true) else normalize(x)
      case MethodCall(x,"+",List(IntConst(0)))
        => normalize(x)
      case MethodCall(x,"*",List(IntConst(1)))
        => normalize(x)
      case MethodCall(IntConst(0),"+",List(x))
        => normalize(x)
      case MethodCall(IntConst(0),"*",List(x))
        => IntConst(0)
      case MethodCall(IntConst(1),"*",List(x))
        => normalize(x)
      case MethodCall(x,"/",List(IntConst(1)))
        => normalize(x)
      case MethodCall(IntConst(0),"/",List(x))
        => IntConst(0)
      case Nth(Tuple(es),n)
        => normalize(es(n-1))
      case Project(Record(es),a)
        => normalize(es(a))
      case _ => apply(e,normalize)
    }

  def normalizeAll ( e: Expr ): Expr = {
    var olde = e
    var ne = olde
    do { olde = ne
         ne = normalize(ne)
       } while (olde != ne)
    ne
  }
}
