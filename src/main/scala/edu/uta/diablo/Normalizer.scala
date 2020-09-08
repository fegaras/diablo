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
        => isSimple(u) && is.map(isSimple).reduce(_&&_)
      case Tuple(cs)
        => cs.isEmpty || cs.map(isSimple).reduce(_&&_)
      case Record(cs)
        => cs.isEmpty || cs.map{ case (_,u) => isSimple(u) }.reduce(_&&_)
      case Seq(cs)
        => cs.isEmpty || cs.map(isSimple).reduce(_&&_)
      case Merge(x,y)
        => isSimple(x) && isSimple(y)
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
        case _ => Nil
      }

  def notGrouped ( qs: List[Qualifier] ): Boolean
    = qs.forall{ case GroupByQual(_,_) => false; case _ => true }

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

  def renameVars ( e: Comprehension ): Comprehension
    = e match {
        case Comprehension(h,qs)
          => val vs = comprVars(qs)
             val env = vs.map(_ -> newvar).toMap
             val enve = env.map{ case (v,w) => (v,Var(w)) }
             val nqs = qs.map {
                          case Generator(p,u)
                            => Generator(substP(p,env),substE(u,enve))
                          case LetBinding(p,u)
                            => LetBinding(substP(p,env),substE(u,enve))
                          case GroupByQual(p,k)
                            => GroupByQual(substP(p,env),substE(k,enve))
                          case Predicate(u)
                            => Predicate(substE(u,enve))
                          case VarDef(v,u)
                            => VarDef(v,substE(u,enve))
                          case AssignQual(d,v)
                            => AssignQual(substE(d,enve),substE(v,enve))
                       }
             Comprehension(substE(h,enve),nqs)
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
      case Generator(p,u)::r
        if occurrences(patvars(p),Comprehension(head,r)) == 0
           && notGrouped(r)
        => normalize(head,r,env,opts)
      case Generator(p@VarPat(v),u@Var(w))::r
        if (u.tpe match { case ParametricType("option",_) => true; case _ => false })
        => if (opts.contains(w))
             normalize(head,r,freeEnv(p,env)+((v,opts(w))),opts)
           else Generator(p,substE(u,env))::normalize(head,r,freeEnv(p,env),opts+(w->Var(v)))
      case Generator(p,u)::r
        => Generator(p,normalize(substE(u,env)))::normalize(head,r,freeEnv(p,env),opts)
      case LetBinding(TuplePat(ps),Tuple(es))::r
        => normalize(head,(ps zip es).map{ case (p,e) => LetBinding(p,e) }++r,env,opts)
      case LetBinding(p,u)::r
        => if (notGrouped(p,head,r))
             normalize(head,r,bindEnv(p,normalize(substE(u,env)))++freeEnv(p,env),opts)
           else LetBinding(p,normalize(substE(u,env)))::normalize(head,r,env,opts)
      case Predicate(BoolConst(false))::r
        => Nil
      case Predicate(BoolConst(true))::r
        => normalize(head,r,env,opts)
      case Predicate(u)::r
        => Predicate(substE(u,env))::normalize(head,r,env,opts)
      case GroupByQual(p,u)::r
        => // lift all env vars except the group-by pattern vars
           val nenv = freeEnv(p,env).map{ case (v,x) => (v,Seq(List(x))) }
           GroupByQual(p,normalize(substE(u,env)))::normalize(head,r,nenv,Map())
    }

  /** normalize an expression */
  def normalize ( e: Expr ): Expr =
    e match {
      case Apply(Lambda(p@VarPat(v),b),u)
        => val nu = normalize(u)
           val nb = normalize(b)
           normalize(if (isSimple(nu) || occurrences(v,nb) <= 1)
                        subst(Var(v),nu,nb)
                     else Let(p,nu,nb))
      case Let(VarPat(v),u,b)
        if isSimple(u) || occurrences(v,b) <= 1
        => normalize(subst(Var(v),u,b))
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
      case Call("!",List(Call("||",List(x,y))))
        => normalize(Call("&&",List(Call("!",List(x)),Call("!",List(y)))))
      case Call("!",List(Call("&&",List(x,y))))
        => normalize(Call("||",List(Call("!",List(x)),Call("!",List(y)))))
      case Call("!",List(Call("!",List(x))))
        => normalize(x)
      case Call("!",List(Call("!=",List(x,y))))
        => normalize(Call("==",List(x,y)))
      case Call("&&",List(BoolConst(b),x))
        => if (b) normalize(x) else BoolConst(false)
      case Call("&&",List(x,BoolConst(b)))
        => if (b) normalize(x) else BoolConst(false)
      case Call("||",List(BoolConst(b),x))
        => if (b) BoolConst(true) else normalize(x)
      case Call("||",List(x,BoolConst(b)))
        => if (b) BoolConst(true) else normalize(x)
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
