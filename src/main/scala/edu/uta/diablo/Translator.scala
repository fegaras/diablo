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

object Translator {
  import AST._
  import Typechecker._

  type Defs = Map[String,(List[String],Stmt)]

  def elem ( x: Expr ): Expr = Seq(List(x))

  def tuple ( s: List[Expr] ): Expr
    = s match { case List(x) => x; case _ => Tuple(s) }

  def tuple ( s: List[Pattern] ): Pattern
    = s match { case List(x) => x; case _ => TuplePat(s) }

  def block ( s: List[Expr] ): Expr
    = s match { case List(x) => x; case _ => Block(s) }

  def translate ( e: Expr, env: Environment, vars: List[String], fncs: Defs ): Expr
    = e match {
        case Var(n)
          => elem(Var(n))
        case Nth(x,n)
          => val v = newvar
             Comprehension(Nth(Var(v),n),
                           List(Generator(VarPat(v),translate(x,env,vars,fncs))))
        case Project(x,n)
          => val v = newvar
             Comprehension(Project(Var(v),n),
                           List(Generator(VarPat(v),translate(x,env,vars,fncs))))
        case Index(u,is)
          => val v = newvar
             val A = newvar
             val vs = is.map(x => newvar)
             val vS = is.map(x => newvar)
             Comprehension(Var(v),
                           (Generator(VarPat(A),translate(u,env,vars,fncs))::
                            (is zip vs).map{ case (i,iv) => Generator(VarPat(iv),translate(i,env,vars,fncs)) })++
                           (Generator(TuplePat(List(tuple(vS.map(VarPat)),VarPat(v))),Var(A))::
                            (vS zip vs).map{ case (v,w) => Predicate(MethodCall(Var(v),"==",List(Var(w)))) }))
        case Let(p,u,b)
          => val v = newvar
             val nenv = bindPattern(p,typecheck(u,env),env)
             Comprehension(Var(v),
                           List(Generator(p,translate(u,env,vars,fncs)),
                                Generator(VarPat(v),translate(b,nenv,vars,fncs))))
        case Call(f,es)
          => val vs = es.map(_ => newvar)
             Comprehension(Call(f,vs.map(Var)),
                           (vs zip es).map {
                               case (v,a)
                                 => Generator(VarPat(v),translate(a,env,vars,fncs))
                           })
        case MatchE(u,cs)
          => val v = newvar
             val w = newvar
             Comprehension(Var(w),
                           List(Generator(VarPat(v),translate(u,env,vars,fncs)),
                                Generator(VarPat(w),
                                          MatchE(Var(v),
                                                 cs.map{ case Case(p,c,b)
                                                           => Case(p,c,translate(b,env,vars,fncs)) }))))
        case MethodCall(o,":",List(x))
          => Merge(translate(o,env,vars,fncs),
                   translate(x,env,vars,fncs))
        case MethodCall(o,m,null)
          => val vo = newvar
             Comprehension(MethodCall(Var(vo),m,null),
                           List(Generator(VarPat(vo),translate(o,env,vars,fncs))))
        case MethodCall(Var(op),"/",List(u))    // reduction such as max/e
          if is_reduction(op,typecheck(u,env))
          => translate(reduce(op,u),env,vars,fncs)
        case MethodCall(o,m,es)
          => val vs = es.map(_ => newvar)
             val vo = newvar
             Comprehension(MethodCall(Var(vo),m,vs.map(Var)),
                           Generator(VarPat(vo),translate(o,env,vars,fncs)) ::
                               (vs zip es).map {
                                   case (v,a)
                                     => Generator(VarPat(v),translate(a,env,vars,fncs))
                               })
        case IfE(p,x,y)
          => val vp = newvar
             val v = newvar
             Comprehension(Var(v),
                           List(Generator(VarPat(vp),translate(p,env,vars,fncs)),
                                Generator(VarPat(v),
                                          IfE(Var(vp),
                                              translate(x,env,vars,fncs),
                                              translate(y,env,vars,fncs)))))
        case Tuple(es)
          => val vs = es.map(_ => newvar)
             Comprehension(Tuple(vs.map(Var)),
                           (vs zip es).map {
                               case (v,a)
                                 => Generator(VarPat(v),translate(a,env,vars,fncs))
                           })
        case Record(es)
          => val vs = es.map(_ => newvar)
             Comprehension(Record((vs zip es).map{ case (v,(s,_)) => (s,Var(v)) }.toMap),
                           (vs zip es).map {
                               case (v,(_,a))
                                 => Generator(VarPat(v),translate(a,env,vars,fncs))
                           }.toList)
        case Seq(es)
          => val vs = es.map(_ => newvar)
             Comprehension(Seq(vs.map(Var)),
                           (vs zip es).map {
                               case (v,a)
                                 => Generator(VarPat(v),translate(a,env,vars,fncs))
                           })
        case Range(f,l,s)
          => val fv = newvar
             val lv = newvar
             val sv = newvar
             Comprehension(Range(Var(fv),Var(lv),Var(sv)),
                           List(Generator(VarPat(fv),translate(f,env,vars,fncs)),
                                Generator(VarPat(lv),translate(l,env,vars,fncs)),
                                Generator(VarPat(sv),translate(s,env,vars,fncs))))
        case Apply(Lambda(p,b),arg)
          => val v = newvar
             val w = newvar
             val nenv = bindPattern(p,typecheck(arg,env),env)
             Comprehension(Var(w),
                           List(Generator(VarPat(v),
                                          translate(arg,env,vars,fncs)),
                                Generator(VarPat(w),
                                          Apply(Lambda(p,translate(b,nenv,vars,fncs)),
                                                Var(v)))))
        case Apply(f,arg)
          => val v = newvar
             val w = newvar
             Comprehension(Var(w),
                           List(Generator(VarPat(v),translate(arg,env,vars,fncs)),
                                Generator(VarPat(w),Apply(translate(f,env,vars,fncs),Var(v)))))
//        case Comprehension(h,qs)
//          => Seq(List(e))
        case Comprehension(h,qs)
          => val nqs = qs.flatMap {
                         case Generator(p,u)
                           => val v = newvar
                              List(Generator(VarPat(v),translate(u,env,vars,fncs)),
                                   Generator(p,Var(v)))
                         case LetBinding(p,u)
                            => val v = newvar
                               List(Generator(VarPat(v),translate(u,env,vars,fncs)),
                                    LetBinding(p,Var(v)))
                          case Predicate(u)
                            => val v = newvar
                               List(Generator(VarPat(v),translate(u,env,vars,fncs)),
                                    Predicate(Var(v)))
                           case GroupByQual(p,k)
                            => val v = newvar
                               List(Generator(VarPat(v),translate(k,env,vars,fncs)),
                                    GroupByQual(p,Var(v)))
                          case q => List(apply( q, (x:Expr) => translate(x,env,vars,fncs) ))
                       }
            val v = newvar
            elem(Comprehension(Var(v),nqs:+Generator(VarPat(v),translate(h,env,vars,fncs))))
        case reduce(op,e)
          => var w = newvar
             Comprehension(reduce(op,Var(w)),
                           List(Generator(VarPat(w),translate(e,env,vars,fncs))))
        case _ => elem(apply(e,translate(_,env,vars,fncs)))
      }

  def key ( d: Expr, env: Environment, vars: List[String], fncs: Defs ): Expr
    = d match {
        case Var(v)
          => elem(Tuple(Nil))
        case Project(u,_)
          => key(u,env,vars,fncs)
        case Nth(u,_)
          => key(u,env,vars,fncs)
        case Index(u,is)
          => val k = newvar
             val vs = is.map(x => newvar)
             Comprehension(Tuple(List(Var(k),tuple(vs.map(Var)))),
                           Generator(VarPat(k),key(u,env,vars,fncs))::
                           (is zip vs).map{ case (i,v) => Generator(VarPat(v),translate(i,env,vars,fncs)) })
        case _ => throw new Error("Illegal destination: "+d)
      }

  def destination ( d: Expr, k: Expr, vars: List[String] ): Expr
    = d match {
        case Var(n)
          => elem(Var(n))
        case Project(u,a)
          => val v = newvar
             Comprehension(Project(Var(v),a),
                           List(Generator(VarPat(v),destination(u,k,vars))))
        case Nth(u,n)
          => val v = newvar
             Comprehension(Nth(Var(v),n),
                           List(Generator(VarPat(v),destination(u,k,vars))))
        case Index(u,is)
          => val v = newvar
             val A = newvar
             val ku = newvar
             val vs = is.map(x => newvar)
             val vS = is.map(x => newvar)
             Comprehension(Var(v),
                           List(LetBinding(TuplePat(List(VarPat(ku),tuple(vs.map(VarPat)))),k),
                                Generator(VarPat(A),destination(u,Var(ku),vars)),
                                Generator(TuplePat(List(TuplePat(vS.map(VarPat)),VarPat(v))),Var(A)))++
                           (vS zip vs).map{ case (v,w) => Predicate(MethodCall(Var(v),"==",List(Var(w)))) })
        case _ => throw new Error("Illegal destination: "+d)
      }

  def simpleDest ( e: Expr ): Boolean
    = accumulate[Boolean](e,{ case Index(_,_) => false
                              case _ => true },
                          _&&_,true)

  @tailrec
  def update ( dest: Expr, value: Expr, env: Environment, vars: List[String], fncs: Defs ): List[Expr]
    = dest match {
        case Var(n)
          => val nv = newvar
             val k = newvar
             List(Assign(Var(n),
                         Comprehension(Var(nv),
                                       List(Generator(TuplePat(List(VarPat(k),VarPat(nv))),value)))))
        case Project(u,a)
          => typecheck(u,env) match {
                case RecordType(cs)
                  => val nv = newvar
                     val k = newvar
                     val w = newvar
                     update(u,
                            Comprehension(Tuple(List(Var(k),Record(cs.map {
                                              case (v,_)
                                                => v -> (if (v == a) Var(nv) else Project(Var(w),v))
                                          }))),
                                          List(Generator(TuplePat(List(VarPat(k),VarPat(nv))),value),
                                               Generator(VarPat(w),destination(u,Var(k),vars)))),
                            env,vars,fncs)
                  case _
                  => val nv = newvar
                     val k = newvar
                     val w = newvar
                     update(u,
                            Comprehension(Tuple(List(Var(k),Call("recordUpdate",
                                                                 List(Var(w),StringConst(a),Var(nv))))),
                                          List(Generator(TuplePat(List(VarPat(k),VarPat(nv))),value),
                                               Generator(VarPat(w),destination(u,Var(k),vars)))),
                            env,vars,fncs)

             }
        case Nth(u,n)
          => typecheck(u,env) match {
                case TupleType(cs)
                  => val nv = newvar
                     val k = newvar
                     val w = newvar
                     update(u,
                            Comprehension(Tuple(List(Var(k),Tuple((1 to cs.length).map {
                                              i => if (i == n) Var(nv) else Nth(Var(w),i)
                                          }.toList))),
                                          List(Generator(TuplePat(List(VarPat(k),VarPat(nv))),value),
                                               Generator(VarPat(w),destination(u,Var(k),vars)))),
                            env,vars,fncs)
                case t => throw new Error("Tuple projection "+dest+" must be over a tuple (found "+t+")")
             }
        case Index(u,is)
          if simpleDest(u)
          => val A = newvar
             val k = newvar
             val v = newvar
             val vs = is.map(x => newvar)
             val ce = Comprehension(Tuple(List(tuple(vs.map(Var)),Var(v))),
                                    List(Generator(TuplePat(List(TuplePat(List(VarPat(k),
                                                                               tuple(vs.map(VarPat)))),
                                                                 VarPat(v))),
                                                   value)))
             update(u,Comprehension(Tuple(List(Var(k),Merge(Var(A),ce))),
                                    List(Generator(VarPat(A),destination(u,Var(k),vars)))),  // Var(k) is not used
                    env,vars,fncs)
        case Index(u,is)
          => val A = newvar
             val s = newvar
             val k = newvar
             val v = newvar
             val vs = is.map(x => newvar)
             update(u,Comprehension(Tuple(List(Var(k),Merge(Var(A),Var(s)))),
                                    List(Generator(TuplePat(List(TuplePat(List(VarPat(k),
                                                                               tuple(vs.map(VarPat)))),
                                                                 VarPat(v))),
                                                   value),
                                         LetBinding(VarPat(s),Tuple(List(tuple(vs.map(Var)),Var(v)))),
                                         GroupByQual(VarPat(k),Var(k)),
                                         Generator(VarPat(A),destination(u,Var(k),vars)))),
                    env,vars,fncs)
        case _ => throw new Error("Illegal destination: "+dest)
    }

  def substE ( e: Expr, env: Map[String,String] ): Expr
    = env.foldLeft[Expr](e) { case (r,(v,nv)) => subst(v,Var(nv),r) }

  def renameStmt ( s: Stmt, env: Map[String,String] ): Stmt
    = s match {
        case BlockS(ss)
          => val nenv = env ++ ss.flatMap{
                  case VarDeclS(v,_,_) => List(v -> newvar)
                  case _ => Nil
             }
             BlockS(ss.map(renameStmt(_,nenv)))
        case VarDeclS(v,tp,u)
          => VarDeclS(env(v),tp,u.map(substE(_,env)))
        case AssignS(d,u)
          => AssignS(substE(d,env),substE(u,env))
        case ForS(v,e1,e2,e3,b)
          => ForS(v,substE(e1,env),substE(e2,env),substE(e3,env),renameStmt(b,env))
        case ForeachS(v,e,b)
          => ForeachS(v,substE(e,env),renameStmt(b,env))
        case WhileS(p,b)
          => WhileS(substE(p,env),renameStmt(b,env))
        case IfS(p,s1,s2)
          => IfS(substE(p,env),renameStmt(s1,env),renameStmt(s2,env))
        case ReturnS(e)
          => ReturnS(substE(e,env))
        case ExprS(e)
          => ExprS(substE(e,env))
        case _ => s
      }

  var unfolded_function_bodies: List[Expr] = Nil

  def unfold_calls ( e: Expr, quals: List[Qualifier],
                     env: Environment, vars: List[String], fncs: Defs ): Expr
    = e match {
        case Call(f,List(u))
          if fncs.contains(f)
          => val (List(v),b) = fncs(f)
             val FunctionType(dt,rtp) = env(f)
             val rv = newvar
             val decl = VarDeclS(v,Some(dt),Some(u))
             val c = translate(BlockS(List(VarDeclS(rv,Some(rtp),None),renameStmt(BlockS(List(decl,b)),Map()))),
                               quals,List(rv),env,vars,fncs)
             unfolded_function_bodies = unfolded_function_bodies ++ c
             Var(rv)
        case Call(f,es)
          if env.contains(f)
          => val (ps,b) = fncs(f)
             val FunctionType(TupleType(ds),rtp) = env(f)
             val rv = newvar
             val decls = ((ps zip ds) zip es).map{ case ((v,tp),u) => VarDeclS(v,Some(tp),Some(u)) }.toList
             val c = translate(BlockS(List(VarDeclS(rv,Some(rtp),None),renameStmt(BlockS(decls:+b),Map()))),
                               quals,List(rv),env,vars,fncs)
             unfolded_function_bodies = unfolded_function_bodies ++ c
             Var(rv)
        case _
          => apply(e,unfold_calls(_,quals,env,vars,fncs))
      }

  def unfoldCalls ( e: Expr, quals: List[Qualifier],
                    env: Environment, vars: List[String], fncs: Defs ): (List[Expr],Expr)
    = {  unfolded_function_bodies = Nil
         //val ne = unfold_calls(e,quals,env,vars,fncs)
         //(unfolded_function_bodies,ne)
         (unfolded_function_bodies,e)
      }

  def translate_assign ( d: Expr, s: Expr, quals: List[Qualifier], decl: Boolean,
                         env: Environment, vars: List[String], fncs: Defs ): List[Expr]
    = (d,s) match {
          case (d@Index(Var(a),is),MethodCall(x,op,List(e)))
            if d == x
            => val v = newvar
               val k = newvar
               val vs = is.map(x => newvar)
               val (calls,ne) = unfoldCalls(e,quals,env,vars,fncs)
               val qs = Generator(VarPat(v),translate(ne,env,vars,fncs))::
                        ((vs zip is).map{ case (v,i) => Generator(VarPat(v),translate(i,env,vars,fncs)) }:+
                         GroupByQual(VarPat(k),tuple(vs.map(Var))))
               calls:+Assign(Var(a),
                             ((//Call("increment",List(Var(a),StringConst(op),
                                       elem(Comprehension(Tuple(List(Var(k),reduce(op,Var(v)))),
                                                     quals++qs)))))
          case (d@Var(a),MethodCall(x,op,List(e)))
            if d == x
            => val v = newvar
               val (calls,ne) = unfoldCalls(e,quals,env,vars,fncs)
               calls:+Assign(Var(a),
                             elem(MethodCall(d,op,
                                    List(reduce(op,
                                          Comprehension(Var(v),
                                              quals++List(Generator(VarPat(v),
                                                             translate(ne,env,vars,fncs)))))))))
          case (d@Index(Var(a),is),Call(op,List(x,e)))
            if d == x
            => val v = newvar
               val k = newvar
               val vs = is.map(x => newvar)
               val (calls,ne) = unfoldCalls(e,quals,env,vars,fncs)
               val qs = Generator(VarPat(v),translate(ne,env,vars,fncs))::
                        ((vs zip is).map{ case (v,i) => Generator(VarPat(v),translate(i,env,vars,fncs)) }:+
                         GroupByQual(VarPat(k),tuple(vs.map(Var))))
               calls:+Assign(Var(a),
                             ((//Call("increment",List(Var(a),StringConst(op),
                                       elem(Comprehension(Tuple(List(Var(k),reduce(op,Var(v)))),
                                                     quals++qs)))))
          case (d@Var(a),Call(op,List(x,e)))
            if d == x
            => val v = newvar
               val (calls,ne) = unfoldCalls(e,quals,env,vars,fncs)
               calls:+Assign(Var(a),
                             elem(Call(op,
                                    List(d,reduce(op,
                                          Comprehension(Var(v),
                                              quals++List(Generator(VarPat(v),
                                                             translate(ne,env,vars,fncs)))))))))
          case (d@Index(Var(a),is),e)
            => val v = newvar
               val vs = is.map(x => newvar)
               val (calls,ne) = unfoldCalls(e,quals,env,vars,fncs)
               val qs = Generator(VarPat(v),translate(ne,env,vars,fncs))::
                        (vs zip is).map{ case (v,i) => Generator(VarPat(v),translate(i,env,vars,fncs)) }
               calls:+Assign(Var(a),
                             ((//Call("update",List(Var(a),
                                       elem(Comprehension(Tuple(List(tuple(vs.map(Var)),Var(v))),
                                                     quals++qs)))))
          case (d,MethodCall(x,op,List(e)))
            if d == x
            => val v = newvar
               val k = newvar
               val w = newvar
               val (calls,ne) = unfoldCalls(e,quals,env,vars,fncs)
               calls ++
               update(d,Comprehension(Tuple(List(Var(k),Call(op,List(Var(w),reduce(op,Var(v)))))),
                                      quals++List(Generator(VarPat(v),translate(ne,env,vars,fncs)),
                                                  Generator(VarPat(k),key(d,env,vars,fncs)),
                                                  GroupByQual(VarPat(k),Var(k)),
                                                  Generator(VarPat(w),destination(d,Var(k),vars)))),
                      env,vars,fncs)
          case (d,Call(op,List(x,e)))
            if d == x
            => val v = newvar
               val k = newvar
               val w = newvar
               val (calls,ne) = unfoldCalls(e,quals,env,vars,fncs)
               calls ++
               update(d,Comprehension(Tuple(List(Var(k),MethodCall(Var(w),op,List(reduce(op,Var(v)))))),
                                      quals++List(Generator(VarPat(v),translate(ne,env,vars,fncs)),
                                                  Generator(VarPat(k),key(d,env,vars,fncs)),
                                                  GroupByQual(VarPat(k),Var(k)),
                                                  Generator(VarPat(w),destination(d,Var(k),vars)))),
                      env,vars,fncs)
          case (Var(v),e)
            => val (calls,ne) = unfoldCalls(e,quals,env,vars,fncs)
               calls:+Assign(Var(v),translate(ne,env,vars,fncs))
          case (d,e)
            => val v = newvar
               val k = newvar
               val (calls,ne) = unfoldCalls(e,quals,env,vars,fncs)
               calls ++
               update(d,Comprehension(Tuple(List(Var(k),Var(v))),
                                      quals++List(Generator(VarPat(v),translate(ne,env,vars,fncs)),
                                                  Generator(VarPat(k),key(d,env,vars,fncs)))),
                      env,vars,fncs)
    }

  def translate ( s: Stmt, quals: List[Qualifier], retVars: List[String],
                  env: Environment, vars: List[String], fncs: Defs ): List[Expr]
    = s match {
          case AssignS(d,e)
            => translate_assign(d,e,quals,false,env,vars,fncs)
          case ForS(v,e1,e2,e3,b)
            => val nv = newvar
               translate(b,
                         quals++List(Generator(VarPat(nv),
                                               translate(Range(e1,e2,e3),env,vars,fncs)),
                                     Generator(VarPat(v),Var(nv))),
                         retVars,env + (v->intType),vars,fncs)
          case ForeachS(p,e,b)
            => typecheck(e,env) match {
                  case ArrayType(d,tp)
                    => val A = newvar
                       translate(b,
                                 quals++List(Generator(VarPat(A),
                                                       translate(e,env,vars,fncs)),
                                             Generator(TuplePat(List(StarPat(),p)),Var(A))),
                                 retVars,bindPattern(p,tp,env),vars,fncs)
                  case MapType(t1,t2)
                    => val A = newvar
                       translate(b,
                                 quals++List(Generator(VarPat(A),
                                                       translate(e,env,vars,fncs)),
                                             Generator(TuplePat(List(StarPat(),p)),Var(A))),
                                 retVars,bindPattern(p,TupleType(List(t1,t2)),env),vars,fncs)
                  case ParametricType(_,List(tp))
                    => val A = newvar
                       translate(b,
                                 quals++List(Generator(VarPat(A),
                                                       translate(e,env,vars,fncs)),
                                             Generator(p,Var(A))),
                                 retVars,bindPattern(p,tp,env),vars,fncs)
                  case _ => throw new Error("Foreach statement must be over a collection: "+s)
               }
          case WhileS(e,ts)
            => List(While(translate(e,env,vars,fncs),
                          Block(translate(ts,quals,retVars,env,vars,fncs))))
          case IfS(e,ts,BlockS(Nil))
            => val p = newvar
               translate(ts,quals++List(Generator(VarPat(p),translate(e,env,vars,fncs)),
                                        Predicate(Var(p))),
                         retVars,env,vars,fncs)
          case IfS(e,ts1,ts2)
            => val p = newvar
               val pc = translate(e,env,vars,fncs)
               translate(ts1,quals++List(Generator(VarPat(p),pc),Predicate(Var(p))),
                         retVars,env,vars,fncs) ++
               translate(ts2,quals++List(Generator(VarPat(p),pc),Predicate(MethodCall(Var(p),"!",null))),
                         retVars,env,vars,fncs)
          case ReturnS(e)
            => retVars match {
                 case rv::_
                   => translate(AssignS(Var(rv),e),quals,Nil,env,vars,fncs)
                 case _
                   => throw new Error("A return statement can only appear inside a function body: "+e)
               }
//          case ExprS(e)
//            => List(translate(Comprehension(e,quals),env,vars,fncs))
          case ExprS(e)
            => val v = newvar
               List(Comprehension(Var(v),quals:+Generator(VarPat(v),translate(e,env,vars,fncs))))
          case BlockS(ss)
            => val (m,_,_,_) = ss.foldLeft(( Nil:List[Expr], env, vars, fncs )) {
                    case ((ns,ls,vs,fs),VarDeclS(v,Some(t),None))
                      => ( ns:+VarDecl(v,t,Seq(Nil)), ls+(v->t), v::vs, fs )
                    case ((ns,ls,vs,fs),VarDeclS(v,Some(t),Some(e)))
                      => val es = translate(e,ls,vs,fs)
                         ( ns:+VarDecl(v,t,es), ls+(v->t), v::vs, fs )
                    case ((ns,ls,vs,fs),VarDeclS(v,None,Some(e)))
                      => val tp = typecheck(e,ls)
                         val es = translate(e,ls,vs,fs)
                         ( ns:+VarDecl(v,tp,es), ls+(v->tp), v::vs, fs )
                    case ((ns,ls,vs,fs),DefS(f,ps,tp,b))
                      => val ftp = FunctionType(TupleType(ps.values.toList),tp)
                         val nfs = fs + (f -> (ps.toList.map(_._1),b))
                         val v = newvar
                         val df = Def(f,ps,tp,Block(translate(BlockS(List(VarDeclS(v,Some(tp),None),b)),
                                                              quals,v::retVars,ls+(f->ftp),vs,nfs)
                                                    :+Var(v)))
                         ( ns:+df, ls+(f->ftp), vs, nfs )
                    case ((ns,ls,vs,fs),stmt)
                      => ( ns++translate(stmt,quals,retVars,ls,vs,fs), ls, vs, fs )
                    }
               List(block(m))
          case TypeMapS(v,tps,ps,tp,from,to,map,inv)
            => Nil
          case _ => throw new Error("Illegal statement: "+s)
    }

  def translate ( s: Stmt ): Expr
    = block(translate(s,Nil,Nil,Map(),Nil,Map()))
}
