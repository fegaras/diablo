/*
 * Copyright © 2019 University of Texas at Arlington
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

object Typechecker {
    import AST._

    // binds variable names to types (contains duplicate names)
    type Environment = List[(String,Type)]

    val intType = BasicType("Int")
    val longType = BasicType("Long")
    val boolType = BasicType("Boolean")
    val doubleType = BasicType("Double")
    val stringType = BasicType("String")

    // hooks to the Scala compiler; set at v_impl in Diablo.scala
    var typecheck_call: ( String, List[Type] ) => Option[Type] = _
    var typecheck_method: ( Type, String, List[Type] ) => Option[Type] = _
    var typecheck_var: ( String ) => Option[Type] = _

    val collection_names = List("array","map","List",
                                ComprehensionTranslator.arrayClassName,
                                ComprehensionTranslator.datasetClassPath)

    def find[T] ( name: String, env: List[(String,T)] ): T
      = env.find{ case (n,_) => n == name }.head._2

    def contains[T] ( name: String, env: List[(String,T)] ): Boolean
      = env.exists{ case (n,_) => n == name }

    def tuple ( s: List[Type] ): Type
      = s match { case List(x) => x; case _ => TupleType(s) }

    def isCollection ( f: String ): Boolean
      = collection_names.contains(f)

    def typeMatch ( t1: Type, t2: Type ): Boolean
      = ((t1 == AnyType() || t2 == AnyType())
         || t1 == t2)

    def bindPattern ( pat: Pattern, tp: Type, env: Environment ): Environment
      = (pat,tp) match {
          case (TuplePat(cs),TupleType(ts))
            => if (cs.length != ts.length)
                 throw new Error("Pattern "+pat+" does not match the type "+tp)
               else cs.zip(ts).foldRight(env){ case ((p,t),r) => bindPattern(p,t,r) }
          case (VarPat(v),t)
            => (v,t)::env
          case (StarPat(),_)
            => env
          case _ => throw new Error("Pattern "+pat+" does not match the type "+tp)
      }

  def elemType ( tp: Type ): Type
    = tp match {
          case ArrayType(_,t)
            => t
          case MapType(_,t)
            => t
          case SeqType(t)
            => t
          case ParametricType(c,List(t))
            if isCollection(c)
            => t
          case t => throw new Error("Type "+tp+" is not a collection (found "+t+")")
      }

    def typecheck ( e: Expr, env: Environment ): Type
      = try { val tpe = e match {
          case Var("null")
            => AnyType()
          case Var(v)
            => if (contains(v,env))
                  find(v,env)
               else typecheck_var(v). // call the Scala typechecker to find var v
                          getOrElse(throw new Error("Undefined variable: "+v))
          case Nth(u,n)
            => typecheck(u,env) match {
                  case TupleType(cs)
                    => if (n<=0 || n>cs.length)
                          throw new Error("Tuple does not contain a "+n+" element")
                       cs(n-1)
                  case t => throw new Error("Tuple projection "+e+" must be over a tuple (found "+t+")")
               }
          case Project(u,a)
            => typecheck(u,env) match {
                  case RecordType(cs)
                    => if (cs.contains(a))
                         cs(a)
                       else throw new Error("Unknown record attribute: "+a)
                  case ArrayType(d,_)
                    if a == "dims"
                    => TupleType((1 to d).map(i => longType).toList)
                  case ArrayType(1,_)
                    if a == "length"
                    => longType
                  case ArrayType(2,_)
                    if a == "rows" || a == "cols"
                    => longType
                  case _ => typecheck(MethodCall(u,a,null),env)
               }
          case Index(u,is)
            => val itps = is.map(i => typecheck(i,env))
               for { itp <- itps }
                  if ( itp != longType && itp != intType )
                    throw new Error("Matrix indexing "+e+" must use an integer row index: "+itp)
               typecheck(u,env) match {
                  case ArrayType(d,t)
                    if is.length == d
                    => t
                  case ArrayType(d,t)
                    => throw new Error("Array indexing "+e+" needs "+d+" indices (found "+is.length+" )")
                  case t => throw new Error("Array indexing "+e+" must be over an array (found "+t+")")
               }
          case Let(p,u,b)
            => typecheck(b,bindPattern(p,typecheck(u,env),env))
          case MatchE(u,cs)
            => val tp = typecheck(u,env)
               cs.foldLeft(AnyType():Type) {
                    case (r,Case(p,c,b))
                      => val nenv = bindPattern(p,tp,env)
                         if (typecheck(c,nenv) != boolType)
                           throw new Error("Predicate "+c+" in "+e+" must be boolean")
                         val btp = typecheck(b,env)
                         if (!typeMatch(r,btp))
                           throw new Error("Incompatible results in "+e)
                         btp
                    }
          case Seq(args)
            => val tp = args.foldRight(AnyType():Type){ case (a,r)
                                        => val t = typecheck(a,env)
                                           if (r != AnyType() && t != r)
                                              throw new Error("Incompatible types in collection "+e)
                                           else t }
               SeqType(tp)
          case Comprehension(h,qs)
            => val nenv = qs.foldLeft((env,Nil:List[String])) {
                    case ((r,s),q@Generator(p,u))
                      => (typecheck(u,r) match {
                            case ArrayType(d,t)
                              => bindPattern(p,tuple(List(tuple((1 to d).map(i => longType).toList),t)),r)
                            case MapType(k,v)
                              => bindPattern(p,TupleType(List(k,v)),r)
                            case SeqType(t)
                              => bindPattern(p,t,r)
                            case ParametricType(c,List(t))
                              if isCollection(c)
                              => bindPattern(p,t,r)
                            case t => throw new Error("Expected a collection type in generator "+q+" (found "+t+")")
                         },
                         s ++ patvars(p))
                    case ((r,s),LetBinding(p,d))
                      => ( bindPattern(p,typecheck(d,r),r), s++patvars(p) )
                    case ((r,s),Predicate(p))
                      => if (typecheck(p,r) != boolType)
                           throw new Error("The comprehension predicate "+p+" must be a boolean")
                         (r,s)
                    case ((r,s),GroupByQual(p,k))
                      => val nvs = patvars(p)
                         val ktp = typecheck(k,r)
                         // lift all pattern variables to bags
                         ( bindPattern(p,ktp,s.diff(nvs).map{ v => (v,SeqType(find(v,r))) }.toList ++ r),
                           nvs ++ s )
                    case ((r,s),AssignQual(d,u))
                      => typecheck(d,r)
                         typecheck(u,r)
                         (r,s)
                    case ((r,s),VarDef(n,u))
                      => val tp = typecheck(u,r)
                         ( bindPattern(VarPat(n),tp,r), n::s )
              }._1
              SeqType(typecheck(h,nenv))
          case Call(f,args)
            if contains(f,env)
            => val tp = typecheck(Tuple(args),env)
               find(f,env) match {
                  case FunctionType(dt,rt)
                    => if (typeMatch(dt,tp)) rt
                       else throw new Error("Function "+f+" on "+dt+" cannot be applied to "+args+" of type "+tp);
                  case _ => throw new Error(f+" is not a function: "+e)
               }
          case Call(f,args)
            => // call the Scala typechecker to find function f
               typecheck_call(f,args.map(typecheck(_,env))).
                          getOrElse(throw new Error("Wrong function call: "+e))
          case MethodCall(u,m,null)
            => // call the Scala typechecker to find method m
               typecheck_method(typecheck(u,env),m,null).
                          getOrElse(throw new Error("Wrong method call: "+e))
          case MethodCall(u,m,args)
            => // call the Scala typechecker to find method m
               typecheck_method(typecheck(u,env),m,args.map(typecheck(_,env))).
                          getOrElse(throw new Error("Wrong method call: "+e))
          case IfE(p,a,b)
            => if (typecheck(p,env) != boolType)
                 throw new Error("The if-expression condition "+p+" must be a boolean")
               val tp = typecheck(a,env)
               if (!typeMatch(typecheck(b,env),tp))
                 throw new Error("Ill-typed if-expression"+e)
               tp
          case Apply(Lambda(p,b),arg)
            => typecheck(b,bindPattern(p,typecheck(arg,env),env))
          case Apply(f,arg)
            => val tp = typecheck(arg,env)
               typecheck(f,env) match {
                  case FunctionType(dt,rt)
                    => if (typeMatch(dt,tp)) rt
                       else throw new Error("Function "+f+" cannot be applied to "+arg+" of type "+tp);
                  case _ => throw new Error("Expected a function "+f)
               }
          case Tuple(cs)
            => TupleType(cs.map{ typecheck(_,env) })
          case Record(cs)
            => RecordType(cs.map{ case (v,u) => v->typecheck(u,env) })
          case Merge(x,y)
            => val xtp = typecheck(x,env)
               val ytp = typecheck(y,env)
               if (!typeMatch(xtp,ytp))
                   throw new Error("Incompatible types in Merge: "+e+" (found "+xtp+" and "+ytp+")")
               xtp
          case flatMap(Lambda(p,b),u)
            => val nenv = typecheck(u,env) match {
                            case ArrayType(d,t)
                              => bindPattern(p,tuple(List(tuple((1 to d).map(i => longType).toList),t)),env)
                            case MapType(k,v)
                              => bindPattern(p,TupleType(List(k,v)),env)
                            case SeqType(t)
                              => bindPattern(p,t,env)
                            case ParametricType(c,List(t))
                              if isCollection(c)
                              => bindPattern(p,t,env)
                            case t => throw new Error("Expected a collection type in "+e+" (found "+t+")")
                         }
               typecheck(b,nenv)
          case groupBy(u)
            => typecheck(u,env) match {
                 case ArrayType(d,t)
                   => ArrayType(d,SeqType(t))
                 case MapType(k,t)
                   => MapType(k,SeqType(t))
                 case SeqType(TupleType(List(k,v)))
                   => SeqType(TupleType(List(k,SeqType(v))))
                 case ParametricType(c,List(TupleType(List(k,v))))
                   if isCollection(c)
                   => ParametricType(c,List(TupleType(List(k,SeqType(v)))))
                 case t => throw new Error("Expected a collection of pairs in "+e+" (found "+t+")")
               }
          case reduce(m,u)
            => if (!contains(m,env))
                 throw new Error("The monoid "+m+" in reduction "+e+" is undefined")
               else find(m,env) match {
                 case FunctionType(TupleType(List(t1,t2)),t3)
                   if t1 == t2 && t1 == t3
                   => elemType(typecheck(u,env))
                 case _ => throw new Error("The monoid "+m+" in reduction "+e+" is ill-formed")
               }
          case Block(es)
            => es.foldLeft((AnyType():Type,env)) {
                  case ((_,r),VarDecl(v,tp,u))
                    => if (!typeMatch(elemType(typecheck(u,env)),tp))   // u is lifted to a collection
                         throw new Error("Incompatible values in assignment: "+e)
                       (tp,(v,tp)::r)
                  case ((_,r),Def(f,ps,tp,b))
                    => typecheck(b,ps.toList++r)
                       (tp,(f,FunctionType(TupleType(ps.values.toList),tp))::r)
                  case ((_,r),e)
                    => (typecheck(e,r),r)
               }._1
          case VarDecl(_,t,u)
            => t
          case Assign(d,u)
            => val ut = typecheck(u,env)
               if (!typeMatch(typecheck(d,env),elemType(ut)))   // u is lifted to a collection
                 throw new Error("Incompatible values in assignment: "+e)
               ut
          case StringConst(_) => stringType
          case IntConst(_) => intType
          case LongConst(_) => longType
          case DoubleConst(_) => doubleType
          case BoolConst(_) => boolType
          case _ => throw new Error("Illegal expression: "+e)
        }
        e.tpe = tpe
        tpe
      } catch { case m: Error => throw new Error(m.getMessage+"\nFound in: "+e) }

    def typecheck ( s: Stmt, return_types: List[Type], env: Environment ): Environment
      = try { s match {
          case VarDeclS(v,Some(t),Some(u))
            => if (!typeMatch(typecheck(u,env),t))
                 throw new Error("Incompatible value in: "+s)
               (v,t)::env
          case VarDeclS(v,Some(t),None)
            => (v,t)::env
          case VarDeclS(v,None,Some(u))
            => val t = typecheck(u,env)
               (v,t)::env
          case DefS(f,ps,tp,b)
            => typecheck(b,tp::return_types,ps.toList++env)
               (f,FunctionType(TupleType(ps.values.toList),tp))::env
          case BlockS(cs)
            => cs.foldLeft(env){ case (r,c) => typecheck(c,return_types,r) }
          case AssignS(d,v)
            => val dt = typecheck(d,env)
               val vt = typecheck(v,env)
               if (!typeMatch(dt,vt))
                  throw new Error("Incompatible values in assignment: "+s+" ("+dt+","+vt+")")
               else env
          case IfS(p,x,y)
            => if (typecheck(p,env) != boolType)
                  throw new Error("The if-statement condition "+p+" must be a boolean")
               typecheck(x,return_types,env)
               typecheck(y,return_types,env)
               env
          case ForS(v,a,b,c,u)
            => val at = typecheck(a,env)
               val bt = typecheck(b,env)
               val ct = typecheck(c,env)
               if (at != longType && at != intType)
                  throw new Error("For loop "+s+" must use an integer or long initial value: "+a)
               else if (bt != longType && bt != intType)
                  throw new Error("For loop "+s+" must use an integer or long final value: "+b)
               else if (ct != longType && ct != intType)
                  throw new Error("For loop "+s+" must use an integer or long step: "+c)
               else typecheck(u,return_types,(v,intType)::env)
          case ForeachS(p,c,b)
            => typecheck(c,env) match {
                  case ArrayType(d,t)
                    => typecheck(b,return_types,bindPattern(p,t,env))
                  case SeqType(t)
                    => typecheck(b,return_types,bindPattern(p,t,env))
                  case MapType(d,t)
                    => typecheck(b,return_types,bindPattern(p,t,env))
                  case ParametricType(f,List(t))
                    if isCollection(f)
                    => typecheck(b,return_types,bindPattern(p,t,env))
                  case tp => throw new Error("Foreach statement must be over a collection: "+s+" (found "+tp+")")
               }
          case WhileS(p,b)
            => if (typecheck(p,env) != boolType)
                  throw new Error("The while-statement condition "+p+" must be a boolean")
               typecheck(b,return_types,env)
          case ReturnS(u)
            => return_types match {
                  case rt::_
                    => if (!typeMatch(typecheck(u,env),rt))
                         throw new Error(s+" must return a value of type: "+rt)
                  case _ => throw new Error("A Return statement can only appear inside a function body: "+s)
               }
               env
          case ExprS(u)
            => typecheck(u,env)
               env
          case _ => throw new Error("Illegal statement: "+s)
    } } catch { case m: Error => throw new Error(m.getMessage+"\nFound in: "+s) }

    val localEnv: Environment = List()

    def typecheck ( s: Stmt ) { typecheck(s,Nil,localEnv) }
    def typecheck ( e: Expr ) { typecheck(e,localEnv) }
}
