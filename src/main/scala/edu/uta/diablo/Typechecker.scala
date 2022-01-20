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

import scala.util.matching.Regex
import scala.util.parsing.input.NoPosition

object Typechecker {
    import AST._
    import Lifting.{typeMap,getTypeMap}

    // binds variable names to types
    type Environment = Map[String,Type]

    val intType: Type = BasicType("Int")
    val longType: Type = BasicType("Long")
    val boolType: Type = BasicType("Boolean")
    val doubleType: Type = BasicType("Double")
    val stringType: Type = BasicType("String")

    // hooks to the Scala compiler; set at v_impl in Diablo.scala
    var typecheck_call: ( String, List[Type] ) => Option[Type] = _
    var typecheck_method: ( Type, String, List[Type] ) => Option[Type] = _
    var typecheck_var: String => Option[Type] = _

    val collection_names = List("array","map","List",collectionClass)

    val system_functions = List("binarySearch","zero","array2tensor","array2tensor_bool")

    var useStorageTypes: Boolean = false

    def tuple ( s: List[Expr] ): Expr
      = s match { case List(x) => x; case _ => Tuple(s) }

    def tuple ( s: List[Type] ): Type
      = s match { case List(x) => x; case _ => TupleType(s) }

    def tuple ( s: List[Pattern] ): Pattern
      = s match { case List(x) => x; case _ => TuplePat(s) }

    def isCollection ( f: String ): Boolean
      = collection_names.contains(f)

  type Env = Option[Environment]

  def substType ( tp: Type, env: Env ): Type
    = env match {
        case Some(m)
          => def f ( t: Type ): Type
              = t match {
                  case TypeParameter(n)
                    if m.contains(n)
                    => m(n)
                  case _ => apply(t,f)
                }
             f(tp)
        case _ => tp
      }

  def substType ( e: Expr, env: Env ): Expr
    = e match {
        case VarDecl(v,at,u)
          => VarDecl(v,substType(at,env),u)
        case Store(f,tps,args,v)
          => Store(f,tps.map(substType(_,env)),
                   args,substType(v,env))
        case _ => apply(e,substType(_,env))
      }

  def merge ( x: Env, y: Env ): Env
    = (x,y) match {
        case (Some(m1),Some(m2))
          => Some(m1++m2)
        case _ => None
      }

  def unfold_storage_type ( tp: Type ): Type
    = tp match {
        case StorageType(f,tps,_)
          => val Some(TypeMapS(_,ps,_,_,st,_,_,_)) = getTypeMap(f)
             substType(st,Some((ps zip tps).toMap))
        case _ => tp
      }

  def tmatch ( t1: Type, t2: Type ): Env
    = if (t1 == t2) Some(Map())
      else (unfold_storage_type(t1),unfold_storage_type(t2)) match {
         case (AnyType(),_)
           => Some(Map())
         case (_,AnyType())
           => Some(Map())
         case (TypeParameter(n),tp)
           => Some(Map(n->tp))
         case (tp,TypeParameter(n))
           => Some(Map(n->tp))
         case (TupleType(ts1),TupleType(ts2))
           if ts1.length == ts2.length
           => (ts1 zip ts2).map{ case (x,y) => tmatch(x,y) }.reduce[Env](merge)
         case (TupleType(List(t1)),t2)
           => tmatch(t1,t2)
         case (t1,TupleType(List(t2)))
           => tmatch(t1,t2)
         case (RecordType(rs1),RecordType(rs2))
           if rs1.keys == rs2.keys
           => ((rs1.values) zip (rs2.values)).map{ case (x,y) => tmatch(x,y) }.reduce[Env](merge)
         case (SeqType(st1),SeqType(st2))
           => tmatch(st1,st2)
         case (ArrayType(d1,et1),ArrayType(d2,et2))
           if d1 == d2
           => tmatch(et1,et2)
         case (MapType(tk1,tv1),MapType(tk2,tv2))
           => merge(tmatch(tk1,tk2),tmatch(tv1,tv2))
         case (ParametricType(n1,ts1),ParametricType(n2,ts2))
           if n1 == n2 && ts1.length == ts2.length
           => (ts1 zip ts2).map{ case (x,y) => tmatch(x,y) }.reduce[Env](merge)
         case _ => None
      }

    def typeMatch ( t1: Type, t2: Type ): Boolean
      = tmatch(t1,t2).nonEmpty

    def bindPattern ( pat: Pattern, tp: Type, env: Environment ): Environment
      = (pat,unfold_storage_type(tp)) match {
          case (TuplePat(cs),TupleType(ts))
            => if (cs.length != ts.length)
                 throw new Error("Pattern "+pat+" does not match the type "+tp)
               else cs.zip(ts).foldRight(env){ case ((p,t),r) => bindPattern(p,t,r) }
          case (VarPat(v),t)
            => env + (v -> t)
          case (StarPat(),_)
            => env
          case _ => throw new Error("Pattern "+pat+" does not match the type "+tp)
      }

  def elemType ( tp: Type ): Type
    = unfold_storage_type(tp) match {
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

    def import_type ( tp: Type, vname: String ): Type
      = tp match {
          case TupleType(List(itp,ParametricType(rdd,List(TupleType(List(ktp,
                                       TupleType(List(jtp,ArrayType(1,etp)))))))))
            // imported dense block tensor variable
            if (rdd == rddClass || rdd == datasetClass)
               && itp == intType && ktp == intType && jtp == intType
            => val cm = if (rdd == rddClass) "rdd" else "dataset"
               if (useStorageTypes)
                 StorageType(cm+"_block_tensor_1_0",List(etp),List(Nth(Var(vname),0)))
               else ArrayType(1,etp)
          case TupleType(List(itp,ParametricType(rdd,List(TupleType(List(ktp,
                     TupleType(List(jtp,TupleType(List(ArrayType(1,ct),ArrayType(1,rt),ArrayType(1,etp)))))))))))
            // imported sparse block tensor variable
            if (rdd == rddClass || rdd == datasetClass)
               && itp == intType && ktp == intType && jtp == intType
               && ct == intType && rt == intType
            => val cm = if (rdd == rddClass) "rdd" else "dataset"
               if (useStorageTypes)
                 StorageType(cm+"_block_tensor_0_1",List(etp),List(Nth(Var(vname),0)))
               else ArrayType(1,etp)
          case TupleType(is:+ParametricType(rdd,List(TupleType(List(TupleType(ks),
                                       TupleType(js:+ArrayType(1,etp)))))))
            // imported dense block tensor variable
            if (rdd == rddClass || rdd == datasetClass)
               && is.length == js.length && is.length == ks.length
               && (is++ks++js).forall(_ == intType)
            => val cm = if (rdd == rddClass) "rdd" else "dataset"
               if (useStorageTypes)
                 StorageType(cm+"_block_tensor_"+is.length+"_0",List(etp),
                             (1 to is.length).map(i => Nth(Var(vname),i)).toList)
               else ArrayType(is.length,etp)
          case TupleType(is:+ParametricType(rdd,List(TupleType(List(TupleType(ks),
                     TupleType(js:+TupleType(List(ArrayType(1,ct),ArrayType(1,rt),ArrayType(1,etp)))))))))
            // imported sparse block tensor variable
            if (rdd == rddClass || rdd == datasetClass)
               && is.length == js.length && is.length == ks.length
               && (ct::rt::is++ks++js).forall(_ == intType)
            => val cm = if (rdd == rddClass) "rdd" else "dataset"
               if (useStorageTypes)
                 StorageType(cm+"_block_tensor_"+(is.length-1)+"_1",List(etp),
                             (1 to is.length).map(i => Nth(Var(vname),i)).toList)
               else ArrayType(is.length,etp)
          case TupleType(is:+ArrayType(1,etp))     // imported tensor variable
            if is.forall(_ == intType)
            => if (useStorageTypes)
                 StorageType("tensor_"+is.length+"_0",List(etp),
                             (1 to is.length).map(i => Nth(Var(vname),i)).toList)
               else ArrayType(is.length,etp)
          case ParametricType(rdd,List(etp))
            if rdd == rddClass || rdd == datasetClass
            => val cm = if (rdd == rddClass) "rdd" else "dataset"
               if (useStorageTypes)
                 StorageType(cm,List(etp),Nil)
               else SeqType(etp)
          case _ => tp
      }

    def is_reduction ( op: String, tp: Type ): Boolean = {
      tp match {
        case SeqType(etp)
          => typecheck_call(op,List(etp,etp)) == Some(etp)
        case _ => false
      }
    }

    val tpat: Regex = """(full_|)tensor_(\d+)_(\d+)""".r
    val btpat: Regex = """(full_|)(rdd|dataset)_block_tensor_(\d+)_(\d+)""".r

    def typecheck ( e: Expr, env: Environment ): Type
      = if (e.tpe != null)
           e.tpe   // the cached type of e
        else try { val tpe = e match {
          case Var("null")
            => AnyType()
          case Var(v)
            => if (env.contains(v))
                 env(v)
               else import_type(typecheck_var(v). // call the Scala typechecker to find var v
                            getOrElse(throw new Error("Undefined variable: "+v)),v)
          case Nth(u,n)
            => unfold_storage_type(typecheck(u,env)) match {
                  case TupleType(cs)
                    => if (n<=0 || n>cs.length)
                          throw new Error("Tuple "+u+" does not contain a "+n+" element")
                       cs(n-1)
                  case t => throw new Error("Tuple projection "+e+" must be over a tuple (found "+t+")")
               }
          case Project(u,a)
            => unfold_storage_type(typecheck(u,env)) match {
                  case RecordType(cs)
                    => if (cs.contains(a))
                         cs(a)
                       else throw new Error("Unknown record attribute: "+a)
                  case _ => typecheck(MethodCall(u,a,null),env)
               }
          case Index(u,is)
            => val itps = is.map(i => typecheck(i,env))
               for { itp <- itps }
                  if ( itp != longType && itp != intType )
                    throw new Error("Matrix indexing "+e+" must use an integer row index: "+itp)
               unfold_storage_type(typecheck(u,env)) match {
                  case ArrayType(d,t)
                    if is.length == d
                    => t
                  case ArrayType(d,t)
                    => throw new Error("Array indexing "+e+" needs "+d+" indices (found "+is.length+" )")
                  case SeqType(TupleType(List(BasicType("Int"),t)))
                    if is.length == 1
                    => t
                  case SeqType(TupleType(List(TupleType(ts),t)))
                    if ts.forall(_ == intType) && ts.length == is.length
                    => t
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
                         val btp = typecheck(b,nenv)
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
                      => (unfold_storage_type(typecheck(u,r)) match {
                            case ArrayType(d,t)
                              => bindPattern(p,tuple(List(tuple((1 to d).map(i => intType).toList),t)),r)
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
                         ( bindPattern(p,ktp,r++s.diff(nvs).map{ v => (v,SeqType(r(v))) }.toMap),
                           nvs ++ s )
                    case ((r,s),AssignQual(d,u))
                      => typecheck(d,r)
                         typecheck(u,r)
                         (r,s)
                    case ((r,s),VarDef(n,at,u))
                      => val tp = typecheck(u,r)
                         if (!typeMatch(tp,at))
                           throw new Error("Incompatible value in variable declaration: "
                                           +e+"\n(expected "+at+" found "+tp+")")
                         ( bindPattern(VarPat(n),tp,r), n::s )
              }._1
              SeqType(typecheck(h,nenv))
          case Lift(f,ne)
            => val Some(TypeMapS(_,_,_,at,st,_,_,_)) = getTypeMap(f)
               val ev = tmatch(st,typecheck(ne,env))
               substType(at,ev)
          case x@Store(f,tps,args,u)
            => tps match {
                 case List(BasicType("Boolean"))
                   => f match {
                        case tpat(full,dn,sn) if sn.toInt > 0
                          => // change tensor_*_* to bool_tensor_*_*
                             x.mapping = full+"bool_"+f                         // destructive
                        case btpat(full,cn,dn,sn) if sn.toInt > 0
                          => // change block_tensor_*_* to block_bool_tensor_*_*
                             x.mapping = s"${full}${cn}_block_bool_tensor_${dn}_$sn"    // destructive
                        case _ => ;
                      }
                 case _ => ;
               }
               getTypeMap(x.mapping)
               args.map(typecheck(_,env))
               typecheck(u,env)
               StorageType(x.mapping,tps,args)
          case x@Call(f,args@(_:+l))
            if (f match { case tpat(_,_,_) => true; case btpat(_,_,_) => true; case _ => false })
            => typecheck(l,env) match {
                  case SeqType(TupleType(List(_, BasicType("Boolean"))))
                    => f match {
                        case tpat(full,dn,sn) if sn.toInt > 0
                          => // change tensor_*_* to bool_tensor_*_*
                             x.name = full+"bool_"+f                         // destructive
                        case btpat(full,cn,dn,sn) if sn.toInt > 0
                          => // change block_tensor_*_* to block_bool_tensor_*_*
                             x.name = s"${full}${cn}_block_bool_tensor_${dn}_$sn"    // destructive
                        case _ => ;
                      }
                  case _ => ;
               }
               val Some(TypeMapS(_,tps,ps,at,st,lt,view,store)) = getTypeMap(x.name)
               val ev = tmatch(tuple(ps.values.toList:+lt),tuple(args.map(typecheck(_,env))))
               if (ev.isEmpty)
                 throw new Error("Wrong tensor storage: "+x+"\n(expected: "
                                 +tuple(ps.values.toList:+lt)+", found: "
                                 +tuple(args.map(typecheck(_,env)))+")")
               if (useStorageTypes)
                 substType(st,ev)
               else substType(at,ev)
          case Call("_full",List(e))
            => typecheck(e,env) match {
                  case StorageType(f@tpat(_,dn,sn),tps,args)
                    if sn.toInt > 0       // full sparse tensor scan
                    => StorageType("full_"+f,tps,args)
                  case StorageType(f@btpat(_,_,dn,sn),tps,args)
                    if sn.toInt > 0       // full block sparse tensor scan
                    => StorageType("full_"+f,tps,args)
                  case tp => tp
               }
          case Call("unique_values",List(Lambda(VarPat(i),b)))
            => SeqType(typecheck(b,env+((i,intType))))
          case Call(f,args)
            if getTypeMap(f).isDefined
            => val Some(TypeMapS(_,tps,ps,at,st,lt,view,store)) = getTypeMap(f)
               val ev = tmatch(tuple(ps.values.toList:+lt),tuple(args.map(typecheck(_,env))))
               if (ev.isEmpty)
                 throw new Error("Wrong type storage: "+e+"\n(expected: "
                                 +tuple(ps.values.toList:+lt)+", found: "
                                 +tuple(args.map(typecheck(_,env)))+")")
               if (useStorageTypes)
                 substType(st,ev)
               else substType(at,ev)
          case Call(f,args)
            if env.contains(f)
            => val tp = typecheck(tuple(args),env)
               env(f) match {
                  case FunctionType(dt,rt)
                    => if (typeMatch(dt,tp)) rt
                       else throw new Error("Function "+f+" on "+dt
                                  +" cannot be applied to "+args+" of type "+tp);
                  case _ => throw new Error(f+" is not a function: "+e)
               }
          case Call(f,args)
            => // call the Scala typechecker to find function f
               val tas = args.map(typecheck(_,env)).map {
                                       case ArrayType(n,t)   // convert abstract arrays to storage tensors
                                         if !system_functions.contains(f)
                                         => tuple(1.to(n).map(i => intType).toList:+ArrayType(1,t))
                                       case t => t
                                  }
               typecheck_call(f,tas)
                 .getOrElse(throw new Error("Wrong function call: "+e+" for type "+tas))
          case MethodCall(u,"reduceByKey",List(Lambda(TuplePat(List(p1,p2)),b)))
            => val tu = typecheck(u,env)
               val TupleType(List(_,tp)) = elemType(tu)
               typecheck_method(tu,"reduceByKey",List(FunctionType(TupleType(List(tp,tp)),tp)))
                 .getOrElse(throw new Error("Wrong method call: "+e+" for type "+tu))
          case MethodCall(u,m,null)
            => // call the Scala typechecker to find method m
               val tu = typecheck(u,env)
               tu match {
                  case ArrayType(d,_)
                    if m == "dims"
                    => TupleType((1 to d).map(i => intType).toList)
                  case ArrayType(1,_)
                    if m == "length"
                    => intType
                  case ArrayType(2,_)
                    if m == "rows" || m == "cols"
                    => intType
                  case _ => typecheck_method(tu,m,null)
                                .getOrElse(throw new Error("Wrong method call: "+e+" for type "+tu))
               }
          case MethodCall(Var(op),"/",List(u))    // reduction such as max/e
            if is_reduction(op,typecheck(u,env))
            => typecheck(reduce(op,u),env)
          case MethodCall(u,m,args)
            => // call the Scala typechecker to find method m
               val tu = typecheck(u,env)
               val tas = args.map(typecheck(_,env))
               typecheck_method(tu,m,tas)
                 .getOrElse(throw new Error("Wrong method call: "+e+" for type "+tu+"."+tas))
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
          case Lambda(p,b)   // fix: needs type inference
            => val tp = TypeParameter(newvar)
               FunctionType(tp,typecheck(b,bindPattern(p,tp,env)))
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
            => val nenv = unfold_storage_type(typecheck(u,env)) match {
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
            => unfold_storage_type(typecheck(u,env)) match {
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
            => if (env.contains(m))
                 env(m) match {
                    case FunctionType(TupleType(List(t1,t2)),t3)
                      if t1 == t2 && t1 == t3
                      => elemType(typecheck(u,env))
                    case _ => throw new Error("The monoid "+m+" in reduction "+e+" is ill-formed")
                 } else {
                    val tp = elemType(typecheck(u,env))
                    typecheck_method(tp,m,List(tp)) match {
                      case Some(ftp) if ftp == tp => tp
                      case _ => typecheck_call(m,List(tp,tp)) match {
                                  case Some(ftp) if ftp == tp => tp
                                  case _ => throw new Error("Wrong monoid in "+e)
                                }
                    }
                 }
          case Block(es)
            => es.foldLeft((AnyType():Type,env)) {
                  case ((_,r),x@VarDecl(v,at,u))
                    => val tp = elemType(typecheck(u,r))  // type of u is concrete
                       if (!typeMatch(tp,at))
                         throw new Error("Incompatible value in variable declaration: "
                                         +x+"\n(expected "+at+" found "+tp+")")
                       if (useStorageTypes)
                          (tp,r + (v->tp))
                       else (at,r + (v->at))
                  case ((_,r),Def(f,List(p),tp,b))
                    => typecheck(b,r+p)
                       (tp,r + (f -> FunctionType(p._2,tp)))
                  case ((_,r),Def(f,ps,tp,b))
                    => typecheck(b,r++ps.toMap)
                       (tp,r + (f -> FunctionType(tuple(ps.map(_._2)),tp)))
                  case ((_,r),e)
                    => (typecheck(e,r),r)
               }._1
          case While(p,b)
            => if (elemType(typecheck(p,env)) != boolType)
                  throw new Error("The while-statement condition "+p+" must be a boolean")
               typecheck(b,env)
          case VarDecl(v,at,u)
            => val tp = elemType(typecheck(u,env))  // type of u is concrete
               if (!typeMatch(tp,at))
                 throw new Error("Incompatible value in variable declaration: "
                                 +e+"\n(expected "+at+" found "+tp+")")
               if (useStorageTypes) tp else at
          case Assign(d,u)
            => val ut = typecheck(u,env)    // u is lifted to a collection
               val dt = typecheck(d,env)
               if (!typeMatch(dt,ut) && !typeMatch(dt,elemType(ut)))
                 throw new Error("Incompatible values in assignment: "+e+"\nAssign( "+dt+" , "+ut+" )")
               else dt
          case Range(a,b,c)
            => val at = typecheck(a,env)
               val bt = typecheck(b,env)
               val ct = typecheck(c,env)
               if (at != longType && at != intType)
                  throw new Error("Range "+e+" must use an integer or long initial value: "+a)
               else if (bt != longType && bt != intType)
                  throw new Error("Range "+e+" must use an integer or long final value: "+b)
               else if (ct != longType && ct != intType)
                  throw new Error("Range "+e+" must use an integer or long step: "+c)
               SeqType(at)
          case StringConst(_) => stringType
          case IntConst(_) => intType
          case LongConst(_) => longType
          case DoubleConst(_) => doubleType
          case BoolConst(_) => boolType
          case _ => throw new Error("Illegal expression: "+e)
        }
        e.tpe = tpe
        tpe
      } catch { case m: Error
                  => val pos = e.pos
                     val line = if (pos == NoPosition) "" else " line "+pos
                     throw new Error(m.getMessage+"\nFound in"+line+": "+e+"\nwith env: "+env)
              }

    def typecheck ( s: Stmt, return_types: List[Type], env: Environment ): Environment
      = try { s match {
          case VarDeclS(v,Some(t),Some(u))
            => val tp = typecheck(u,env)
               if (!typeMatch(tp,t))
                 throw new Error("Incompatible value in: "+s+" (expected "+t+", found "+tp+")")
               env + (v->t)
          case VarDeclS(v,Some(t),None)
            => env + (v->t)
          case VarDeclS(v,None,Some(u))
            => val t = typecheck(u,env)
               env + (v->t)
          case DefS(f,List(p),tp,b)
            => typecheck(b,tp::return_types,env+p)
               env + (f -> FunctionType(p._2,tp))
          case DefS(f,ps,tp,b)
            => typecheck(b,tp::return_types,env++ps.toMap)
               env + (f -> FunctionType(TupleType(ps.map(_._2)),tp))
          case BlockS(cs)
            => cs.foldLeft(env){ case (r,c) => typecheck(c,return_types,r) }
          case AssignS(d,u)
            => val dt = typecheck(d,env)
               val ut = typecheck(u,env)
               (dt,ut) match {
                 case (ArrayType(1,edt),SeqType(TupleType(List(BasicType("Int"),eut))))
                   if typeMatch(edt,eut)
                   => env
                 case (ArrayType(d,edt),SeqType(TupleType(List(TupleType(is),eut))))
                   if is.length == d && !is.exists(_ != BasicType("Int")) && typeMatch(edt,eut)
                   => env
                 case _
                   => if (!typeMatch(dt,ut))
                        throw new Error("Incompatible values in assignment: "+s+" ("+dt+","+ut+")")
                      else env
               }
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
               else typecheck(u,return_types,env + (v->intType))
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
          case TypeMapS(f,tps,ps,at,st,lt,view,store)
            => typeMap(f,tps,ps,at,st,lt,view,store)
               env
          case _ => throw new Error("Illegal statement: "+s)
    } } catch { case m: Error
                  => val pos = s.pos
                     val line = if (pos == NoPosition) "" else " line "+pos
                     throw new Error(m.getMessage+"\nFound in"+line+": "+s)
              }

    // clean cached type info in every Expr node
    def clean ( e: Expr ): Boolean = {
      e.tpe = null
      accumulate[Boolean](e,x => clean(x),_||_,false)
    }

    def check ( e: Expr ): Boolean = {
      if (e.tpe == null)
        println("@@@ "+e)
      accumulate[Boolean](e,x => check(x),_||_,false)
    }

    val localEnv: Environment = Map()

    def typecheck ( s: Stmt ) { typecheck(s,Nil,localEnv) }
    def typecheck ( e: Expr ): Type = typecheck(e,localEnv)
}
