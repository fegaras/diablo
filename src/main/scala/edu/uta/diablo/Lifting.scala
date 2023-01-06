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

import TypeMappings.{tensor,full_tensor,block_tensor}
import scala.util.matching.Regex

object Lifting {
  import AST._
  import Typechecker._
  import Normalizer.{normalizeAll,renameVars}
  import scala.collection.mutable

  // Contains the natural transformations for type abstractions
  var typeMaps: mutable.Map[String,TypeMapS] = mutable.Map[String,TypeMapS]()

  /** check and construct a new type mapping */
  def typeMap ( typeName: String, typeParams: List[String], params: Map[String,Type],
                abstractType: Type, storageType: Type, liftedType: Type,
                view: Lambda, store: Lambda ): Unit = {
    def storage_type ( tp: Type ): Type
      = tp match {
          case ParametricType(f,ts)
            if typeMaps.contains(f)
            => StorageType(f,ts.map(storage_type),Nil)
          case _ => apply(tp,storage_type)
        }
    val st = storage_type(storageType)
    val Lambda(vp,vb) = view
    val Lambda(sp,sb) = store
    val venv = bindPattern(vp,st,params)
    if (vb != Tuple(Nil) && !typeMatch(typecheck(vb,venv),liftedType))
      throw new Error("Wrong view function: "+view+" "+typecheck(vb,venv)+" "+liftedType)
    val nvp = tuple(params.keys.toList.map(VarPat):+vp)
    val senv = bindPattern(sp,liftedType,params)
    val nsp = tuple(params.keys.toList.map(VarPat):+sp)
    val nsb = tuple(params.keys.toList.map(Var):+lift_expr(sb,senv))
    val nst = tuple(params.values.toList:+st)
    if (sb != Tuple(Nil) && !typeMatch(typecheck(nsb,senv),nst))
      throw new Error("Wrong store function: "+store+" "+typecheck(nsb,senv)+" "+nst)
    typeMaps += typeName -> TypeMapS(typeName,typeParams,params,abstractType,nst,
                                     liftedType,Lambda(nvp,vb),Lambda(nsp,nsb))
  }

  val pat: Regex = """(full_|)(rdd_block_|dataset_block_|)(bool_|)tensor_(\d+)_(\d+)""".r
  val btpat: Regex = """(full_|)bool_tensor_(\d+)_(\d+)""".r
  val tpat: Regex = """(full_|)tensor_(\d+)_(\d+)""".r
  val bpat: Regex = """(full_|)(rdd|dataset)_block_tensor_(\d+)_(\d+)""".r
  val bbtpat: Regex = """(full_|)(rdd|dataset)_block_bool_tensor_(\d+)_(\d+)""".r

  // get a type map if exists, or create a type map from a tensor
  def getTypeMap ( name: String ): Option[TypeMapS] = {
     if (typeMaps.contains(name))
        Some(typeMaps(name))
      else {
        val tm = name match {
          case btpat("",dn,sn)
            => tensor(dn.toInt,sn.toInt,true)
          case tpat("",dn,sn)
            => tensor(dn.toInt,sn.toInt)
          case btpat(_,dn,sn)
            => full_tensor(dn.toInt,sn.toInt,true)
          case tpat(_,dn,sn)
            => full_tensor(dn.toInt,sn.toInt)
          case bbtpat(full,cm,dn,sn)
            => block_tensor(dn.toInt,sn.toInt,cm,true,full)
          case bpat(full,cm,dn,sn)
            => block_tensor(dn.toInt,sn.toInt,cm,false,full)
          case _ => ""
        }
        if (tm != "") {
          if (trace) println(s"Loading $name:"+tm)
          typecheck(Parser.parse(tm))
          Some(typeMaps(name))
        } else None
    }
  }

  /* return a type mapping with fresh type variables */
  def fresh ( tm: TypeMapS ): TypeMapS
    = tm match {
        case TypeMapS(f,tps,ps,at,st,lt,Lambda(pm,map),Lambda(pi,inv))
          if tps.nonEmpty
          => val ntps = tps.map(tp => newvar)
             val ev = Some((tps zip ntps).map{ case (tp,ntp) => tp -> TypeParameter(ntp) }.toMap)
             TypeMapS(f,ntps,ps,substType(at,ev),substType(st,ev),substType(lt,ev),
                      renameVars(Lambda(pm,substType(map,ev))),
                      renameVars(Lambda(pi,substType(inv,ev))))
        case _ => tm
      }

  def lift_domain ( e: Expr, env: Environment ): Expr = {
    e.tpe = null    // clear the type info of e
    typecheck(e,env) match {
        case StorageType(f,tps,args)
          => val Some(TypeMapS(_,_,_,_,t1,_,map,_)) = getTypeMap(f).map(fresh)
             Apply(map,e)
        case _ => e
     }
  }

  /* if the source type doesn't match the destination type in an assignment, coerce the source */
  def lift_assign ( src: Expr, dtype: Type, stype: Type, env: Environment ): Expr
    = if (typeMatch(dtype,stype))
        src
      else (dtype,stype) match {
        case (StorageType(f,tps,args),SeqType(tp))
          => val nv = newvar
             Comprehension(Store(f,tps,args,Var(nv)),
                           List(Generator(VarPat(nv),src)))
        case (StorageType(f,tps,args),StorageType(g,_,_))
          => val nv = newvar
             Comprehension(Store(f,tps,args,Lift(g,Var(nv))),
                           List(Generator(VarPat(nv),src)))
        case (TupleType(ts1),TupleType(ts2))
          => tuple((ts1 zip ts2).zipWithIndex
                       .map{ case ((t1,t2),i) => lift_assign(Nth(src,i+1),t1,t2,env) })
        case (RecordType(rs1),RecordType(rs2))
          => Record((((rs1.values) zip (rs2.values)) zip rs1.keys)
                       .map{ case ((t1,t2),a) => a -> lift_assign(Project(src,a),t1,t2,env) }.toMap)
        case _ => src
      }

  val array_buffer_pat: Regex = """array_buffer([_a-z]*)""".r

  def lift_expr ( e: Expr, env: Environment ): Expr
    = e match {
        case Let(p,u,b)
          => Let(p,lift_expr(u,env),
                 lift_expr(b,bindPattern(p,typecheck(u,env),env)))
        case MatchE(u,cs)
          => val tp = typecheck(u,env)
             MatchE(lift_expr(u,env),
                    cs.map {
                       case Case(p,c,b)
                         => val nenv = bindPattern(p,tp,env)
                            Case(p,lift_expr(c,nenv),lift_expr(b,nenv)) })
        case Block(es)
          => Block(es.foldLeft((env,Nil:List[Expr])) {
                  case ((r,s),x@VarDecl(v,at,Seq(List(Call("array",_)))))
                    => (r + (v->at), s:+x)
                  case ((r,s),x@VarDecl(v,at,Seq(List(Call(array_buffer_pat(_),_)))))
                    => (r + (v->at), s:+x)
                  case ((r,s),x@VarDecl(v,at,Seq(List(Var(w)))))
                    => (r + (v->r(w)),
                        s:+VarDecl(v,r(w),Seq(List(Var(w)))))
                  case ((r,s),x@VarDecl(v,at,Seq(Nil)))
                    => (r + (v->at), s:+x)
                  case ((r,s),VarDecl(v,at,u))
                    => val nu = lift_expr(u,r)
                       val tp = elemType(typecheck(nu,r))
                       (r + (v->tp),
                        s:+VarDecl(v,tp,nu))
                  case ((r,s),Def(f,ps,tp,b))
                    => (r + (f->FunctionType(TupleType(ps.map(_._2)),tp)),
                        s:+Def(f,ps,tp,lift_expr(b,r)))
                  case ((r,s),e)
                    => (r,s:+lift_expr(e,r))
             }._2)
        case Call(f,args:+x)
            if typeMaps.contains(f)
            => val nargs = args.map(lift_expr(_,env))
               val nx = lift_expr(x,env)
               val TypeMapS(_,ps,_,_,_,lt,_,_) = fresh(typeMaps(f))
               tmatch(lt,typecheck(nx,env)) match {
                 case Some(ev)
                   => Store(f,ps.map(v => ev.getOrElse(v,TypeParameter(v))),nargs,nx)
                 case _ => throw new Error("Wrong type mapping: "+e)
               }
        case Assign(d,Call("update_array",List(a,u)))
          => val dl = lift_expr(d,env)
             val ul = lift_expr(u,env)
             val dt = typecheck(dl,env)
             val ut = elemType(typecheck(ul,env))
             Assign(dl,Call("update_array",List(a,lift_assign(ul,dt,ut,env))))
        case Assign(d,Call("increment_array",List(a,op,u)))
          => val dl = lift_expr(d,env)
             val ul = lift_expr(u,env)
             val dt = typecheck(dl,env)
             val ut = elemType(typecheck(ul,env))
             Assign(dl,Call("increment_array",List(a,op,lift_assign(ul,dt,ut,env))))
        case Assign(d,u)
          => val dl = lift_expr(d,env)
             val ul = lift_expr(u,env)
             val dt = typecheck(dl,env)
             val ut = elemType(typecheck(ul,env))
             Assign(dl,lift_assign(ul,dt,ut,env))
        case Comprehension(h,qs)
          => val (nenv,_,nqs)
                = qs.foldLeft((env,Nil:List[String],Nil:List[Qualifier])) {
                    case ((r,s,n),Generator(p,Call("_full",List(u))))
                      => val lu = lift_expr(u,r)
                         lu.tpe = null    // clear the type info of e
                         typecheck(lu,r) match {
                            case StorageType(f@pat(_,_,_,_,sn),tps,args)
                              if sn.toInt > 0
                              => val Some(TypeMapS(_,ps,_,_,t1,lt,map,_)) = getTypeMap("full_"+f).map(fresh)
                                 val tp = substType(lt,Some((ps zip tps).toMap))
                                 ( bindPattern(p,elemType(tp),r),
                                   s ++ patvars(p),
                                   n:+Generator(p,Lift("full_"+f,lu)) )
                            case StorageType(f,tps,args)
                              => val Some(TypeMapS(_,ps,_,_,t1,lt,map,_)) = getTypeMap(f).map(fresh)
                                 val tp = substType(lt,Some((ps zip tps).toMap))
                                 ( bindPattern(p,elemType(tp),r),
                                   s ++ patvars(p),
                                   n:+Generator(p,Lift(f,lu)) )
                            case _
                              => ( bindPattern(p,elemType(typecheck(lu,r)),r),
                                   s ++ patvars(p),
                                   n:+Generator(p,lu) )
                         }
                    case ((r,s,n),Generator(p,u))
                      => val lu = lift_expr(u,r)
                         lu.tpe = null    // clear the type info of e
                         typecheck(lu,r) match {
                            case StorageType(f,tps,args)
                              => val Some(TypeMapS(_,ps,_,_,t1,lt,map,_)) = getTypeMap(f).map(fresh)
                                 val tp = substType(lt,Some((ps zip tps).toMap))
                                 ( bindPattern(p,elemType(tp),r),
                                   s ++ patvars(p),
                                   n:+Generator(p,Lift(f,lu)) )
                            case tp
                              => ( bindPattern(p,elemType(typecheck(lu,r)),r),
                                   s ++ patvars(p),
                                   n:+Generator(p,lu) )
                         }
                    case ((r,s,n),LetBinding(p,d))
                      => val tp = typecheck(d,r)
                         ( bindPattern(p,tp,r),
                           s++patvars(p),
                           n:+LetBinding(p,lift_expr(d,r)) )
                    case ((r,s,n),GroupByQual(p,k))
                      => val nvs = patvars(p)
                         val ktp = typecheck(k,r)
                         // lift all pattern variables to bags
                         ( bindPattern(p,ktp,r++s.diff(nvs).map{ v => (v,SeqType(r(v))) }.toMap),
                           nvs ++ s,
                           n:+GroupByQual(p,lift_expr(k,r)) )
                    case ((r,s,n),Predicate(p))
                      => (r,s,n:+Predicate(lift_expr(p,r)))
                    case ((r,s,n),q)
                      => (r,s,n:+q)
                  }
             Comprehension(lift_expr(h,nenv),nqs)
        case Apply(Lambda(p,b),arg)
          => val na = lift_expr(arg,env)
             Apply(Lambda(p,lift_expr(b,bindPattern(p,typecheck(na,env),env))),na)
        case _ => apply(e,lift_expr(_,env))
      }

  def lift ( mapping: String, storage: Expr ): Expr = {
    val Some(TypeMapS(_,tps,_,_,st,lt,map,_)) = getTypeMap(mapping).map(fresh)
    val view = if (mapping == "dataset")
                 Coerce(MethodCall(MethodCall(storage,"collect",Nil),"toList",null),lt)
               else Apply(map,storage)
    if (storage.tpe == null) view
    else {
      val ev = tmatch(st,storage.tpe)
      substType(view,ev)
    }
  }

  def store ( mapping: String, typeParams: List[Type], args: List[Expr], value: Expr ): Expr = {
    val TypeMapS(_,tps,_,_,_,_,_,inv) = fresh(typeMaps(mapping))
    val f = if (mapping == "dataset") {
              val vs = args.map(v => newvar)
              Lambda(TuplePat(vs.map(VarPat):+VarPat("_x")),
                     Tuple(vs.map(Var):+Coerce(MethodCall(Var("_x"),"toDF",null),
                                               ParametricType(datasetClass,List(typeParams.head)))))
            } else inv
    val ev = Some((tps zip typeParams).toMap)
    substType(normalizeAll(Apply(f,tuple(args:+value))),ev)
  }

  def lift ( e: Expr ): Expr = {
    def fe ( e: Expr ): Expr = {
      e.tpe = null
      e match {
          case Var(v)
            => Var(v) // erase e.tpe
          case VarDecl(v,tp,u)
            => VarDecl(v,tp,fe(u))
          case _ => apply(e,fe)
        }
    }
    useStorageTypes = true  // from now on, use storage types
    e match {
      case Block(_)
        => fe(lift_expr(e,Map()))
      case _
        => fe(lift_expr(Block(List(e)),Map()))
    }
  }
}
