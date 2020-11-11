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

object Lifting {
  import AST._
  import Typechecker._
  import Normalizer.renameVars

  val N: Expr = IntConst(tileSize)

  val arrayBuffer = "scala.collection.mutable.ArrayBuffer"

  /* check and construct a new type mapping */
  def typeMap ( typeName: String, typeParams: List[String],
                abstractType: Type, storageType: Type, liftedType: Type,
                map: Lambda, inv: Lambda ) {
    { val Lambda(p,b) = map
      if (!typeMatch(typecheck(b,bindPattern(p,storageType,Map())),liftedType))
        throw new Error("Wrong type map: "+map)
    }
    val env = inv match {
                case Lambda(TuplePat(ps:+p),b)
                  => bindPattern(p,liftedType,ps.foldLeft[Environment](Map()) {
                                                case (r,p) => bindPattern(p,intType,r) })
                case Lambda(p,b)
                  => bindPattern(p,liftedType,Map())
        }
    val Lambda(p,b) = inv
    val nb = lift_expr(b,env)
    if (!typeMatch(typecheck(nb,env),storageType))
      throw new Error("Wrong type map inverse: "+nb+" "+typecheck(nb,env))
    typeMaps += typeName -> TypeMapS(typeName,typeParams,abstractType,storageType,
                                     liftedType,map,Lambda(inv.pattern,nb))
  }

  /* return a type mapping with fresh type variables */
  def fresh ( tm: TypeMapS ): TypeMapS
    = tm match {
        case TypeMapS(f,tps,at,st,lt,Lambda(pm,map),Lambda(pi,inv))
          if tps.nonEmpty
          => val ntps = tps.map(tp => newvar)
             val ev = Some((tps zip ntps).map{ case (tp,ntp) => tp -> TypeParameter(ntp) }.toMap)
             TypeMapS(f,ntps,substType(at,ev),substType(st,ev),substType(lt,ev),
                      renameVars(Lambda(pm,substType(map,ev))),
                      renameVars(Lambda(pi,substType(inv,ev))))
        case _ => tm
      }

  def initialize () {
    typeMap("vector",List("T"),
             ArrayType(1,TypeParameter("T")),
             ArrayType(1,TypeParameter("T")),
             SeqType(TupleType(List(intType,TypeParameter("T")))),
             Lambda(VarPat("A"),
                    Comprehension(Tuple(List(Var("i"),Index(Var("A"),List(Var("i"))))),
                                  List(Generator(VarPat("i"),
                                                 Range(IntConst(0),
                                                       MethodCall(MethodCall(Var("A"),"length",null),
                                                                  "-",List(IntConst(1))),
                                                       IntConst(1)))))),
             { val a = newvar
               Lambda(TuplePat(List(VarPat("d"),VarPat("L"))),
                      Block(List(VarDecl(a,ArrayType(1,TypeParameter("T")),
                                         Seq(List(Call("array",List(Var("d")))))),
                                 Comprehension(Assign(Index(Var(a),List(Var("i"))),
                                                      Seq(List(Var("v")))),
                                               List(Generator(TuplePat(List(VarPat("i"),VarPat("v"))),
                                                              Var("L")),
                                                    Predicate(MethodCall(Var("i"),"<",List(Var("d")))))),
                                 Var(a)))) })
    // a matrix in a sparse format
    typeMap("matrix",List("T"),
             ArrayType(2,TypeParameter("T")),
             TupleType(List(intType,intType,ArrayType(1,TypeParameter("T")))),
             SeqType(TupleType(List(TupleType(List(intType,intType)),
                                    TypeParameter("T")))),
             Lambda(VarPat("A"),
                    Comprehension(Tuple(List(Tuple(List(Var("i"),Var("j"))),
                                             Index(Var("a"),
                                                   List(MethodCall(MethodCall(Var("i"),"*",List(Var("n"))),
                                                                   "+",List(Var("j"))))))),
                                  List(LetBinding(TuplePat(List(VarPat("n"),VarPat("m"),VarPat("a"))),
                                                  Var("A")),
                                       Generator(VarPat("i"),
                                                 Range(IntConst(0),
                                                       MethodCall(Var("n"),"-",List(IntConst(1))),
                                                       IntConst(1))),
                                       Generator(VarPat("j"),
                                                 Range(IntConst(0),
                                                       MethodCall(Var("m"),"-",List(IntConst(1))),
                                                       IntConst(1)))))),
             { val a = newvar
               Lambda(TuplePat(List(VarPat("n"),VarPat("m"),VarPat("L"))),
                      Block(List(VarDecl(a,ArrayType(1,TypeParameter("T")),
                                         Seq(List(Call("array",List(MethodCall(Var("n"),"*",List(Var("m")))))))),
                                 Comprehension(Assign(Index(Var(a),
                                                            List(MethodCall(MethodCall(Var("i"),"*",List(Var("n"))),
                                                                            "+",List(Var("j"))))),
                                                      Seq(List(Var("v")))),
                                               List(Generator(TuplePat(List(TuplePat(List(VarPat("i"),VarPat("j"))),
                                                                            VarPat("v"))),
                                                              Var("L")),
                                                    Predicate(MethodCall(Var("i"),"<",List(Var("n")))),
                                                    Predicate(MethodCall(Var("j"),"<",List(Var("m")))))),
                                 Tuple(List(Var("n"),Var("m"),Var(a)))))) })
      // a square tile of size tileSize*tileSize
      typeMap("tile",List("T"),
               ArrayType(2,TypeParameter("T")),
               ArrayType(1,TypeParameter("T")),
               SeqType(TupleType(List(TupleType(List(intType,intType)),
                                      TypeParameter("T")))),
               Lambda(VarPat("A"),
                      Comprehension(Tuple(List(Tuple(List(Var("i"),Var("j"))),
                                               Index(Var("A"),
                                                     List(MethodCall(MethodCall(Var("i"),"*",List(N)),
                                                                     "+",List(Var("j"))))))),
                                    List(Generator(VarPat("i"),
                                                   Range(IntConst(0),IntConst(tileSize-1),IntConst(1))),
                                         Generator(VarPat("j"),
                                                   Range(IntConst(0),IntConst(tileSize-1),IntConst(1)))))),
               { val a = newvar
                 Lambda(VarPat("L"),
                        Block(List(VarDecl(a,ArrayType(1,TypeParameter("T")),
                                           Seq(List(Call("array",List(IntConst(tileSize*tileSize)))))),
                                   Comprehension(Assign(Index(Var(a),
                                             List(MethodCall(MethodCall(MethodCall(Var("i"),"%",List(N)),
                                                                        "*",List(N)),
                                                             "+",List(MethodCall(Var("j"),"%",List(N)))))),
                                                        Seq(List(Var("v")))),
                                          List(Generator(TuplePat(List(TuplePat(List(VarPat("i"),VarPat("j"))),
                                                                       VarPat("v"))),
                                                         Var("L")))),
                                   Var(a)))) })
      // a matrix in a compressed sparse column (CSC) format
      typeMap("CSC",List("T"),
               ArrayType(2,TypeParameter("T")),
               TupleType(List(intType,                              // numCols
                              intType,                              // colPtrs
                              ArrayType(1,intType),                 // colPtrs
                              ArrayType(1,intType),                 // rowIndices
                              ArrayType(1,TypeParameter("T")))),    // values
               SeqType(TupleType(List(TupleType(List(intType,intType)),
                                      TypeParameter("T")))),
               Lambda(VarPat("A"),
                      Comprehension(Tuple(List(Tuple(List(Index(Nth(Var("A"),4),
                                                                List(Var("col"))),
                                                          Var("j"))),
                                               Index(Nth(Var("A"),5),
                                                     List(Var("col"))))),
                                    List(Generator(VarPat("j"),
                                                   Range(IntConst(0),
                                                         MethodCall(Nth(Var("A"),2),"-",List(IntConst(1))),
                                                         IntConst(1))),
                                         Generator(VarPat("col"),
                                                   Range(Index(Nth(Var("A"),3),List(Var("j"))),
                                                         Index(Nth(Var("A"),3),List(MethodCall(Var("j"),"+",
                                                                                               List(IntConst(1))))),
                                                         IntConst(1)))))),
              Lambda(TuplePat(List(VarPat("n"),VarPat("m"),VarPat("L"))),
                     Block(List(VarDecl("cols",ParametricType(arrayBuffer,List(intType)),Seq(Nil)),
                                VarDecl("rows",ParametricType(arrayBuffer,List(intType)),Seq(Nil)),
                                VarDecl("values",ParametricType(arrayBuffer,List(TypeParameter("T"))),Seq(Nil)),
                                Comprehension(
                                    Block(List(MethodCall(Var("rows"),"+=",List(Var("i"))),
                                               MethodCall(Var("values"),"+=",List(Var("v"))))),
                                    List(Generator(VarPat("j"),
                                             Range(IntConst(0),
                                                   MethodCall(Var("m"),"-",List(IntConst(1))),
                                                   IntConst(1))),
                                         Predicate(Block(List(MethodCall(Var("cols"),"+=",List(Var("j"))),
                                                              BoolConst(true)))),
                                         Generator(TuplePat(List(TuplePat(List(VarPat("i"),VarPat("jj"))),
                                                                 VarPat("v"))),
                                                   Var("L")),
                                         Predicate(MethodCall(Var("jj"),"==",List(Var("j")))),
                                         Predicate(MethodCall(Var("v"),"!=",List(DoubleConst(0.0)))))),
                                Tuple(List(Var("n"),Var("m"),
                                           MethodCall(Var("cols"),"toArray",null),
                                           MethodCall(Var("rows"),"toArray",null),
                                           MethodCall(Var("values"),"toArray",null)))))))
    typeMap("rdd",List("T"),
             SeqType(TypeParameter("T")),
             ParametricType(rddClass,List(TypeParameter("T"))),
             SeqType(TypeParameter("T")),
             Lambda(VarPat("R"),
                    MethodCall(MethodCall(Var("R"),"collect",Nil),"toList",null)),
             Lambda(VarPat("L"),
                    MethodCall(Var("spark_context"),"parallelize",
                               List(Var("L")))))
    typeMap("tiled",List("T"),
             ArrayType(2,TypeParameter("T")),
             TupleType(List(intType,intType,
                            StorageType("rdd",List(TupleType(List(TupleType(List(intType,intType)),
                                                   StorageType("tile",List(TypeParameter("T")),
                                                               Nil)))),
                                        Nil))),
             SeqType(TupleType(List(TupleType(List(intType,intType)),
                                    TypeParameter("T")))),
             Lambda(VarPat("V"),
                   Comprehension(Tuple(List(Tuple(List(MethodCall(MethodCall(Var("ii"),"*",List(N)),
                                                                  "+",List(Var("i"))),
                                                       MethodCall(MethodCall(Var("jj"),"*",List(N)),
                                                                  "+",List(Var("j"))))),
                                            Index(Var("v"),
                                                  List(MethodCall(MethodCall(Var("i"),"*",List(N)),
                                                                  "+",List(Var("j"))))))),
                                 List(LetBinding(TuplePat(List(VarPat("n"),VarPat("m"),VarPat("a"))),
                                                 Var("V")),
                                      Generator(TuplePat(List(TuplePat(List(VarPat("ii"),VarPat("jj"))),
                                                              VarPat("v"))),
                                                Lift("rdd",Var("a"))),
                                      Generator(VarPat("i"),
                                                Range(IntConst(0),IntConst(tileSize-1),IntConst(1))),
                                      Generator(VarPat("j"),
                                                Range(IntConst(0),IntConst(tileSize-1),IntConst(1)))))),
             Lambda(TuplePat(List(VarPat("n"),VarPat("m"),VarPat("L"))),
                    Tuple(List(Var("n"),Var("m"),
                           Call("rdd",List(Comprehension(Tuple(List(Tuple(List(Var("ii"),Var("jj"))),
                                                        Call("tile",List(Var("w"))))),
                                   List(Generator(TuplePat(List(TuplePat(List(VarPat("i"),VarPat("j"))),
                                                                VarPat("v"))),
                                                  Call("rdd",List(Var("L")))),
                                        LetBinding(VarPat("ii"),MethodCall(Var("i"),"/",List(N))),
                                        LetBinding(VarPat("jj"),MethodCall(Var("j"),"/",List(N))),
                                        LetBinding(VarPat("w"),
                                              Tuple(List(Tuple(List(MethodCall(Var("i"),"%",List(N)),
                                                                    MethodCall(Var("j"),"%",List(N)))),
                                                         Var("v")))),
                                        GroupByQual(TuplePat(List(VarPat("ii"),VarPat("jj"))),
                                                    Tuple(List(Var("ii"),Var("jj"))))))))))))
    for { d <- 1 to 9 } {
       val vs = (0 until d).map(_ => newvar).toList
       typeMap("darray"+d,List("T"),
             ArrayType(d,TypeParameter("T")),
             StorageType("rdd",List(TupleType(List(tuple((0 until d).map(_ => intType).toList),
                                                   TypeParameter("T")))),Nil),
             SeqType(TupleType(List(tuple((0 until d).map(_ => intType).toList),TypeParameter("T")))),
             Lambda(VarPat("R"),
                    Comprehension(Tuple(List(tuple(vs.map(Var)),Var("v"))),
                                  List(Generator(TuplePat(List(tuple(vs.map(VarPat)),VarPat("v"))),
                                                 Var("R"))))),
             Lambda(VarPat("L"),
                    Call("rdd",List(Comprehension(Tuple(List(tuple(vs.map(Var)),Var("v"))),
                                  List(Generator(TuplePat(List(tuple(vs.map(VarPat)),VarPat("v"))),
                                                 Var("L"))))))))
    }
  }

  def lift_domain ( e: Expr, env: Environment ): Expr = {
    e.tpe = null    // clear the type info of e
    typecheck(e,env) match {
        case StorageType(f,tps,args)
          => val TypeMapS(_,ps,_,t1,_,map,_) = fresh(typeMaps(f))
             Apply(map,e)
        case _ => e
     }
  }

  def lift_assign ( src: Expr, dtype: Type, stype: Type, env: Environment ): Expr
    = dtype match {
        case StorageType(f,tps,args)
          if !typeMatch(dtype,stype)
          => val nv = newvar
             val TypeMapS(_,ps,tp,_,t2,_,inv) = fresh(typeMaps(f))
             val ev = tmatch(t2,stype)
             if (ev.nonEmpty)
                Comprehension(Store(f,ps.map(ev.get(_)),args,Var(nv)),
                              List(Generator(VarPat(nv),src)))
             else src
        case _
          => (dtype,stype) match {
                case (TupleType(ts1),TupleType(ts2))
                  => tuple((ts1 zip ts2).zipWithIndex
                           .map{ case ((t1,t2),i) => lift_assign(Nth(src,i+1),t1,t2,env) })
                case (RecordType(rs1),RecordType(rs2))
                  => Record((((rs1.values) zip (rs2.values)) zip rs1.keys)
                            .map{ case ((t1,t2),a) => a -> lift_assign(Project(src,a),t1,t2,env) }.toMap)
                case _ => src
             }
      }

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
                  case ((r,s),VarDecl(v,at,u@Seq(List(Call("array",_)))))
                    => (r + (v->at),
                        s:+VarDecl(v,at,u))
                  case ((r,s),x@VarDecl(v,at,Seq(Nil)))
                    => (r + (v->at), s:+x)
                  case ((r,s),VarDecl(v,at,u))
                    => val nu = lift_expr(u,r)
                       val tp = elemType(typecheck(nu,r))
                       (r + (v->tp),
                        s:+VarDecl(v,tp,nu))
                  case ((r,s),Def(f,ps,tp,b))
                    => (r + (f->FunctionType(TupleType(ps.values.toList),tp)),
                        s:+Def(f,ps,tp,lift_expr(b,r)))
                  case ((r,s),e)
                    => (r,s:+lift_expr(e,r))
             }._2)
        case Call(f,args:+x)
            if typeMaps.contains(f)
            => val nargs = args.map(lift_expr(_,env))
               val nx = lift_expr(x,env)
               val TypeMapS(_,ps,_,_,lt,_,_) = fresh(typeMaps(f))
               tmatch(lt,typecheck(nx,env)) match {
                 case Some(ev)
                   => Store(f,ps.map(v => ev.getOrElse(v,TypeParameter(v))),nargs,nx)
                 case _ => throw new Error("Wrong type mapping: "+e)
               }
        case Assign(d,u)
          => val dl = lift_expr(d,env)
             val ul = lift_expr(u,env)
             val dt = typecheck(dl,env)
             val ut = elemType(typecheck(ul,env))
             Assign(dl,lift_assign(ul,dt,ut,env))
        case Comprehension(h,qs)
          => val (nenv,_,nqs)
                = qs.foldLeft((env,Nil:List[String],Nil:List[Qualifier])) {
                    case ((r,s,n),Generator(p,u))
                      => val lu = lift_expr(u,r)
                         lu.tpe = null    // clear the type info of e
                         typecheck(lu,r) match {
                            case StorageType(f,tps,args)
                              => val TypeMapS(_,ps,_,t1,lt,map,_) = fresh(typeMaps(f))
                                 val tp = substType(lt,Some((ps zip tps).toMap))
                                 ( bindPattern(p,elemType(tp),r),
                                   s ++ patvars(p),
                                   n:+Generator(p,Lift(f,lu)) )
                            case _
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
    val TypeMapS(_,_,_,_,_,map,_) = fresh(typeMaps(mapping))
    Apply(map,storage)
  }

  def store ( mapping: String, typeParams: List[Type], args: List[Expr], value: Expr ): Expr = {
    val TypeMapS(_,tps,_,_,_,_,inv) = fresh(typeMaps(mapping))
    val ev = Some((tps zip typeParams).toMap)
    substType(Apply(inv,tuple(args:+value)),ev)
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
