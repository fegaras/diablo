/*
 * Copyright © 2022-2023 University of Texas at Arlington
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

object SQLGenerator {
  import AST._
  import ComprehensionTranslator._
  import Typechecker.{tuple=>_,_}

  type Env = Map[String,Expr]

  val dataFrameClass = "org.apache.spark.sql.DataFrame"

  var sql_tables: List[String] = Nil

  case class SQL ( select: List[Expr], from: Env, lateralView: Env,
                   where: List[Expr], groupBy: Option[Expr], having: List[Expr] )

  def bind ( p: Pattern, e: Expr, env: Env ): Env
    = p match {
        case VarPat(v)
          => env+(v->e)
        case TuplePat(ps)
          => e match {
               case Tuple(es)
                 => (ps zip es).foldLeft(env) { case (m,(q,u)) => bind(q,u,m) }
               case _ => ps.zipWithIndex.foldLeft(env) {
                             case (m,(q,i)) => bind(q,Nth(e,i+1),m)
                         }
             }
        case _ => env
      }

  def typenv ( qs: List[Qualifier], env: Environment ): Environment
    = qs.foldLeft(env) {
         case (r,Generator(p,u))
           => bindPattern(p,elemType(typecheck(u,r)),r)
         case (r,LetBinding(p,u))
           => bindPattern(p,typecheck(u,r),r)
         case (r,GroupByQual(p,k))
           => bindPattern(p,typecheck(k,r),
                          r.map{ case (v,tp) => (v,SeqType(tp)) })   // lift local vars
         case (r,_) => r
      }

  def translate ( hs: Expr, qs: List[Qualifier], env: Environment ): (SQL,List[Expr]) = {
    val (el,SQL(s,f,l,w,g,h),binds,nenv)
        = qs.foldLeft[(List[Expr],SQL,Env,Environment)]((Nil,SQL(Nil,Map(),Map(),Nil,None,Nil),Map(),env)) {
             case ((es,SQL(s,f,l,w,g,h),binds,r),e)
               => e match {
                    case Generator(VarPat(v),Range(n1,n2,n3))
                      => val (nn1,el1) = translate(n1,binds,r)
                         val (nn2,el2) = translate(MethodCall(n2,"+",List(IntConst(1))),binds,r)
                         val (nn3,el3) = translate(n3,binds,r)
                         val nu = Call("range",List(nn1,nn2,nn3))
                         val id = Call("rangeVar",List(Var(v)))
                         (es++el1++el2++el3,
                          SQL(s,f+(v->nu),l,w,g,h),
                          binds+(v->id),
                          r+(v->intType))
                    case Generator(p,d@Lift("dataset",u))
                      => val v = newvar
                         val nu = translate_domain(u)
                         val view = MethodCall(nu,"createOrReplaceTempView",List(StringConst(v)))
                         sql_tables = sql_tables:+v
                         (es:+view,
                          SQL(s,f+(v->Var(v)),l,w,g,h),
                          bind(p,Var(v),binds+(v->Var(v))),
                          bindPattern(p,elemType(typecheck(d,r)),r))
                    case Generator(p,d@Lift("rdd",u))
                      => val v = newvar
                         val nu = translate_domain(u)
                         val view = MethodCall(MethodCall(nu,"toDF",null),
                                               "createOrReplaceTempView",List(StringConst(v)))
                         sql_tables = sql_tables:+v
                         (es:+view,
                          SQL(s,f+(v->Var(v)),l,w,g,h),
                          bind(p,Var(v),binds+(v->Var(v))),
                          bindPattern(p,elemType(typecheck(d,r)),r))
                    case Generator(p,u)
                      => // silly SQL uses lateral views & explode for dependent joins
                         val v = newvar
                         val (nu,el) = translate(u,binds,r)
                         (es++el,
                          SQL(s,f,l+(v->nu),w,g,h),
                          bind(p,Var(v),binds+(v->Var(v))),
                          bindPattern(p,elemType(typecheck(u,r)),r))
                    case Predicate(u)
                      if g.isEmpty
                      => val (nu,el) = translate(u,binds,r)
                         (es++el,SQL(s,f,l,w:+nu,g,h),binds,r)
                    case Predicate(u)
                      => val (nu,el) = translate(u,binds,r)
                         (es++el,SQL(s,f,l,w,g,h:+nu),binds,r)
                    case LetBinding(p,u)
                      => val (nu,el) = translate(u,binds,r)
                         (es++el,
                          SQL(s,f,l,w,g,h),
                          bind(p,nu,binds),
                          bindPattern(p,typecheck(u,r),r))
                    case GroupByQual(p,k)
                      => val (nk,el) = translate(k,binds,r)
                         (es++el,
                          SQL(s,f,l,w,Some(nk),h),
                          bind(p,nk,binds),
                          bindPattern(p,typecheck(k,r),
                                      r.map{ case (v,tp) => (v,SeqType(tp)) }))   // lift local vars
                  }
          }
    val (nh,nl) = translate(hs,binds,nenv)
    ( nh match {
         case Tuple(ts)
           => SQL(ts,f,l,w,g,h)
         case _ => SQL(List(nh),f,l,w,g,h)
      }, el++nl )
  }

  def translate_domain ( e: Expr ): Expr
    = e match {
        case Nth(u,n)
          => Nth(translate_domain(u),n)
        case _ => e
      }

  val sql_oprs = Map( "+"->"+", "-"->"-", "*"->"*", "/"->"/", "%"->"%",
                      "&&" -> "and", "||" -> "or",
                      "=="->"=", "<"->"<", ">"->">", "<="->"<=", ">="->">=" )

  val sql_udafs = Map( "+"->"SUM", "*"->"PROD", "max"->"MAX", "min"->"MIN" )

  def translate_non_local_var ( v: String, tp: Type ): (Expr,List[Expr]) = {
    val fname = "f"+newvar
    val rf = MethodCall(MethodCall(Var("spark"),"udf",null),
                        "register",
                        List(StringConst(fname),Call("udf",List(Var(fname)))))
                       (Call(fname,Nil),
                        List(Block(List(Def(fname,Nil,tp,Var(v)),rf))))
  }

  def translate ( e: Expr, binds: Env, env: Environment ): (Expr,List[Expr])
    = e match {
        case Var(v)
          if binds.contains(v)
          => if (binds(v) == e) (e,Nil) else translate(binds(v),binds,env)
        case Var(v)
          if env.contains(v)
          => translate_non_local_var(v,env(v))
        case Var(v)
          => typecheck_var(v) match {
                case Some(tp)
                  => translate_non_local_var(v,tp)
                case _ => (e,Nil)
             }
        case IntConst(n) => (e,Nil)
        case LongConst(n) => (e,Nil)
        case BoolConst(n) => (e,Nil)
        case DoubleConst(n) => (e,Nil)
        case StringConst(n) => (e,Nil)
        case Nth(u,n)
          => val (cu,ds) = translate(u,binds,env)
             (Nth(cu,n),ds)
        case Tuple(es)
          => val (ces,ds)
                = es.foldLeft[(List[Expr],List[Expr])]((Nil,Nil)) {
                     case ((cs,ds),u)
                       => val (cu,d) = translate(u,binds,env)
                          (cs:+cu,ds++d)
                  }
             (Tuple(ces),ds)
        case Call(f,es) 
          if List("range").contains(f)
          => val (ces,ds)
                = es.foldLeft[(List[Expr],List[Expr])]((Nil,Nil)) {
                     case ((cs,ds),u)
                       => val (cu,d) = translate(u,binds,env)
                          (cs:+cu,ds++d)
                  }
             (Call(f,ces),ds)
        case MethodCall(x,"id",null)
          => (e,Nil)
        case MethodCall(x,f,List(y))
          if List("contains").contains(f)
          => val (cx,nx) = translate(x,binds,env)
             val (cy,ny) = translate(y,binds,env)
             (MethodCall(cx,f,List(cy)),nx++ny)
        case MethodCall(x,op,List(y))
          if sql_oprs.contains(op)
          => val (cx,nx) = translate(x,binds,env)
             val (cy,ny) = translate(y,binds,env)
             (MethodCall(cx,sql_oprs(op),List(cy)),nx++ny)
        case reduce(op,u)
          if sql_udafs.contains(op)
          => val (cu,ds) = translate(u,binds,env)
             (Call(sql_udafs(op),List(cu)),ds)
        case reduce(f,u)
          => val (cu,ds) = translate(u,binds,env)
             (Call(f,List(cu)),ds)
        case _
          => val fs = freevars(e,global_env.keys.toList).distinct.filter(v => env.contains(v))
             val fname = "f"+newvar
             val type_env = fs.map( v => (v,env(v)))
             val tp = typecheck(e,env)
             val args = fs.map(x => { val xc = if (binds.contains(x)) binds(x) else Var(x)
                                      env(x) match {
                                         case SeqType(_)
                                           => Call("collect_list",List(xc))
                                         case _ => xc
                                      } })
             val rf = MethodCall(MethodCall(Var("spark"),"udf",null),
                                 "register",
                                 List(StringConst(fname),Call("udf",List(Var(fname)))))

             // Spark UDFs can handle at most 10 arguments
             if (fs.length > 10) {
               val nv = newvar
               (Call(fname,List(Tuple(args))),   // put args in a tuple
                List(Block(List(Def(fname,List((nv,tuple(type_env.map(_._2)))),tp,
                                    MatchE(Var(nv),List(Case(tuple(fs.map(VarPat)),
                                                             BoolConst(true),e)))),
                                rf))))
             } else (Call(fname,args),
                     List(Block(List(Def(fname,type_env,tp,e),rf))))
                                     
      }

  def toSQL ( e: Expr ): String
    = e match {
        case Var(v) => v
        case IntConst(n) => n.toString
        case LongConst(n) => n.toString
        case BoolConst(n) => n.toString
        case DoubleConst(n) => n.toString
        case StringConst(n)
          => "\'"+n+"\'"
        case Nth(x,n)
          => toSQL(x)+"._"+n
        case Tuple(es)
          => "("+es.zipWithIndex.map{ case (u,i) => toSQL(u)+" AS _"+(i+1) }.mkString(",")+")"
        case MethodCall(x,"id",null)
          => toSQL(x)+".id"
        case MethodCall(x,"contains",es)
          => "array_contains("+toSQL(x)+","+es.map(toSQL).mkString(",")+")"
        case MethodCall(x,op,List(y))
          => "("+toSQL(x)+" "+op+" "+toSQL(y)+")"
        case Call("rangeVar",List(x))
          => "CAST ("+toSQL(x)+".id AS INT)"
        case Call(f,es)
          => f+"("+es.map(toSQL).mkString(",")+")"
        case _ => e.toString
      }

  def toSQL ( sql: SQL ): String
    = sql match {
          case SQL(ts,f,l,w,g,h)
            => val tss = ts.zipWithIndex.map{ case (t,i) => toSQL(t)+" AS _"+(i+1) }.mkString(", ")
               val fs = f.map{ case (v,Var(w)) if v==w => v
                               case (v,u) => toSQL(u)+" AS "+v }.mkString(", ")
               val ws = if (w.isEmpty) "" else " WHERE "+w.map(toSQL).mkString(" and ")
               val ls = l.map{ case (v,u) => " LATERAL VIEW EXPLODE("+toSQL(u)+") AS "+v }.mkString
               val gs = g match {
                          case Some(Tuple(es))
                            => " GROUP BY "+es.map(toSQL).mkString(", ")
                          case Some(e)
                            => " GROUP BY "+toSQL(e)
                          case _ => ""
                        }
               val hs = if (h.isEmpty) "" else " HAVING "+h.map(toSQL).mkString(" and ")
               "SELECT "+tss+" FROM "+fs+ls+ws+gs+hs
      }

  def make_sql ( sql: String ): Expr = {
    val rv = newvar
    Block((VarDecl(rv,BasicType(dataFrameClass),
                       Seq(List(MethodCall(Var("spark"),"sql",List(StringConst(sql))))))
           ::sql_tables.distinct.map(v => MethodCall(MethodCall(Var("spark"),"catalog",null),
                                                     "dropTempView",
                                                     List(StringConst(v)))))
          :+Var(rv))
  }

  def make_sql2 ( sql: String ): Expr
    = MethodCall(Var("spark"),"sql",List(StringConst(sql)))

  def translate_sql ( h: Expr, qs: List[Qualifier] ): Expr = {
    clean(h)   // clear cached types
    sql_tables = Nil
    val (se,el) = translate(h,qs,global_env)
    val sql = toSQL(se)
    Block( el:+make_sql(sql) )
  }

  def translate_sql ( h: Expr, qs: List[Qualifier], op: String ): Expr = {
    clean(h)   // clear cached types
    sql_tables = Nil
    val (SQL(ts,f,l,w,g,hv),el) = translate(h,qs,global_env)
    // total aggregation needs more work
    //val sql = toSQL(SQL(List(Call(sql_udafs(op),ts)),f,l,w,g,hv))
    val sql = toSQL(SQL(ts,f,l,w,g,hv))
    //Block( el:+make_sql(sql) )
    reduce(op,
           flatMap(Lambda(VarPat("x"),Seq(List(MethodCall(Var("x"),"getDouble",List(IntConst(0)))))),
                   MethodCall(Block( el:+make_sql(sql) ),
                              "rdd",null)))
  }

  def translate_sql ( h: Expr, qs: List[Qualifier], acc: Lambda, zero: Expr, map: Option[Lambda] ): Expr = {
    clean(h); clean(acc)   // clear cached types
    sql_tables = Nil
    val ztp = typecheck(zero,global_env)
    val (se,el) = translate(h,qs,global_env)
    val SQL(List(index,value),f,l,w,None,Nil) = se
    val rname = "f"+newvar
    val rv = newvar
    val xv = newvar
    val sv = newvar
    val update = Assign(Var(rv),Seq(List(Apply(acc,Tuple(List(Var(rv),Var(xv)))))))
    val reducer = Def(rname,List((sv,SeqType(ztp))),ztp,
                      Block(List(VarDecl(rv,ztp,Seq(List(zero))),
                                 flatMap(Lambda(VarPat(xv),Seq(List(update))),Var(sv)),
                                 Var(rv))))
    val aggr = MethodCall(MethodCall(Var("spark"),"udf",null),
                          "register",
                          List(StringConst(rname),Call("udf",List(Var(rname)))))
    map match {
       case Some(Lambda(mp,mb))
         => val mname = "f"+newvar
            val mtp = typecheck(mb,bindPattern(mp,unfold_storage_type(ztp),global_env))
            val mapper = Def(mname,List(("_x",ztp)),mtp,MatchE(Var("_x"),List(Case(mp,BoolConst(true),mb))))
            val mapr = MethodCall(MethodCall(Var("spark"),"udf",null),
                                  "register",
                                  List(StringConst(mname),Call("udf",List(Var(mname)))))
            val sql = toSQL(SQL(List(index,Call(mname,List(Call(rname,List(Call("collect_list",
                                                                                List(value))))))),
                                f,l,w,Some(index),Nil))
            Block( el:+reducer:+aggr:+mapper:+mapr:+make_sql(sql) )
       case _
         => val sql = toSQL(SQL(List(index,Call(rname,List(Call("collect_list",List(value))))),
                                f,l,w,Some(index),Nil))
            Block( el:+reducer:+aggr:+make_sql(sql) )
    }
  }

  def outerJoinSQL ( x: Expr, y: Expr, f: Lambda, tp: Type ): Expr = {
      val Lambda(TuplePat(List(VarPat(vx),VarPat(vy))),b) = f
      val fname = "f"+newvar
      sql_tables = List("X","Y")
      Block(List(MethodCall(x,"createOrReplaceTempView",List(StringConst("X"))),
                 MethodCall(y,"createOrReplaceTempView",List(StringConst("Y"))),
                 Def(fname,List((vx,tp),(vy,tp)),tp,b),
                 MethodCall(MethodCall(Var("spark"),"udf",null),
                            "register",
                            List(StringConst(fname),Call("udf",List(Var(fname))))),
                 make_sql(s"""SELECT X._1 AS _1,
                                     CASE WHEN X._2 IS NULL THEN Y._2
                                          WHEN Y._2 IS NULL THEN X._2
                                          ELSE $fname(X._2,Y._2) END AS _2
                              FROM X FULL JOIN Y ON X._1 = Y._1""")))
  }
}
