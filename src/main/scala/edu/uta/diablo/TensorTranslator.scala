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

import scala.annotation.tailrec

/* Translate in-memory tensor comprehensions to Scala code */
object TensorTranslator {
  import AST._
  import Typechecker.{tuple=>_,_}
  import ComprehensionTranslator._

  def tile_dimensions ( n: Int, e: Expr ): List[Expr]
    = if (n == 1) List(e)
      else if (n == 0) Nil
      else e match { case Tuple(es) => (1 to n).map(i => es(i-1)).toList
                     case _ => (1 to n).map(i => Nth(e,i)).toList }

  /* default translator for list comprehensions with no group-by */
  def default_translator_nogb ( h: Expr, qs: List[Qualifier], vars: List[String] ): Expr
    = qs.foldRight[(Expr,List[String])] ((Seq(List(h)),vars)) {
         case (Generator(p,u),(r,s))
           => (flatMap(Lambda(p,r),u),
               patvars(p)++s)
         case (LetBinding(p,u),(r,s))
           => (Let(p,u,r),
               patvars(p)++s)
         case (Predicate(p),(r,s))
           => (IfE(p,r,Seq(Nil)),s)
         case (AssignQual(d,u),(r,s))
           => (Block(List(Assign(d,Seq(List(u))),r)),s)
         case (VarDef(v,t,u),(r,s))
           => (Block(List(VarDecl(v,t,Seq(List(u))),r)),s)
         case (_,(r,s)) => (r,s)
      }._1

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
                 => val Comprehension(nh,nqs) = unlift_comprehensions(Comprehension(h,qs))
                    default_translator_nogb(nh,nqs,vars)
             }

  def yieldReductions ( e: Expr, vars: List[String] ): Expr
    = e match {
        case MethodCall(u@Var(v),"length",null)
          if vars.contains(v)
          => reduce("+",flatMap(Lambda(VarPat("_x"),Seq(List(IntConst(1)))),u))
        case Project(u@Var(v),"length")
          if vars.contains(v)
          => reduce("+",flatMap(Lambda(VarPat("_x"),Seq(List(IntConst(1)))),u))
        case reduce(_,_)
          => e
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

  def mcall ( m: String, x: Expr, y: Expr ): Expr
    = if (m.matches("^[a-zA-Z0-9_]*$"))
        Call(m,List(x,y))
      else MethodCall(x,m,List(y))

  /* translate a tensor comprehension with a group-by when the group-by key is equal to the head key */
  def tensor_groupby_eqkey ( tensor: String, tp: Type, dims: List[Expr],
                             head: Expr, cqs: List[Qualifier] ): Expr = {
    val Tuple(List(key,body)) = head
    val (dn,sn) = tensor_dims(tensor)
    cqs.span{ case GroupByQual(p,k) => false; case _ => true } match {
              case (qs,GroupByQual(p,k)::ts)
                => assert(toExpr(p) == key,"The group-by key must be equal to the head key")
                   val groupByVars = patvars(p)
                   // non-groupby variables used in head
                   val usedVars = freevars(head,groupByVars).intersect(comprVars(qs)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(head,ts),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   // non-groupby variables that are used in a reduction in head
                   val reducedVars = reducedTerms.map(_._1)
                   // non-groupby variables used in head as is (not reduced)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   // the type of reduced terms
                   val reducedTermTypes = (reducedTerms.map{ case (v,u) => (v,typecheck(u)) }
                                           ++rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                               .map{ case (v,u) => (v,typecheck(u)) }).toMap
                   val ndims = dn+sn
                   val vars = 1.to(ndims).map(x => newvar).toList
                   val xv = newvar    // the vector variable that contains the liftedVars values
                   val all_dims = tile_dimensions(dn,dims.head)++tile_dimensions(sn,dims(1))
                   // the map index in row-major format
                   val idx = all_dims.tail.zipWithIndex.foldLeft[Expr](Var("i1")) {
                                case (r,(e,i))
                                  => MethodCall(MethodCall(r,"*",List(e)),"+",List(Var("i"+(i+2))))
                             }
                   // the ith variable in liftedVars is computed from xv[idx].map(_.i)
                   val lvs = liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                     List(Generator(tuple(liftedVars.map(VarPat)),
                                                                    Index(Var(xv),List(idx)))))))
                   // vector values that compute all non-groupby variables in head
                   val env = reducedTerms.map{ case (v,t) => (t,Index(Var(v),List(idx))) } ++ lvs
                   // replace the reduced terms in head and ts with vector values using env
                   val Comprehension(ne,nts) = env.foldLeft(yieldReductions(Comprehension(body,ts),
                                                                            usedVars)) {
                                                   case (r,(from,to)) => subst(from,to,r)
                                               }
                   val size = all_dims.reduce[Expr]{ case (x,y) => MethodCall(x,"*",List(y)) }
                   val dsize = if (dn==0) IntConst(0)
                               else tile_dimensions(dn,dims.head).reduce[Expr] {
                                       case (x,y) => MethodCall(x,"*",List(y))
                                    }
                   val ssize = if (sn==0) IntConst(0)
                               else tile_dimensions(sn,dims(1)).reduce[Expr] {
                                       case (x,y) => MethodCall(x,"*",List(y))
                                    }
                   // all vectors used in aggregations are vectors of size d1*d2*...
                   def vector_decl ( v: String, tp: Type )
                     = VarDecl(v,ArrayType(1,tp),
                               Seq(List(Call("array_buffer_dense",List(size,zeroValue(tp))))))
                   // vector declarations; xv vector is not needed if the head is a single aggregation
                   val init = (if (liftedVars.isEmpty) Nil
                               else List(vector_decl(xv,TupleType(liftedVars.map(reducedTermTypes(_)))))) ++
                              reducedVars.map(v => vector_decl(v,reducedTermTypes(v)))
                   // append the lifted variables not reduced to xv[idx]
                   val xvincr = if (liftedVars.isEmpty) Nil
                                else List(AssignQual(Index(Var(xv),List(idx)),
                                                     MethodCall(Index(Var(xv),List(idx)),
                                                                ":+",
                                                                List(tuple(liftedVars.map(Var))))))
                   // one vector update for each reduction
                   val incr = reducedTerms.flatMap {
                                case (v,reduce(m,flatMap(Lambda(p,Seq(List(u))),x)))
                                  => List(AssignQual(Index(Var(v),List(idx)),
                                                     mcall(m,Index(Var(v),List(idx)),Apply(Lambda(p,u),x))))
                                case (v,reduce(m,x))
                                  => List(AssignQual(Index(Var(v),List(idx)),
                                                     mcall(m,Index(Var(v),List(idx)),x)))
                                case _ => Nil
                              }
                   // the traversal indices are i1, i2, ... with i1<d1, i2<d2, ...
                   val conds = all_dims.zipWithIndex.flatMap {
                                  case (d,i) => List(Predicate(MethodCall(Var("i"+(i+1)),">=",List(IntConst(0)))),
                                                     Predicate(MethodCall(Var("i"+(i+1)),"<",List(d))))
                               }
                   val nqs = qs++(LetBinding(tuple(1.to(ndims).map(i => VarPat("i"+i)).toList),k)::
                                  conds++xvincr++incr)
                   val buffer = "buffer"   // dense vector that holds the result values
                   val zero = zeroValue(tp)
                   def convert ( e: Expr ): Expr
                     = if (sn == 0)
                         e     // the result is a dense tensor
                       else if (dn == 0)
                              if (isBoolTensor(tensor))
                                Call("array2tensor_bool",List(ssize,e))
                              else Call("array2tensor",List(ssize,zero,e))
                              else if (isBoolTensor(tensor))
                                     Call("array2tensor_bool",List(dsize,ssize,e))
                              else Call("array2tensor",List(dsize,ssize,zero,e))
                   def build ( zero: Expr, array: Expr ): Expr
                     = if (sn == 0)
                         Call("array_buffer_dense",List(dsize,zero,array))
                       else if (dn == 0)
                              if (isBoolTensor(tensor))
                                Call("array_buffer_sparse_bool",List(ssize,array))
                              else Call("array_buffer_sparse",List(ssize,zero,array))
                              else if (isBoolTensor(tensor))
                                     Call("array_buffer_bool",List(dsize,ssize,array))
                              else Call("array_buffer",List(dsize,ssize,zero,array))
                   val b = ne match {
                             case Index(Var(v),_)
                               if reducedVars.contains(v) && ts.isEmpty
                               => val tp = reducedTermTypes(v)
                                  val dcl = array_assignment match {
                                                 case Some(a)   // buffer must be the assignment destination
                                                   => VarDecl(v,ArrayType(1,tp),
                                                              Seq(List(build(zeroValue(tp),a))))
                                                 case _ => vector_decl(v,tp)
                                            }
                                  Block(List(dcl,Comprehension(ignore,nqs++nts),convert(Var(v))))
                             case _
                               // when there are more qualifiers after group-by
                               // or the head value is not a simple aggregation
                               => val rs = all_dims.zipWithIndex.map {   // range over all indices
                                              case (d,i) => Generator(VarPat("i"+(i+1)),
                                                                 Range(IntConst(0),
                                                                       MethodCall(d,"-",List(IntConst(1))),
                                                                       IntConst(1)))
                                           }
                                  Block(vector_decl(buffer,tp)::init ++
                                        List(Comprehension(ignore,nqs),
                                             Comprehension(Assign(Index(Var(buffer),List(idx)),
                                                                  Seq(List(ne))),
                                                           rs++nts),
                                             convert(Var(buffer))))
                           }
                   val nb = unlift_comprehensions(b)
                   tuple(dims:+nb)
              case _ => default_translator(head,cqs,Nil)
            }
    }

  /* translate a tensor comprehension with a group-by when the group-by key is NOT equal to the head key */
  def tensor_groupby_neqkey ( tensor: String, tp: Type, dims: List[Expr],
                              head: Expr, cqs: List[Qualifier] ): Expr = {
    val Tuple(List(key,body)) = head
    val result_keys = key match { case Tuple(ks) => ks; case _ => List(key) }
    val (dn,sn) = tensor_dims(tensor)
    cqs.span{ case GroupByQual(p,k) => false; case _ => true } match {
              case (qs,GroupByQual(p,k)::ts)
                => val groupByVars = patvars(p)
                   // non-groupby variables used in head
                   val usedVars = freevars(head,groupByVars).intersect(comprVars(qs)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(head,ts),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   // non-groupby variables that are used in a reduction in head
                   val reducedVars = reducedTerms.map(_._1)
                   // non-groupby variables used in head as is (not reduced)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   // the type of reduced terms
                   val reducedTermTypes = (reducedTerms.map{ case (v,u) => (v,typecheck(u)) }
                                           ++rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                               .map{ case (v,u) => (v,typecheck(u)) }).toMap
                   val ndims = dn+sn
                   val vars = 1.to(ndims).map(x => newvar).toList
                   val xv = newvar    // the vector variable that contains the liftedVars values
                   val all_dims = tile_dimensions(dn,dims.head)++tile_dimensions(sn,dims(1))
                   // the map index in row-major format
                   val idx = all_dims.tail.zipWithIndex.foldLeft[Expr](Var("i1")) {
                                case (r,(e,i))
                                  => MethodCall(MethodCall(r,"*",List(e)),"+",List(Var("i"+(i+2))))
                             }
                   // the ith variable in liftedVars is computed from xv[idx].map(_.i)
                   val lvs = liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                     List(Generator(tuple(liftedVars.map(VarPat)),
                                                                    MapAccess(Var(xv),idx))))))
                   // vector values that compute all non-groupby variables in head
                   val env = reducedTerms.map{ case (v,t) => (t, MapAccess(Var(v),idx)) } ++ lvs
                   // replace the reduced terms in head with vector values using env
                   val Comprehension(ne,nts) = env.foldLeft(yieldReductions(Comprehension(body,ts),
                                                                            usedVars)) {
                                                   case (r,(from,to)) => subst(from,to,r)
                                               }
                   // all collections used in aggregations are Maps
                   def map_decl ( v: String, tp: Type )
                     = VarDecl(v,MapType(intType,tp),Seq(List(Call("map",Nil))))
                   // map declarations; xv vector is not needed if the head is a single aggregation
                   val init = (if (liftedVars.isEmpty) Nil
                               else List(map_decl(xv,TupleType(liftedVars.map(reducedTermTypes(_)))))) ++
                              reducedVars.map(v => map_decl(v,reducedTermTypes(v)))
                   // append the lifted variables not reduced to xv[idx]
                   val xvincr = if (liftedVars.isEmpty) Nil
                                else List(AssignQual(MapAccess(Var(xv),idx),
                                                     IfE(MethodCall(Var(xv),"contains",List(idx)),
                                                         MethodCall(MapAccess(Var(xv),idx),
                                                                    ":+",
                                                                    List(tuple(liftedVars.map(Var)))),
                                                         Seq(List(tuple(liftedVars.map(Var)))))))
                   // one vector update for each reduction
                   val incr = reducedTerms.flatMap {
                                case (v,reduce(m,flatMap(Lambda(p,Seq(List(u))),x)))
                                  => List(AssignQual(MapAccess(Var(v),idx),
                                                     IfE(MethodCall(Var(v),"contains",List(idx)),
                                                         mcall(m,MapAccess(Var(v),idx),Apply(Lambda(p,u),x)),
                                                         Apply(Lambda(p,u),x))))
                                case (v,reduce(m,x))
                                  => List(AssignQual(MapAccess(Var(v),idx),
                                                     IfE(MethodCall(Var(v),"contains",List(idx)),
                                                         mcall(m,MapAccess(Var(v),idx),x),
                                                         x)))
                                case _ => Nil
                              }
                   // the new comprehension qualifiers
                   val nqs = qs++(LetBinding(tuple(1.to(ndims).map(i => VarPat("i"+i)).toList),key)::
                                  xvincr++incr)
                   val rv = newvar
                   val rs = all_dims.zipWithIndex.map {   // range over all indices
                               case (d,i) => Generator(VarPat("i"+(i+1)),
                                                       Range(IntConst(0),
                                                             MethodCall(d,"-",List(IntConst(1))),
                                                             IntConst(1)))
                                             }
                   val conds = reducedTerms.map {
                                  case (v,t)
                                    => Predicate(MethodCall(Var(v),"contains",List(idx)))
                               }
                   val b = Block(VarDecl(rv,ArrayType(1,tp),
                                                Seq(List(Call("array",List(all_dims.reduce[Expr] {
                                                       case (x,y) => MethodCall(x,"*",List(y))
                                                     })))))::
                                        init ++ List(Comprehension(ignore,nqs),
                                                     Comprehension(Assign(Index(Var(rv),List(idx)),
                                                                          Seq(List(ne))),
                                                                   rs++conds++nts),
                                                     Var(rv)))
                   val res = if (sn == 0)
                               tuple(dims:+b)    // the result is already a dense tensor
                             else { val vv = newvar
                                    val iv = newvar
                                    val ivars = tuple(1.to(ndims).map(i => Var("i"+i)).toList)
                                    val pvars = tuple(1.to(ndims).map(i => VarPat("i"+i)).toList)
                                    val dense_dims = List(Tuple(tile_dimensions(dn,dims.head)
                                                                ++tile_dimensions(sn,dims(1))),
                                                          Tuple(Nil))
                                    // copy the dense result to a sparse tensor
                                    Block(List(VarDecl(vv,StorageType(s"tensor_${ndims}_0",List(tp),dense_dims),
                                                       Seq(List(Tuple(dense_dims:+b)))),
                                               Store(tensor,List(tp),dims,
                                                     Comprehension(Tuple(List(ivars,Var(iv))),
                                                             List(Generator(TuplePat(List(pvars,
                                                                                     VarPat(iv))),
                                                                            Lift(s"tensor_${ndims}_0",
                                                                                 Var(vv))))))))
                                  }
                   res
              case _ => default_translator(head,cqs,Nil)
            }
    }
}
