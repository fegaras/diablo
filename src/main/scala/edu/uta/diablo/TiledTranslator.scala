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

import scala.util.matching.Regex

/* Translate distributed tensor comprehensions to RDD comprehensions */
object TiledTranslator {
  import AST._
  import Typechecker.{tuple=>_,_}
  import TensorTranslator._
  import RDDTranslator._
  import SQLGenerator.{translate_sql,outerJoinSQL}
  import Lifting.{store,lift,getTypeMap}
  import ComprehensionTranslator._

  /* Is this generator domain a Tiled RDD? Generator domains have been lifted by the Lifter */
  def isTiled ( e: Expr ): Boolean
    = e match {
        case Lift(name,_) if isBlockTensor(name) => true
        case _ => false
      }

  def is_tiled_comprehension ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case Generator(p,u) => isTiled(u); case _ => false }

  def hasGroupBy ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case GroupByQual(_,_) => true; case _ => false }

  def hasGroupByKey ( qs: List[Qualifier], key: Expr ): Boolean
    = qs.exists{ case GroupByQual(p,_) => key == toExpr(p); case _ => false }

  // tiled values are normaly (indices,value), but can be ((indices,value),(indices,value)) etc
  // if they are the results of a join
  def tile_indices ( p: Pattern ): List[String]
    = p match {
        case TuplePat(List(VarPat(i),VarPat(_)))
          => List(i)
        case TuplePat(List(TuplePat(ps),VarPat(_)))
          if ps.forall(_.isInstanceOf[VarPat])
          => ps.flatMap{ case VarPat(i) => List(i); case _ => Nil }
        case TuplePat(ps)
          => ps.flatMap(tile_indices)
        case _ => Nil
      }

  def tile_indices ( qs: List[Qualifier] ): List[String]
    = qs.flatMap{ case Generator(p,u) if isTiled(u) => tile_indices(p); case _ => Nil }

  def tile_values ( p: Pattern ): List[String]
    = p match {
        case TuplePat(List(VarPat(_),VarPat(v)))
          => List(v)
        case TuplePat(List(TuplePat(ps),VarPat(v)))
          if ps.forall(_.isInstanceOf[VarPat])
          => List(v)
        case TuplePat(ps)
          => ps.flatMap(tile_values)
        case _ => Nil
      }

  def tile_values ( qs: List[Qualifier] ): List[String]
    = qs.flatMap{ case Generator(p,u) if isTiled(u) => tile_values(p); case _ => Nil }

  def tile_type ( block: String ): String
    = block match {
        case block_tensor_pat(full,_,dn,sn)
          => s"${full}tensor_${dn}_$sn"
        case block_bool_tensor_pat(full,_,dn,sn)
          => s"${full}bool_tensor_${dn}_$sn"
      }

  def tile_type ( block: String, tp: Type ): String = {
    val isBool = tp == boolType
    block match {
        case block_tensor_pat(full,_,dn,sn)
          => if (isBool && sn.toInt > 0)
               s"${full}bool_tensor_${dn}_$sn"
             else s"${full}tensor_${dn}_$sn"
        case block_bool_tensor_pat(full,_,dn,sn)
          => if (isBool && sn.toInt > 0)
               s"${full}bool_tensor_${dn}_$sn"
             else s"${full}tensor_${dn}_$sn"
      }
  }

  def tileType ( block: String, tp: Type ): Type = {
     val Some(x@TypeMapS(_,tvs,args,_,st,_,_,_)) = Lifting.getTypeMap(tile_type(block,tp))
     def coordType ( tp: Type ): List[Type]
       = tp match { case TupleType(l) => l; case _ => List(tp) }
     TupleType(List(TupleType(args.flatMap(x => coordType(x._2)).toList),
                    substType(st,Some(tvs.map(tv => tv -> tp).toMap))))
  }


/*----------------------- Tiled comprehension without groupBy that preserves tiling -------------------
 * tensor*(...)[ ((i,j,...),e) | ... ]
 * Requirements:
 * 1) no group-by
 * 2) comprehension indices (i,j,...) are vars
 * 3) i,j,... are unique (indices from tensor*, tensor, and range)
 * ----------------------------------------------------------------------------------------------------*/

  def correlated_indices ( qs: List[Qualifier], indices: Set[String] ): Set[String]
    = qs.foldLeft(indices) {
        case (ks,Predicate(MethodCall(Var(i),"==",List(Var(j)))))
          => if (ks.contains(i))
               ks+j
             else if (ks.contains(j))
                    ks+i
             else ks
        case (ks,_) => ks
      }

  def unique_expr ( e: Expr, indices: List[String] ): Boolean
    = e match {
        case MethodCall(x,op,List(y))
          => List("*","+","-").contains(op) &&
                ((unique_expr(x,indices) && constant_int(y))
                  || (unique_expr(y,indices) && constant_int(x)))
        case Var(i)
          => indices.contains(i)
        case _ => false
      }

  def unique_indices ( qs: List[Qualifier] ): List[String]
    = qs.foldLeft(Nil:List[String]) {
        case (r,Generator(TuplePat(List(k,_)),u))
          if isTiled(u)
          => patvars(k)++r
        case (r,Generator(TuplePat(List(k,_)),u))
          if isTensor(u)
          => patvars(k)++r
        case (r,Generator(VarPat(i),Range(_,_,_)))
          => i::r
        case (r,LetBinding(VarPat(i),u))
          if unique_expr(u,r)
          => i::r
        case (r,_) => r
      }

  def constant_int ( e: Expr ): Boolean
    = e match {
        case IntConst(_) => true
        case LongConst(_) => true
        case MethodCall(x,op,List(y))
          => List("*","+","%","/").contains(op) &&
                constant_int(x) && constant_int(y)
        case _ => false
      }

  def constant_index ( e: Expr ): Boolean
    = e match {
        case Var(_) => true
        case Tuple(s) => s.forall(constant_index)
        case _ => constant_int(e)
      }

  def preserves_tiling ( key: Expr, qs: List[Qualifier] ): Boolean
    = !hasGroupBy(qs) && constant_index(key) && {
         var key_vars = freevars(key).toSet
         val indices = unique_indices(qs).toSet
         val cis = correlated_indices(qs,key_vars)
         key_vars.forall(indices.contains) && indices == cis
      }

  def local_expr ( e: Expr, vars: List[String] ): Boolean
    = !freevars(e, vars).exists(v => typecheck_var(v).isEmpty)

  def rdd_qualifier_vars ( qs: List[Qualifier], vars: List[String] ): List[String]
    = qs.foldLeft[List[String]] (vars) {
          case (s,Generator(TuplePat(List(p,VarPat(v))),Lift(m,_)))
            if isTensor(m) || isBlockTensor(m)
            => s++patvars(p):+v
          case (s,Generator(p,Lift("rdd",_)))
            => s++patvars(p)
          case (s,Generator(p,Lift("dataset",_)))
            => s++patvars(p)
          case (s,Generator(VarPat(i),Range(_,_,_)))
            => s:+i
          case (s,LetBinding(p,e))
            if local_expr(e,s)
            => s++patvars(p)
          case (s,_) => s
      }

  def prefix ( prefix: String, v: String ): String = "_"+prefix+"_"+v

  val block_pat: Regex = """(full_|)(dataset|rdd)_block_(bool_|)tensor_(\d+)_(\d+)""".r

  // the last tile size is dim % block_dim_size
  def tile_sizes ( vars: List[String], dims: List[Expr], dn: Int, sn: Int,
                   shuffle: Boolean = false ): List[Qualifier] = {
    val ds = tile_dimensions(dn,dims.head)++tile_dimensions(sn,dims(1))
    (vars zip ds).map {
          case (i,d)
            => LetBinding(VarPat(prefix("size",i)),
                          IfE(MethodCall(MethodCall(MethodCall(Var(if (shuffle) i
                                                                   else prefix("coord",i)),
                                                               "+",List(IntConst(1))),
                                                    "*",List(IntConst(block_dim_size))),
                                         ">",List(d)),
                              MethodCall(d,"%",List(IntConst(block_dim_size))),
                              IntConst(block_dim_size)))
    }
  }

  // from the comprehension qualifiers qs, generate the RDD qualifiers
  def rdd_qualifiers ( qs: List[Qualifier], vars: List[String], shuffle: Boolean = false ): List[Qualifier] = {
    val local_vars = rdd_qualifier_vars(qs,vars).toSet
    val unique_is = unique_indices(qs)
    val cp = """_coord_(\S+)""".r
    val tp = """_tile_(\S+)""".r
    def tile_index ( e: Expr ): String
      = e match {
          case MethodCall(MethodCall(Var(cp(cv)),"*",_),
                          "+",List(Var(tp(tv))))
            if cv == tv
            => cv
          case _ => ""
        }
    qs.flatMap (
        q => q match {
          case Generator(TuplePat(List(p,pv)),
                         Lift(block_pat(full,cm,bool,dn,sn),e))
            => val is = patvars(p)
               val v = patvars(pv).mkString("_")
               Generator(tuple(List(tuple(is.map(i => VarPat(prefix("coord",i)))),
                                    VarPat(prefix("tile",v)))),
                         Lift(cm,Nth(e,3)))::
                  (if (shuffle)   // will contain all needed tiles after group-by
                     List(LetBinding(VarPat(prefix("tiles",v)),
                                     tuple(List(tuple(is.map(i => Var(prefix("coord",i)))),
                                                Var(prefix("tile",v))))))
                   else Nil)
          case Generator(_,Lift("rdd",_))
            => List(q)
          case Generator(_,Lift("dataset",_))
            => List(q)
          case Generator(VarPat(i),Range(n1,n2,n3))
            => List(Generator(VarPat(prefix("coord",i)),
                              Range(MethodCall(n1,"/",List(IntConst(block_dim_size))),
                                    MethodCall(n2,"/",List(IntConst(block_dim_size))),
                                    n3)))
          case Generator(TuplePat(List(p,pv)),Lift(tensor,e))
            if isTensor(tensor)
            => val (dn,sn) = tensor_dims(tensor)
               val vdims = (if (dn==1) List(Nth(e,1))
                            else (1.to(dn)).map( i => Nth(Nth(e,1),i))).toList ++
                           (if (sn==1) List(Nth(e,2))
                            else (1.to(sn)).map( i => Nth(Nth(e,2),i))).toList
               (patvars(p) zip vdims).
                   map { case (v,dim)
                           => Generator(VarPat(prefix("coord",v)),
                                        Range(IntConst(0),
                                              MethodCall(MethodCall(dim,
                                                                    "-",List(IntConst(1))),
                                                         "/",List(IntConst(block_dim_size))),
                                              IntConst(1))) }
          case LetBinding(p,e)
            if freevars(e).toSet.intersect(local_vars).isEmpty
            => List(q)
          case Predicate(MethodCall(Var(i),"==",List(Var(j))))
            if unique_is.contains(i) && unique_is.contains(j)
            => List(Predicate(MethodCall(Var(prefix("coord",i)),
                                         "==",List(Var(prefix("coord",j))))))
          case Predicate(MethodCall(Var(i),"==",List(e)))
            if unique_is.contains(i) && freevars(e).toSet.subsetOf(local_vars)
               && freevars(e).intersect(unique_is).isEmpty
            => List(Predicate(MethodCall(Var(prefix("coord",i)),
                         "==",List(MethodCall(e,"/",List(IntConst(block_dim_size)))))))
          case Predicate(MethodCall(e,"==",List(Var(i))))
            if unique_is.contains(i) && freevars(e).toSet.subsetOf(local_vars)
               && freevars(e).intersect(unique_is).isEmpty
            => List(Predicate(MethodCall(Var(prefix("coord",i)),
                          "==",List(MethodCall(e,"/",List(IntConst(block_dim_size)))))))
          case Predicate(MethodCall(Var(i),"==",List(e)))
            if unique_is.contains(i) && tile_index(e) != ""
            => List(Predicate(MethodCall(Var(prefix("coord",i)),
                                         "==",List(Var(prefix("coord",tile_index(e)))))))
          case Predicate(MethodCall(e,"==",List(Var(j))))
            if unique_is.contains(j) && tile_index(e) != ""
            => List(Predicate(MethodCall(Var(prefix("coord",tile_index(e))),
                                         "==",List(Var(prefix("coord",j))))))
          case _ => Nil
      })
  }

  def tile_vars ( qs: List[Qualifier], vars: List[String] ): List[String]
    = qs.foldLeft[List[String]] (vars) {
          case (s,Generator(TuplePat(List(p,pv)),Lift(m,_)))
            if isTensor(m) || isBlockTensor(m)
            => s++patvars(p)++patvars(pv)
          case (s,Generator(VarPat(i),Range(_,_,_)))
            => s:+i
          case (s,LetBinding(p,e))
            if local_expr(e,s)
            => s++patvars(p)
          case (s,_) => s
      }

  def block_tile_vars ( qs: List[Qualifier] ): List[String]
    = qs.foldLeft[List[String]] (Nil) {
          case (s,Generator(TuplePat(List(p,pv)),Lift(m,_)))
            if isBlockTensor(m)
            => s++patvars(p)++patvars(pv)
          case (s,Generator(VarPat(i),Range(_,_,_)))
            => s:+i
          case (s,_) => s
      }

  // from the comprehension qualifiers qs, generate the tile qualifiers
  def tile_qualifiers ( qs: List[Qualifier], vars: List[String], shuffle: Boolean = false ): List[Qualifier] = {
    val local_vars = tile_vars(qs,vars)
    val block_vars = block_tile_vars(qs)
    qs.flatMap (
        q => q match {
          case Generator(p,Lift("rdd",_))
            => Nil   // goes into the rdd_qualifiers
          case Generator(p,Lift("dataset",_))
            => Nil   // goes into the rdd_qualifiers
          case Generator(TuplePat(List(p,pv)),Lift(block,_))
            if isBlockTensor(block)
            => val is = patvars(p)
               val v = patvars(pv).mkString("_")
               val lbinds = is.zipWithIndex.map {
                                 case (i,k)
                                   => LetBinding(VarPat(i),
                                                 MethodCall(MethodCall(Var(prefix("coord",i)),
                                                                       "*",List(IntConst(block_dim_size))),
                                                            "+",List(Var(prefix("tile",i)))))
                            }
               (if (shuffle)
                  List(Generator(tuple(List(tuple(is.map(i => VarPat(prefix("coord",i)))),
                                            VarPat(prefix("tile",v)))),
                                 Var(prefix("tiles",v))))
                else Nil)++
               (Generator(tuple(List(tuple(is.map(i => VarPat(prefix("tile",i)))),pv)),
                          Lift(tile_type(block),Var(prefix("tile",v))))::lbinds)
          case Generator(VarPat(i),Range(n1,n2,n3))
            => List(Generator(VarPat(prefix("tile",i)),
                              Range(IntConst(0),
                                    MethodCall(Var(prefix("size",i)),
                                               "-",List(IntConst(1))),
                                    IntConst(1))),
                    LetBinding(VarPat(i),
                               MethodCall(MethodCall(Var(prefix("coord",i)),
                                                     "*",List(IntConst(block_dim_size))),
                                          "+",List(Var(prefix("tile",i))))))
          case Generator(TuplePat(List(p,pv)),Lift(tensor,e))
            if isTensor(tensor)
            => Generator(TuplePat(List(p,pv)),Lift(tensor,e))::
                    patvars(p).map( i => Predicate(MethodCall(Var(prefix("coord",i)),"==",
                                                List(MethodCall(Var(i),
                                                        "/",List(IntConst(block_dim_size)))))) )
          case Generator(_,u)
            if !isRDD(u)
            => List(q)
          case LetBinding(p,e)
            if local_expr(e,local_vars)
            => List(q)
          case Predicate(e)
            if local_expr(e,local_vars)
            => List(q)
          case _ => Nil
      })
  }

  def preserve_tiles ( block: String, hs: Expr, qs: List[Qualifier],
                       vars: List[String], tp: Type, dims: List[Expr] ): Expr
    = hs match {
        case Tuple(List(k,e))
          => val is = freevars(k)
             val is_array_assign = block_array_assignment.nonEmpty
             val tensor = tile_type(block,tp)
             val (dn,sn) = tensor_dims(tensor)
             val tbinds = tile_sizes(is,dims,dn,sn)
             val vdims = is.map( v => Var(prefix("size",v)) )
             val tile_dims = List(tuple(vdims.take(dn)),tuple(vdims.takeRight(sn)))
             val tile_coords = is.map( i => Var(prefix("coord",i)) )
             val tile_indices = tuple(is.map{ i => MethodCall(Var(i),"%",
                                                     List(IntConst(block_dim_size))) })
             val tc = Comprehension(Tuple(List(tile_indices,e)),
                                    tile_qualifiers(qs,vars))
             val tile = Store(tensor,List(tp),tile_dims,tc)
             if (isDatasetTensor(block)) {
               val Comprehension(nhs,nqs)
                     = optimize(Comprehension(Tuple(List(tuple(tile_coords),tile)),
                                              rdd_qualifiers(qs,vars)++tbinds))
               if (trace) println("Comprehension that preserves tilling:\n"
                                  +Pretty.print(Comprehension(nhs,nqs)))
               val sql = translate_sql(nhs,nqs)
               val ds = block_array_assignment match {
                           case Some(array)
                             => val Some(TypeMapS(_,tvs,_,_,st,_,_,_)) = getTypeMap(tile_type(block,tp))
                                val stp = substType(st,Some(tvs.map(_->tp).toMap))
                                val dest = Nth(array,3)
                                val f = Lambda(TuplePat(List(VarPat("_x"),VarPat("_y"))),Var("_y"))
                                outerJoinSQL(dest,sql,f,stp)
                           case _ => sql
                        }
               store("dataset",List(tileType(block,tp)),dims,ds)
             } else if (is_rdd_comprehension(qs) || is_array_assign) {
               val mtile = if (is_array_assign)
                             add_initial_array(tile,Nth(Var("_array"),3))
                           else tile
               val assigns = block_array_assignment match {
                                case Some(array)
                                  => val array_coords = tuple(is.map( i => VarPat(prefix("array",i)) ))
                                     Generator(TuplePat(List(array_coords,VarPat("_array"))),
                                               Lift("rdd",Nth(array,3)))::
                                     is.map { i => Predicate(MethodCall(Var(prefix("array",i)),
                                                                  "==",List(Var(prefix("coord",i))))) }
                                case _ => Nil
                             }
               val res = optimize(Comprehension(Tuple(List(tuple(tile_coords),mtile)),
                                                rdd_qualifiers(qs,vars)++assigns++tbinds))
               if (trace) println("Comprehension that preserves tilling:\n"
                                  +Pretty.print(res))
               val rtp = elemType(typecheck(res))
               tuple(dims:+Store("rdd",List(rtp),Nil,res))
             } else {
               val p = tuple(is.map( i => VarPat(prefix("coord",i)) )
                             ++ is.map( i => VarPat(prefix("size",i)) ))
               val nc = Comprehension(toExpr(p),
                                      rdd_qualifiers(qs,vars)++tbinds)
               if (trace) println("Parallelizing the in-memory comprehension:\n"
                                  +Pretty.print(nc))
               val rdd = flatMap(Lambda(p,Seq(List(tuple(List(tuple(tile_coords),tile))))),
                                 MethodCall(Var("spark_context"),
                                            "parallelize",
                                            List(nc,IntConst(number_of_partitions))))
               tuple(dims:+rdd)
             }
      }


/*-------------- Tiled comprehension without groupBy that does not preserve tiling -------------------------*/

  def shuffles_tiles ( key: Expr, qs: List[Qualifier] ): Boolean
    = !hasGroupBy(qs) && {
         var key_vars = freevars(key).filter(v => typecheck_var(v).isEmpty).toSet
         val indices = unique_indices(qs).toSet
         val cis = correlated_indices(qs,key_vars)
         key_vars.forall(indices.contains) //&& indices == cis
      }

  /* shuffle the tiles of a tiled comprehension */
  def shuffle_tiles ( block: String, hs: Expr, qs: List[Qualifier],
                      vars: List[String], tp: Type, dims: List[Expr] ): Expr
    = hs match {
        case Tuple(List(p,h))
          => val ks = p match { case Tuple(ks) => ks; case _ => List(p) }
             val vs = ks.map{ _ => newvar }
             val fs = tile_indices(qs)
             val N = IntConst(block_dim_size)
             val tensor = tile_type(block,tp)
             val (dn,sn) = tensor_dims(tensor)
             val tbinds = tile_sizes(vs,dims,dn,sn,true)
             val vdims = vs.map( v => Var(prefix("size",v)) )
             val tile_dims = List(tuple(vdims.take(dn)),tuple(vdims.takeRight(sn)))
             def gkeys ( op: String ): List[Expr]
               = (ks zip vs).map {
                      case (k,vk)
                        => val is = freevars(k,Nil).intersect(fs)
                           val gk = is.map{ v => (v,MethodCall(MethodCall(Var(prefix("coord",v)),
                                                                          "*",List(N)),
                                                               "+",List(Var(prefix("tile",v))))) }
                           MethodCall(gk.foldLeft[Expr](k){ case (r,(v,e)) => subst(v,e,r) },
                                      op,List(N))
                      }
             val all_dims = tile_dimensions(dn,dims.head)++tile_dimensions(sn,dims(1))
             // generate all the unique block coordinates from the current block coordinates
             //   used by the comprehension keys
             val unique_coords
                 = (ks zip vs zip all_dims zip gkeys("/")).flatMap {
                            case (((Var(v),vk),_),_)
                              => List(LetBinding(VarPat(vk),Var(prefix("coord",v))))
                            case (((k,vk),_),gkey)
                              => val is = freevars(k,Nil).intersect(fs)
                                 val ts = tuple(is.map{ v => VarPat(prefix("tile",v)) })
                                 List(Generator(VarPat(vk),
                                           Call("unique_values",
                                                List(Lambda(ts,gkey)))))
                         }
             val rqs = (rdd_qualifiers(qs,vars,true)++unique_coords:+
                               GroupByQual(tuple(vs.map(VarPat)),
                                           tuple(vs.map(Var))))++tbinds
             val tqs = (vs zip gkeys("/")).map {
                           case (vk,gkey)
                             => Predicate(MethodCall(Var(vk),"==",List(gkey)))
                       }
             val tile = Store(tile_type(block,tp),List(tp),tile_dims,
                              Comprehension(Tuple(List(Tuple(gkeys("%")),h)),
                                            tile_qualifiers(qs,vars,true)++tqs))
             if (trace) println("Comprehension that does not preserve tilling:\n"
                                +Pretty.print(Comprehension(Tuple(List(tuple(vs.map(Var)),tile)),rqs)))
             val res = optimize(Comprehension(Tuple(List(tuple(vs.map(Var)),tile)),rqs))
             val rtp = elemType(typecheck(res))
             val rdd = if (is_rdd_comprehension(qs))
                         Store("rdd",List(rtp),Nil,res)
                       else MethodCall(Var("spark_context"),
                                       "parallelize",
                                       List(Store("rdd",List(rtp),Nil,res),
                                            IntConst(number_of_partitions)))
             if (isDatasetTensor(block))
               store("dataset",List(tileType(block,tp)),dims,rdd)
             else tuple(dims:+rdd)
    }


/* -------------------- a group-by on block tensors -----------------------------------------*/

  def hasGroupByTiling ( qs: List[Qualifier], key: Expr ): Boolean
    = qs.exists {
        case GroupByQual(kp,e)
          => key == toExpr(kp) &&
             freevars(e).toSet.subsetOf(unique_indices(qs).toSet)
        case _ => false
      }

  def groupBy_tiles ( block: String, hs: Expr, qs: List[Qualifier],
                      vars: List[String], tp: Type, dims: List[Expr] ): Expr
    = hs match {
        case Tuple(List(kp,head))
          => qs.span{ case GroupByQual(gp,_) => toExpr(gp) != kp; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val tensor = tile_type(block,tp)
                   val (dn,sn) = tensor_dims(tensor)
                   val ndims = dn+sn
                   val groupByVars = p match {
                                       case VarPat(_) if ndims > 1
                                         => freevars(k)
                                       case _ => patvars(p) }
                   // non-groupby variables used in head
                   val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val h = yieldReductions(head,usedVars)
                   val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val ms = rt.map{ case (_,reduce(m,_)) => m
                                    case (_,_) => "++"
                                  }
                   val msTypes = rt.map{ case (v,u) => typecheck(u) }
                   def nvar ( s: String ) = tuple(1.to(ndims).map(i => Var(s+i)).toList)
                   def nvarp ( s: String ) = tuple(1.to(ndims).map(i => VarPat(s+i)).toList)
                   def combine ( x: String, y: String, m: String, tp: Type ): Expr = {
                     val zero = zeroValue(tp)
                     val mst = Call("merge_tensors",
                                    List(Nth(Var(x),3),Nth(Var(y),3),
                                         Lambda(TuplePat(List(VarPat("v"),VarPat("w"))),
                                                mcall(m,Var("v"),Var("w"))),
                                         zero))
                     Tuple(List(Nth(Var(x),1),Nth(Var(x),2),mst))
                   }
                   val md = h match {
                              case reduce(_,_)
                                => Lambda(TuplePat(List(VarPat("_x"),VarPat("_y"))),
                                          combine("_x","_y",ms.head,msTypes.head))
                              case _
                                => { val xs = rt.map(_ => newvar)
                                     val ys = rt.map(_ => newvar)
                                     Lambda(TuplePat(List(tuple(xs.map(VarPat)),
                                                          tuple(ys.map(VarPat)))),
                                            Tuple((ms zip msTypes zip (xs zip ys))
                                                      .map{ case ((m,tp),(x,y))
                                                              => combine(x,y,m,tp) } ))
                                   }
                            }
                   val tbinds = tile_sizes(groupByVars,dims,dn,sn)
                   val rqs = rdd_qualifiers(qs,vars)
                   val vdims = groupByVars.map( v => Var(prefix("size",v)) )
                   val tile_dims = List(tuple(vdims.take(dn)),tuple(vdims.takeRight(sn)))
                   val tile_keys = tuple(groupByVars.map( v => VarPat(prefix("tile",v)) ))
                   val tindices = tile_indices(qs).map( i => (i,Var(prefix("tile",i))) )
                   val tgb_key = tindices.foldLeft(k) { case (r,(from,to)) => subst(from,to,r) }
                   val tiles = (rt zip msTypes).map {
                                 case ((_,u),tp)
                                   => (Store(tile_type(block,tp),List(tp),tile_dims,
                                             Comprehension(Tuple(List(toExpr(tile_keys),u)),
                                                   (tile_qualifiers(r,vars)
                                                    :+GroupByQual(tile_keys,tgb_key))++s)))
                               }
                   val tile_coords = tuple(groupByVars.map( v => VarPat(prefix("coord",v)) ))
                   val coord_indices = tile_indices(qs).map( i => (i,Var(prefix("coord",i))) )
                   val coord_gb_key = coord_indices.foldLeft(k) { case (r,(from,to)) => subst(from,to,r) }
                   val nc = Comprehension(Tuple(List(toExpr(tile_coords),tuple(tiles))),
                                          (rqs:+LetBinding(tile_coords,coord_gb_key))++tbinds)
                   val env = rt.map{ case (n,e) => (e,newvar) }
                   def liftExpr ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => subst(from,Var(to+"_"),r) }
                   val liftedTile
                     = liftExpr(h) match {
                         case Var(v)
                           => Var(v.dropRight(1))
                         case nh
                         => val first_aggr = Var(env.head._2)
                            val vdims = (if (dn==1) List(Nth(first_aggr,1))
                                         else (1.to(dn)).map( i => Nth(Nth(first_aggr,1),i))).toList ++
                                        (if (sn==1) List(Nth(first_aggr,2))
                                         else (1.to(sn)).map( i => Nth(Nth(first_aggr,2),i))).toList
                            val tile_dims = List(tuple(vdims.take(dn)),tuple(vdims.takeRight(sn)))
                            Store(tensor,List(tp),tile_dims,
                                  Comprehension(Tuple(List(nvar("i0_"),nh)),
                               env.map(_._2).zip(msTypes).zipWithIndex.flatMap {
                                  case ((v,tp),i)
                                    => val tensor =  tile_type(block,tp)
                                       Generator(TuplePat(List(nvarp("i"+i+"_"),
                                                               VarPat(v+"_"))),
                                                 Lift(tensor,Var(v)))::
                                       (if (i > 0)
                                          1.to(ndims).map(j => Predicate(MethodCall(Var("i"+i+"_"+j),
                                                                   "==",List(Var("i0_"+j))))).toList
                                        else Nil)
                               }))
                       }
                   if (isDatasetTensor(block)) {
                       val N = IntConst(block_dim_size)
                       val sdims = List(Tuple(1.to(dn).map( i => N ).toList),
                                        Tuple(1.to(sn).map( i => N ).toList))
                       // empty tile:
                       val zero = tuple(msTypes.map(tp => Store(tile_type(block,tp),
                                                                List(tp),sdims,Seq(Nil))))
                       val rval = tuple(env.map(x => VarPat(x._2)))
                       val mapper = if (liftedTile != toExpr(rval))
                                      Some(Lambda(rval,liftedTile))
                                    else None
                       if (trace) println("Comprehension without group-by:\n"
                                          +Pretty.print(Comprehension(Tuple(List(toExpr(tile_coords),tuple(tiles))),
                                                             (rqs:+LetBinding(tile_coords,coord_gb_key))++tbinds))
                                          +"\nAccumulator:\n"+Pretty.print(md)
                                          +"\nMapper:\n"+Pretty.print(mapper))
                       // translate it to DataFrames SQL
                       val sql = translate_sql(Tuple(List(toExpr(tile_coords),tuple(tiles))),
                                               (rqs:+LetBinding(tile_coords,coord_gb_key))++tbinds,
                                               md,zero,mapper)
                       val Some(TypeMapS(_,tvs,_,_,st,_,_,_)) = getTypeMap(tile_type(block,tp))
                       val stp = substType(st,Some(tvs.map(_->tp).toMap))
                       val ds = block_array_assignment match {
                                   case Some(array)
                                     => val dest = Nth(array,3)
                                        outerJoinSQL(dest,sql,md,stp)
                                   case _ => sql
                                 }
                       store("dataset",List(tileType(block,tp)),dims,ds)
                   } else {
                       val rtp = elemType(typecheck(nc))
                       val rbknc = MethodCall(Store("rdd",List(rtp),Nil,nc),
                                              "reduceByKey",
                                              List(md,IntConst(number_of_partitions)))
                       val all_dims = tile_dimensions(dn,dims.head)++tile_dimensions(sn,dims(1))
                       // check for groupBy join
                       val rbk = group_by_join(rbknc,toExpr(tile_coords),all_dims) match {
                                   case Some(ne) => ne
                                   case _ => rbknc
                                 }
                       val rdd = block_array_assignment match {
                                   case Some(array)
                                     => val dest = Nth(array,3)
                                        Call("outerJoin",List(dest,rbk,md))
                                   case _ => rbk
                                 }
                       val rval = tuple(env.map(x => VarPat(x._2)))
                       val pvars = patvars(p).map(Var)
                       val tdims = List(tuple(pvars.take(dn)),tuple(pvars.takeRight(sn)))
                       if (trace) println("Comprehension without group-by:\n"
                                          +Pretty.print(Comprehension(Tuple(List(toExpr(p),liftedTile)),
                                                     List(Generator(TuplePat(List(p,rval)),
                                                                    Lift("rdd",rdd))))))
                       val gnc = Comprehension(Tuple(List(toExpr(p),liftedTile)),
                                               List(Generator(TuplePat(List(p,rval)),
                                                              Lift("rdd",rdd))))
                       val gtp = elemType(typecheck(gnc))
                       val res = Store("rdd",List(gtp),Nil,gnc)
                       Tuple(dims:+res)
                   }
            case _ => throw new Error("Expected a group-by comprehension: "
                                      +Comprehension(hs,qs))
          }
    }


/* -------------------- GroupBy Join using the SUMMA algorithm -----------------------------------------*/

  // convert a join followed by groupBy to an optimal groupBy-join (SUMMA algorithm)
  def group_by_join ( e: Expr, gbkey: Expr, dims: List[Expr] ): Option[Expr] = {
    def depends ( e: Expr, p: Pattern ): Boolean = freevars(e).toSet.subsetOf(patvars(p).toSet)
    (e,gbkey) match {
      case (MethodCall(flatMap(Lambda(TuplePat(List(_,pg)),IfE(_,prod,_)),
                               MethodCall(flatMap(Lambda(px,Seq(List(Tuple(List(jx,bx))))),
                                                  x),
                                          "join",List(flatMap(Lambda(py,Seq(List(Tuple(List(jy,by))))),
                                                              y),
                                                      partitions))),
                       "reduceByKey",List(Lambda(pa,plus),_)),
            Tuple(List(gx,gy)))
        if groupByJoin && (depends(gx,px) && depends(gy,py) || (depends(gy,px) && depends(gx,py)))
        => val (gtx,gty) = if (depends(gx,px)) (gx,gy) else (gy,gx)
           val left_rows = dims.head
           val right_cols = dims(1)
           // grid dimension so that each grid cell is handled by one Spark executor
           val grid_dim = Math.sqrt(number_of_partitions).toInt
           // each grid cell contains grid_blocks*grid_blocks tensors
           val left_blocks = MethodCall(Var("Math"),"max",
                                List(IntConst(1),
                                     MethodCall(MethodCall(Var("Math"),"ceil",
                                        List(MethodCall(left_rows,"/",
                                                List(DoubleConst(block_dim_size*grid_dim*1.0))))),
                                                "toInt",null)))
           val right_blocks = MethodCall(Var("Math"),"max",
                                List(IntConst(1),
                                     MethodCall(MethodCall(Var("Math"),"ceil",
                                        List(MethodCall(right_cols,"/",
                                                List(DoubleConst(block_dim_size*grid_dim*1.0))))),
                                                "toInt",null)))
           val kv = newvar
           // replicate each tensor grid_dim times (sent to different grid cells)
           val left = flatMap(Lambda(px,flatMap(Lambda(VarPat(kv),
                                           Seq(List(Tuple(List(Tuple(List(Var(kv),
                                                                          MethodCall(gtx,"%",List(IntConst(grid_dim))))),
                                                               Tuple(List(Tuple(List(jx,gtx)),bx))))))),
                                                Range(IntConst(0),IntConst(grid_dim-1),IntConst(1)))),
                              x)
           val right = flatMap(Lambda(py,flatMap(Lambda(VarPat(kv),
                                            Seq(List(Tuple(List(Tuple(List(MethodCall(gty,"%",List(IntConst(grid_dim))),
                                                                           Var(kv))),
                                                                Tuple(List(Tuple(List(jy,gty)),by))))))),
                                                 Range(IntConst(0),IntConst(grid_dim-1),IntConst(1)))),
                               y)
           Some(flatMap(Lambda(TuplePat(List(TuplePat(List(VarPat("_cell_i"),VarPat("_cell_j"))),
                                             TuplePat(List(VarPat("as"),VarPat("bs"))))),
                               Call("groupByJoin_mapper",
                                    List(Var("as"),Var("bs"),left_blocks,
                                         Lambda(pg,prod),Lambda(pa,plus)))),
                        MethodCall(left,"cogroup",List(right,IntConst(grid_dim*grid_dim)))))
                        //MethodCall(left,"cogroup",List(right,partitions))))
      case _ => None
    }
  }


/* -------------------- translate distributed tensor comprehensions -------------------------------------*/

  def translate_tiled_compr ( block: String, hs: Expr, qs: List[Qualifier],
                              vars: List[String], tp: Type, dims: List[Expr] ): Expr
    = hs match {
      case Tuple(List(p,h))   // a tiled comprehension that preserves tiling
        if preserves_tiling(p,qs)
        => preserve_tiles(block,hs,qs,vars,tp,dims)
      case Tuple(List(p,_))   // a tiled comprehension that doesn't preserve tiling
        if shuffles_tiles(p,qs)
        => shuffle_tiles(block,hs,qs,vars,tp,dims)
      case Tuple(List(kp,_))   // group-by tiled comprehension with group-by-key == comprehension key
                               //  and this key is from tensor indices
        if hasGroupByTiling(qs,kp)
        => groupBy_tiles(block,hs,qs,vars,tp,dims)
      case _
        if !data_frames && is_rdd_comprehension(qs)
          // Any other tiled comprehension that depends on RDDs and block tensors
        => val rqs = qs.map {
                        case Generator(p,Lift(block,u))
                          if isBlockTensor(block)
                          => Generator(p,lift(block,u))
                        case q => q
                     }
           val Comprehension(h,nqs) = optimize(Comprehension(hs,rqs))
           val rdd = translate_rdd_compr(h,nqs,vars)
          store(block,List(tp),dims,Lift("rdd",rdd))
      case _
        => Store(block,List(tp),dims,Comprehension(hs,qs))
    }

  def translate_tiled ( e: Expr, vars: List[String] ): Expr
    = e match {
        case Store(block,tps,dims,Comprehension(h,qs))
          if isBlockTensor(block)
          => val tp = tps match { case List(tp) => tp; case _ => boolType }
             val res = optimize(translate_tiled_compr(block,h,qs,vars,tp,dims))
             if (res == e) res else translate_tiled(res,vars)
        case reduce(op,x@Comprehension(h,qs))
          if is_tiled_comprehension(qs)
          // total aggregation on tiled comprehensions
          => val tile_value = reduce(op,Comprehension(h,tile_qualifiers(qs,vars)))
             val nq = rdd_qualifiers(qs,vars)
             val Comprehension(nhs,nqs) = optimize(Comprehension(tile_value,nq))
             if (data_frames)
               translate_sql(nhs,nqs,op)
             else reduce(op,translate_tiled(Comprehension(nhs,nqs),vars))
        case Block(es)
          => Block(es.foldLeft[(List[Expr],List[String])] ((Nil,vars)) {
                       case ((r,s),e@VarDecl(v,u,x))
                         => (r:+translate_tiled(e,s),v::s)
                       case ((r,s),e)
                         => (r:+translate_tiled(e,s),s)
                   }._1)
        case _ => apply(e,(x:Expr) => translate_tiled(x,vars))
      }
}
