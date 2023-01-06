/*
 * Copyright © 2021-2023 University of Texas at Arlington
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

import Lifting.{typeMaps,getTypeMap}
import scala.util.matching.Regex

object TypeMappings {
  val arrayBuffer = "scala.collection.mutable.ArrayBuffer"
  val mapClass = "scala.collection.immutable.Map"

  /* initial type mappings */
  val inits = s"""

    // for testing only; use tensor instead
    typemap vec[T] ( d: Int ): vector[T] {
      def view ( v: vector[T] )
        = [ (i,v[i]) | i <- 0..(d-1) ]
      def store ( L: list[(Int,T)] )
        = { var a: vector[T] = array(d);
            [ { a[i] = v }
            | (i,v) <- L ]
            a }
    }

    // key-value map
    typemap map[K,V] (): list[(K,V)] {
       def view ( m: $mapClass[K,V] ) = m.toList
       def store ( L: list[(K,V)] ) = L.toMap
    }

    // A Spark RDD collection
    typemap rdd[T] (): list[T] {
       def view ( R: $rddClass[T] ) = R.collect.toList
       def store ( L: list[T] ) = spark_context.parallelize(L)
    }

    // A Spark Dataset collection
    typemap dataset[T] (): list[T] {
       def view ( R: $datasetClass[T] ) = ()
       def store ( L: list[T] ) = ()
    }

    typemap block_map[K,V] (): map[K,V] {
       def view ( b: rdd[(Int,$mapClass[K,V])] )
         = [ (k,v) |
             (i,m) <- lift(rdd,b),
             (k,v) <- lift(map,m) ]
       def store ( L: list[(K,V)] )
         = rdd[ (i,map(w)) |
                (k,v) <- L,
                let w = (k,v),
                group by i: (k.hashCode % $block_dim_size) ]
    }

    typemap flatten[T] ( d: Int ): vector[vector[T]] {
       def view ( dense: vector[Int], values: vector[T] )
         = [ ( i, [ (j-dense[i],values[j]) | j <- dense[i]..(dense[i+1]-1) ] ) |
             i <- 0..(d-1) ]
       def store ( L: list[(Int,list[(Int,T)])] )
         = { var dense: vector[Int] = array(d+1);
             var values: $arrayBuffer[T];
             [ { dense[i] = values.length;
                 [ arraySet(values,dense[i]+j,v) |
                   (j,v) <- a ] } |
               i <- 0..(d-1), (ii,a) <- L, ii == i ];
             dense[d] = values.length;
             (dense,values.toArray) }
    }
    """

  /* generate a typemap for a tensor with dn dense and sn sparse dimensions */
  def tensor ( dn: Int, sn: Int, boolean_values: Boolean = false ): String = {
    assert(sn+dn > 0)
    val dims = "( d: ("+1.to(dn).map(i => "Int").mkString(",")+
               "), s: ("+1.to(sn).map(i => "Int").mkString(",")+") )"
    val ldims = "("+1.to(dn+sn).map(i => "Int").mkString(",")+")"
    val dsize = if (dn==1) "d" else 1.to(dn).map(i => "d#"+i).mkString("*")
    val ssize = if (sn==1) "s" else 1.to(sn).map(i => "s#"+i).mkString("*")
    val drange = if (dn==1) "i1 <- 0..(d-1)"
                 else 1.to(dn).map(i => s"i$i <- 0..(d#$i-1)").mkString(", ")
    val srange = if (sn==1) "i1 <- 0..(s-1)"
                 else 1.to(sn).map(i => s"j$i <- 0..(s#$i-1)").mkString(", ")
    val dvars = 1.to(dn).map("i"+_).mkString(",")
    val dvars2 = 1.to(dn).map("ii"+_).mkString(",")
    val svars = 1.to(sn).map("j"+_).mkString(",")
    val deq = 1.to(dn).map(i => s"ii$i == i$i").mkString(", ")
    val dkey = (2 to dn).foldLeft("i1") { case (r,i) => s"($r*d#$i+i$i)" }
    val skey = (2 to sn).foldLeft("j1") { case (r,i) => s"($r*s#$i+j$i)" }
    val conds = ((if (dn==1) List("i1 >= 0, i1 < d")
                  else 1.to(dn).map( i => s"i$i >= 0, i$i < d#$i" ))
                 ++(if (sn==1) List("j1 >= 0, j1 < s")
                    else 1.to(sn).map( i => s"j$i >= 0, j$i < s#$i" ))).mkString(", ")
    val svarset = if (sn==1) "let j1 = sparse[col]%s"
                  else (1 to sn).map{ k => s"let j$k = "+("sparse[col]"::(sn.to(k+1,-1))
                            .map(i => s"s#$i").toList).mkString("/")+s"%s#$k" }.mkString(", ")
    if (sn == 0)   // a dense tensor
      s"""
       typemap tensor_${dn}_0[T] $dims: array$dn[T] {
          def view ( values: vector[T] )
            = [ (($dvars),values[$dkey]) |
                $drange ]
          def store ( L: list[($ldims,T)] )
            = { var zero: T;
                var buffer: vector[T] = array_buffer_dense($dsize,zero);
                [ { buffer[$dkey] = v } |
                  (($dvars),v) <- L, $conds ];
                buffer }
       }
      """
    else if (dn == 0 && boolean_values) // a boolean sparse tensor
      s"""
       typemap bool_tensor_0_$sn $dims: array$sn[Boolean] {
          def view ( sparse: vector[Int] )
            = [ (($svars),true) |
                col <- 0..(sparse.length-1),
                $svarset ]
          def store ( L: list[($ldims,Boolean)] )
            = { var buffer: vector[Boolean] = array_buffer_sparse_bool($ssize);
                [ { buffer[$skey] = v } |
                  (($svars),v) <- L, $conds ];
                array2tensor_bool($ssize,buffer)
              }
       }
      """
    else if (dn == 0) // a sparse tensor
      s"""
       typemap tensor_0_$sn[T] $dims: array$sn[T] {
          def view ( sparse: vector[Int], values: vector[T] )
            = [ (($svars),values[col]) |
                col <- 0..(sparse.length-1),
                $svarset ]
          def store ( L: list[($ldims,T)] )
            = { var zero: T;
                var buffer: vector[T] = array_buffer_sparse($ssize,zero);
                [ { buffer[$skey] = v } |
                  (($svars),v) <- L, $conds ];
                array2tensor($ssize,zero,buffer)
              }
       }
      """
    else if (boolean_values) // a boolean tensor with dn dense and sn sparse dimensions
      s"""
       typemap bool_tensor_${dn}_$sn $dims: array${dn+sn}[Boolean] {
          def view ( dense: vector[Int], sparse: vector[Int] )
            = [ (($dvars,$svars),true) |
                $drange,
                let loc = $dkey,
                col <- (dense[loc])..(dense[loc+1]-1),
                $svarset ]
          def store ( L: list[($ldims,Boolean)] )
            = { var buffer: vector[Boolean] = array_buffer_bool($dsize,$ssize);
                [ { buffer[$dkey*$ssize+$skey] = v } |
                  (($dvars,$svars),v) <- L, $conds ];
                array2tensor_bool($dsize,$ssize,buffer)
              }
       }
      """
    else  // a general tensor with dn dense and sn sparse dimensions
      s"""
       typemap tensor_${dn}_$sn[T] $dims: array${dn+sn}[T] {
          def view ( dense: vector[Int], sparse: vector[Int], values: vector[T] )
            = [ (($dvars,$svars),values[col]) |
                $drange,
                let loc = $dkey,
                col <- (dense[loc])..(dense[loc+1]-1),
                $svarset ]
          def store ( L: list[($ldims,T)] )
            = { var zero: T;
                var buffer: vector[T] = array_buffer($dsize,$ssize,zero);
                [ { buffer[$dkey*$ssize+$skey] = v } |
                  (($dvars,$svars),v) <- L, $conds ];
                array2tensor($dsize,$ssize,zero,buffer)
              }
       }
      """
  }

  /* generate a typemap for a full sparse tensor with dn dense and sn sparse dimensions */
  def full_tensor ( dn: Int, sn: Int, boolean_values: Boolean = false ): String = {
    assert(sn > 0)
    val dims = "( d: ("+1.to(dn).map(i => "Int").mkString(",")+
               "), s: ("+1.to(sn).map(i => "Int").mkString(",")+") )"
    val ldims = "("+1.to(dn+sn).map(i => "Int").mkString(",")+")"
    val drange = if (dn==1) "i1 <- 0..(d-1)"
                 else 1.to(dn).map(i => s"i$i <- 0..(d#$i-1)").mkString(", ")
    val srange = if (sn==1) "j1 <- 0..(s-1)"
                 else 1.to(sn).map(i => s"j$i <- 0..(s#$i-1)").mkString(", ")
    val dvars = 1.to(dn).map("i"+_).mkString(",")
    val svars = 1.to(sn).map("j"+_).mkString(",")
    val dkey = (2 to dn).foldLeft("i1") { case (r,i) => s"($r*d#$i+i$i)" }
    val skey = (2 to sn).foldLeft("j1") { case (r,i) => s"($r*s#$i+j$i)" }
    if (dn == 0 && boolean_values) // a boolean sparse tensor
      s"""
       typemap full_bool_tensor_0_$sn $dims: array$sn[Boolean] {
          def view ( sparse: vector[Int] )
            = [ (($svars),binarySearch($skey,0,sparse.length,sparse)) |
                $srange ]
          def store ( L: list[($ldims,Boolean)] ) = ()
       }
      """
    else if (dn == 0) // a sparse tensor
      s"""
       typemap full_tensor_0_$sn[T] $dims: array$sn[T] {
          def view ( sparse: vector[Int], values: vector[T] )
            = [ (($svars),binarySearch($skey,0,values.length,sparse,values)) |
                $srange ]
          def store ( L: list[($ldims,T)] ) = ()
       }
      """
    else if (boolean_values) // a boolean tensor with dn dense and sn sparse dimensions
      s"""
       typemap full_bool_tensor_${dn}_$sn $dims: array${dn+sn}[Boolean] {
          def view ( dense: vector[Int], sparse: vector[Int] )
            = [ (($dvars,$svars),binarySearch($skey,dense[loc],dense[loc+1],sparse)) |
                $drange, $srange,
                let loc = $dkey ]
          def store ( L: list[($ldims,Boolean)] ) = ()
       }
      """
    else  // a general tensor with dn dense and sn sparse dimensions
      s"""
       typemap full_tensor_${dn}_$sn[T] $dims: array${dn+sn}[T] {
          def view ( dense: vector[Int], sparse: vector[Int], values: vector[T] )
            = [ (($dvars,$svars),binarySearch($skey,dense[loc],dense[loc+1],sparse,values)) |
                $drange, $srange,
                let loc = $dkey ]
          def store ( L: list[($ldims,T)] ) = ()
       }
      """
  }

 /* generate a typemap for a distributed block tensor with dn dense and sn sparse dimensions */
  def block_tensor ( dn: Int, sn: Int, cm: String, boolean_values: Boolean = false, full: String = "" ): String = {
    assert(sn+dn > 0)
    def rep ( f: Int => String, sep: String = "," ): String = 1.to(dn+sn).map(f).mkString(sep)
    val N = block_dim_size
    val dims = "( d: ("+1.to(dn).map(i => "Int").mkString(",")+
               "), s: ("+1.to(sn).map(i => "Int").mkString(",")+") )"
    val ldims = rep(i => "Int")
    // the last tile size is dim % block_dim_size
    val ddims = if (dn==1) s"if ((ii1+1)*$N > d) (d % $N) else $N"
                else 1.to(dn).map(k => s"if ((ii$k+1)*$N > d#$k) (d#$k % $N) else $N").mkString(",")
    val sdims = if (sn==1) s"if ((ii${dn+1}+1)*$N > s) (s % $N) else $N"
                else 1.to(sn).map(k => s"if ((ii${k+dn}+1)*$N > s#$k) (s#$k % $N) else $N").mkString(",")
    val vars = rep("i"+_)
    val vars2 = rep("ii"+_)
    val div_vars = rep(k => s"let ii$k = i$k / $N")
    val mod_vars = rep(k => s"i$k % $N")
    val idx = rep(k => s"ii$k * $N + i$k")
    val ranges = ((if (dn==1) List(s"ii1 * $N + i1 >= 0, ii1 * $N + i1 < d")
                   else 1.to(dn).map(k => s"ii$k * $N + i$k >= 0, ii$k * $N + i$k < d#$k"))
                  ++(if (sn==1) List(s"ii${dn+1} * $N + i${dn+1} >= 0, ii${dn+1} * $N + i${dn+1} < s")
                     else 1.to(sn).map(k => s"ii${k+dn} * $N + i${k+dn} >= 0, ii${k+dn} * $N + i${k+dn} < s#$k"))).mkString(", ")
    if (boolean_values) {
      s"""
       typemap ${full}${cm}_block_bool_tensor_${dn}_$sn $dims: array${dn+sn}[Boolean] {
          def view ( x: $cm[(($ldims),bool_tensor_${dn}_$sn)] )
            = [ (($idx),v) |
                (($vars2),a) <- lift($cm,x),
                (($vars),v) <- lift(${full}bool_tensor_${dn}_$sn,a),
                $ranges ]
          def store ( L: list[(($ldims),Boolean)] )
            = $cm[ (($vars2),bool_tensor_${dn}_$sn(($ddims),($sdims),w)) |
                   (($vars),v) <- L, v,
                   $div_vars,
                   let w = (($mod_vars),v),
                   group by ($vars2) ]
       }
    """
    } else s"""
       typemap ${full}${cm}_block_tensor_${dn}_$sn[T] $dims: array${dn+sn}[T] {
          def view ( x: $cm[(($ldims),tensor_${dn}_$sn[T])] )
            = [ (($idx),v) |
                (($vars2),a) <- lift($cm,x),
                (($vars),v) <- lift(${full}tensor_${dn}_$sn,a),
                $ranges ]
          def store ( L: list[(($ldims),T)] )
            = $cm[ (($vars2),tensor_${dn}_$sn(($ddims),($sdims),w)) |
                   (($vars),v) <- L,
                   $div_vars,
                   let w = (($mod_vars),v),
                   group by ($vars2) ]
    }
    """
  }

  def init (): Unit = {
    Typechecker.typecheck(Parser.parse(inits))
  }

  def main ( args: Array[String] ): Unit = {
     println(tensor(args(0).toInt,args(1).toInt,args(2).toInt == 1))
     println(block_tensor(args(0).toInt,args(1).toInt,"rdd",args(2).toInt == 1))
  }
}
