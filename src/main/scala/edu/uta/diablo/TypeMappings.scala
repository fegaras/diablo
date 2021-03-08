/*
 * Copyright © 2021 University of Texas at Arlington
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


object TypeMappings {

  val arrayBuffer = "scala.collection.mutable.ArrayBuffer"
  val rddClass = "org.apache.spark.rdd.RDD"
  val mapClass = "scala.collection.immutable.Map"

  /* initial type mappings */
  val inits = s"""
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
    """

  /* generate a typemap for a tensor with dn dense and sn sparse dimensions */
  def tensor ( dn: Int, sn: Int, boolean_values: Boolean = false ): String = {
    assert(sn+dn > 0)
    val dims = "( "+(1.to(dn).map(k => s"d$k: Int")
                     ++1.to(sn).map(k => s"s$k: Int")).mkString(", ")+" )"
    val ldims = "("+1.to(dn+sn).map(i => "Int").mkString(",")+")"
    val dsize = 1.to(dn).map("d"+_).mkString("*")
    val drange = 1.to(dn).map(i => s"i$i <- 0..(d$i-1)").mkString(", ")
    val srange = 1.to(sn).map(i => s"j$i <- 0..(s$i-1)").mkString(", ")
    val dvars = 1.to(dn).map("i"+_).mkString(",")
    val dvars2 = 1.to(dn).map("ii"+_).mkString(",")
    val svars = 1.to(sn).map("j"+_).mkString(",")
    val deq = 1.to(dn).map(i => s"ii$i == i$i").mkString(", ")
    val dkey = if (dn==1) "i1"
               else dn.until(0,-1).map("d"+_).tails.map(_.mkString("*")).toList.tail
                      .zip(dn.until(1,-1).map("i"+_)).map{ case (x,y) => x+"*"+y }
                      .mkString("+")+"+i1"
    val skey = if (sn==1) "j1"
               else sn.until(0,-1).map("s"+_).tails.map(_.mkString("*")).toList.tail
                      .zip(sn.until(1,-1).map("j"+_)).map{ case (x,y) => x+"*"+y }
                      .mkString("+")+"+j1"
    val set_sparse = 1.to(sn).map(i => s"sparse.append(j$i)").mkString("; ")
    if (sn == 0)   // a dense tensor
      s"""
       typemap tensor_${dn}_0[T] $dims: array$dn[T] {
          def view ( values: vector[T] )
            = [ (($dvars),values[$dkey]) |
                $drange ]
          def store ( L: list[($ldims,T)] )
            = { var values: vector[T] = array($dsize);
                [ values[$dkey] = v |
                  (($dvars),v) <- L ];
                values }
       }
      """
    else if (dn == 0 && boolean_values) // a boolean sparse tensor
      s"""
       typemap bool_tensor_0_$sn $dims: array$sn[Boolean] {
          def view ( sparse: vector[Int] )
            = [ (($svars),binarySearch($skey,0,sparse.length,sparse)) |
                $srange ]
          def store ( L: list[($ldims,Boolean)] )
            = { var sparse: $arrayBuffer[Int];
                [ sparse.append($skey) |
                  (($svars),v) <- L, v ];
                sort(0,sparse);
                sparse.toArray }
       }
      """
    else if (dn == 0) // a sparse tensor
      s"""
       typemap tensor_0_$sn[T] $dims: array$sn[T] {
          def view ( sparse: vector[Int], values: vector[T] )
            = [ (($svars),binarySearch($skey,0,values.length,sparse,values)) |
                $srange ]
          def store ( L: list[($ldims,T)] )
            = { var sparse: $arrayBuffer[Int];
                var values: $arrayBuffer[T];
                var zero: T;
                [ { sparse.append($skey); values.append(v) } |
                  (($svars),v) <- L,
                  v != zero ];
                sort(0,sparse,values);
                (sparse.toArray,values.toArray) }
       }
      """
    else if (boolean_values) // a boolean tensor with dn dense and sn sparse dimensions
      s"""
       typemap bool_tensor_${dn}_$sn $dims: array${dn+sn}[Boolean] {
          def view ( dense: vector[Int], sparse: vector[Int] )
            = [ (($dvars,$svars),binarySearch($skey,dense[loc],dense[loc+1],sparse)) |
                $drange, $srange,
                let loc = $dkey ]
          def store ( L: list[($ldims,Boolean)] )
            = { var dense: vector[Int] = array($dsize+1);
                var sparse: $arrayBuffer[Int];
                [ { dense[$dkey] = sparse.length;
                    sort(dense[$dkey],sparse);
                    [ sparse.append($skey) |
                      (($dvars2,$svars),v) <- L,
                      $deq, v ] } |
                  $drange ];
                dense[$dsize] = sparse.length;
                sort(dense[$dsize],sparse);
                (dense,sparse.toArray) }
       }
      """
    else  // a general tensor with dn dense and sn sparse dimensions
      s"""
       typemap tensor_${dn}_$sn[T] $dims: array${dn+sn}[T] {
          def view ( dense: vector[Int], sparse: vector[Int], values: vector[T] )
            = [ (($dvars,$svars),binarySearch($skey,dense[loc],dense[loc+1],sparse,values)) |
                $drange, $srange,
                let loc = $dkey ]
          def store ( L: list[($ldims,T)] )
            = { var dense: vector[Int] = array($dsize+1);
                var sparse: $arrayBuffer[Int];
                var values: $arrayBuffer[T];
                var zero: T;
                [ { dense[$dkey] = values.length;
                    sort(dense[$dkey],sparse,values);
                    [ { sparse.append($skey); values.append(v) } |
                      (($dvars2,$svars),v) <- L,
                      $deq, v != zero ] } |
                  $drange ];
                dense[$dsize] = values.length;
                sort(dense[$dsize],sparse,values);
                (dense,sparse.toArray,values.toArray) }
       }
      """
  }

  /* generate a typemap for a distributed block tensor with dn dense and sn sparse dimensions */
  def block_tensor ( dn: Int, sn: Int, boolean_values: Boolean = false ): String = {
    assert(sn+dn > 0)
    val N = Math.pow(blockSize,1.0/(dn+sn)).toInt
    val ldims = "("+1.to(dn+sn).map(i => "Int").mkString(",")+")"
    val ddims = 1.to(dn+sn).map(i => N).mkString(",")
    //val sdims = 1.to(sn).map(i => N).mkString(",")
    val dims = "( "+(1.to(dn).map(k => s"d$k: Int")
                     ++1.to(sn).map(k => s"s$k: Int")).mkString(", ")+" )"
    val vars = 1.to(dn+sn).map("i"+_).mkString(",")
    val vars2 = 1.to(dn+sn).map("ii"+_).mkString(",")
    val idx = 1.to(dn+sn).map(k => s"ii$k*$N+i$k").mkString(",")
    val div_vars = 1.to(dn+sn).map(k => s"let ii$k = i$k/$N").mkString(", ")
    val mod_vars = 1.to(dn+sn).map(k => s"i$k%$N").mkString(",")
    if (boolean_values && sn > 0)
      s"""
       typemap block_bool_tensor_${dn}_$sn $dims: array${dn+sn}[Boolean] {
          def view ( b: rdd[($ldims,bool_tensor_${dn}_$sn)] )
            = [ (($idx),v) |
                (($vars2),a) <- b,
                (($vars),v) <- lift(bool_tensor_${dn}_$sn,a) ]
          def store ( L: list[($ldims,Boolean)] )
            = rdd[ (($vars2),bool_tensor_${dn}_$sn($ddims,w)) |
                   (($vars),v) <- L, v,
                   $div_vars,
                   let w = (($mod_vars),v),
                   group by ($vars2) ]
    }
    """
    else s"""
       typemap block_tensor_${dn}_$sn[T] $dims: array${dn+sn}[T] {
          def view ( b: rdd[($ldims,tensor_${dn}_$sn[T])] )
            = [ (($idx),v) |
                (($vars2),a) <- b,
                (($vars),v) <- lift(tensor_${dn}_$sn,a) ]
          def store ( L: list[($ldims,T)] )
            = rdd[ (($vars2),tensor_${dn}_$sn($ddims,w)) |
                   (($vars),v) <- L,
                   $div_vars,
                   let w = (($mod_vars),v),
                   group by ($vars2) ]
    }
    """
  }

  def init () {
    Typechecker.typecheck(Parser.parse(inits))
  }
}
