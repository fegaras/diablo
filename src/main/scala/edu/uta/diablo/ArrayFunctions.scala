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

import scala.collection.mutable
import scala.reflect.ClassTag
import org.apache.spark.rdd.RDD
import scala.collection.parallel.immutable.ParRange
// add for Scala 2.13
//import scala.collection.parallel.CollectionConverters._


trait ArrayFunctions {
  // parRange doesn't work
  final def parRange ( n: Int, m: Int, s: Int ): ParRange = scala.collection.immutable.Range(n,m,s).par

  /* The size of an object */
  final def sizeof ( x: AnyRef ): Long = {
    import org.apache.spark.util.SizeEstimator.estimate
    estimate(x)
  }

  def array_size ( x: EmptyTuple ): Int = 0
  def array_size ( x: Int ): Int = x
  def array_size ( x: (Int,Int) ): Int = x._1*x._2
  def array_size ( x: (Int,Int,Int) ): Int = x._1*x._2*x._3

  // an RDD map that preserves partitioning
  def mapPreservesPartitioning[V:ClassTag,U:ClassTag] ( rdd: RDD[V], f: V => U ): RDD[U]
    = rdd.mapPartitions( it => it.map(f), preservesPartitioning = true )

  // map-join or reduce-join based on rdd size
  final def diablo_join[K:ClassTag, T:ClassTag, S:ClassTag]
                ( x: RDD[(K,T)], y: RDD[(K,S)],
                  size_x: Int, size_y: Int, numPartions: Int ): RDD[(K,(T,S))] = {
    if (size_x > 0 && size_x <= broadcast_limit) {
      val bc = spark_context.broadcast(x.groupByKey().collectAsMap())
      y.flatMap { case (i,v) => {
          var ret: List[(K, (T,S))] = List()
          for (x_i <- bc.value(i))
             ret :+= (i,(x_i, v))
          ret
        }
      }
    } else if (size_y > 0 && size_y <= broadcast_limit) {
      val bc = spark_context.broadcast(y.groupByKey().collectAsMap())
      x.flatMap { case (i,v) => {
          var ret: List[(K, (T,S))] = List()
          for (y_i <- bc.value(i))
             ret :+= (i,(v,y_i))
          ret
        }
      }
    }
    else {
      x.join(y, numPartions)
    }
  }

  // An outer-join for 1-1 join relationship
  @specialized
  final def outerJoin[K:ClassTag,T:ClassTag] ( xrdd: RDD[(K,T)], yrdd: RDD[(K,T)],
                                               f: (T,T) => T ): RDD[(K,T)]
    = xrdd.fullOuterJoin(yrdd,number_of_partitions).map {
            case (k,(Some(x),Some(y)))
              => (k,f(x,y))
            case (k,(Some(x),None))
              => (k,x)
            case (k,(_,Some(y)))
              => (k,y)
      }

  // convert a dense array to a tensor (dense dimensions dn>0 & sparse dimensions sn>0)
  @specialized
  final def array2tensor[T:ClassTag] ( dn: Int, sn: Int, zero: T, buffer: Array[T] ): (Array[Int],Array[Int],Array[T]) = {
    val splits = 10
    val split_size = (dn-1)/splits+1
    val dense = Array.ofDim[Int](dn+1)
    val sparseV = Array.ofDim[mutable.ArrayBuffer[Int]](splits)
    val valuesV = Array.ofDim[mutable.ArrayBuffer[T]](splits)
    for ( i <- 0 until splits ) {
      sparseV(i) = new mutable.ArrayBuffer[Int](block_dim_size)
      valuesV(i) = new mutable.ArrayBuffer[T](block_dim_size)
    }
    (0 until splits).par.foreach {
      s => var i = 0
           while ( i < split_size ) {
              var j = 0
              val ni = s*split_size+i
              while ( j < sn && ni*sn+j < buffer.length ) {
                  val v = buffer(ni*sn+j)
                  if ( v != zero ) {
                     sparseV(s) += j
                     valuesV(s) += v
                  }
                  j += 1
              }
              if (i < split_size-1 && ni < dn)
                dense(ni+1) = sparseV(s).length
              i += 1
           }
    }
    val sizes = Array.ofDim[Int](splits)
    var len = 0
    for ( s <- 0 until splits ) {
      sizes(s) = len
      var i = 0
      while ( i < split_size && s*split_size+i < dn ) {
        dense(s*split_size+i) += len
        i += 1
      }
      len += sparseV(s).length
    }
    val sparse = Array.ofDim[Int](len)
    val values = Array.ofDim[T](len)
    (0 until splits).par.foreach {
      s => sparseV(s).copyToArray(sparse,sizes(s))
           valuesV(s).copyToArray(values,sizes(s))
    }
    dense(dn) = sparse.length
    (dense,sparse,values)
  }

  // convert a dense boolean array to a boolean tensor (dense dimensions dn>0 & sparse dimensions sn>0)
  final def array2tensor_bool ( dn: Int, sn: Int, buffer: Array[Boolean] ): (Array[Int],Array[Int]) = {
    val splits = 10
    val split_size = (dn-1)/splits+1
    val dense = Array.ofDim[Int](dn+1)
    val sparseV = Array.ofDim[mutable.ArrayBuffer[Int]](splits)
    for ( i <- 0 until splits )
      sparseV(i) = new mutable.ArrayBuffer[Int](block_dim_size)
    (0 until splits).par.foreach {
      s => var i = 0
           while ( i < split_size ) {
              var j = 0
              val ni = s*split_size+i
              while ( j < sn && ni*sn+j < buffer.length ) {
                  if ( buffer(ni*sn+j) )
                     sparseV(s) += j
                  j += 1
              }
              if (ni < split_size-1)
                dense(ni+1) = sparseV(s).length
              i += 1
           }
    }
    val sizes = Array.ofDim[Int](splits)
    var len = 0
    for ( s <- 0 until splits ) {
      sizes(s) = len
      var i = 0
      while ( i < split_size && s*split_size+i < dn ) {
        dense(s*split_size+i) += len
        i += 1
      }
      len += sparseV(s).length
    }
    val sparse = Array.ofDim[Int](len)
    (0 until splits).par.foreach {
      s => sparseV(s).copyToArray(sparse,sizes(s))
    }
    dense(dn) = sparse.length
    (dense,sparse)
  }

  // convert a dense array to a sparse tensor (dense dimensions dn=0 & sparse dimensions sn>0)
  @specialized
  final def array2tensor[T:ClassTag] ( sn: Int, zero: T, buffer: Array[T] ): (Array[Int],Array[T]) = {
    val sparse = new mutable.ArrayBuffer[Int](block_dim_size)
    val values = new mutable.ArrayBuffer[T](block_dim_size)
    var j = 0
    while ( j < sn ) {
      val v = buffer(j)
      if ( v != zero ) {
        sparse += j
        values += v
      }
      j += 1
    }
    (sparse.toArray,values.toArray)
  }

  // convert a dense boolean array to a sparse boolean tensor (dense dimensions dn=0 & sparse dimensions sn>0)
  final def array2tensor_bool ( sn: Int, buffer: Array[Boolean] ): Array[Int] = {
    val sparse = new mutable.ArrayBuffer[Int](block_dim_size)
    var j = 0
    while ( j < sn ) {
      if ( buffer(j) )
        sparse += j
      j += 1
    }
    sparse.toArray
  }

  // merge two dense tensors using the monoid op/zero
  @specialized
  final def merge_tensors[T:ClassTag] ( X: Array[T], Y: Array[T], op: (T,T) => T, zero: T ): Array[T] = {
    val len = Math.min(X.length,Y.length)
    val values = Array.ofDim[T](X.length)
    0.until(len).par.foreach {
      i => values(i) = op(X(i),Y(i))
    }
    values
  }

  // merge two tensors using the monoid op/zero
  @specialized
  final def merge_tensors[T:ClassTag] ( X: (Array[Int],Array[Int],Array[T]),
                                        Y: (Array[Int],Array[Int],Array[T]),
                                        op: (T,T) => T, zero: T ): (Array[Int],Array[Int],Array[T]) = {
    var i = 0
    val len = Math.min(X._1.length,Y._1.length)-1
    val dense = Array.ofDim[Int](len+1)
    val sparse = new mutable.ArrayBuffer[Int](block_dim_size)
    val values = new mutable.ArrayBuffer[T](block_dim_size)
    while (i < len) {
      var xn = X._1(i)
      var yn = Y._1(i)
      while (xn < X._1(i+1) && yn < Y._1(i+1)) {
        if (X._2(xn) == Y._2(yn)) {
          val v = op(X._3(xn),Y._3(yn))
          if (v != zero) {
            sparse += X._2(xn)
            values += v
          }
          xn += 1
          yn += 1
        } else if (X._2(xn) < Y._2(yn)) {
          val v = op(X._3(xn),zero)
          if (v != zero) {
            sparse += X._2(xn)
            values += v
          }
          xn += 1
        } else {
          val v = op(zero,Y._3(yn))
          if (v != zero) {
            sparse += Y._2(yn)
            values += v
          }
          yn += 1
        }
      }
      while (xn < X._1(i+1)) {
        val v = op(X._3(xn),zero)
        if (v != zero) {
          sparse += X._2(xn)
          values += v
        }
        xn += 1
      }
      while (yn < Y._1(i+1)) {
        val v = op(zero,Y._3(yn))
        if (v != zero) {
          sparse += Y._2(yn)
          values += v
        }
        yn += 1
      }
      i += 1
      dense(i) = sparse.length
    }
    (dense,sparse.toArray,values.toArray)
  }

  // merge two boolean tensors using the monoid op/zero
  final def merge_tensors ( X: (Array[Int],Array[Int]), Y: (Array[Int],Array[Int]),
                            op: (Boolean,Boolean) => Boolean, zero: Boolean ): (Array[Int],Array[Int]) = {
    var i = 0
    val len = Math.min(X._1.length,Y._1.length)-1
    val dense = Array.ofDim[Int](len+1)
    val sparse = new mutable.ArrayBuffer[Int](block_dim_size)
    while (i < len) {
      var xn = X._1(i)
      var yn = Y._1(i)
      while (xn < X._1(i+1) && yn < Y._1(i+1)) {
        if (X._2(xn) == Y._2(yn)) {
          val v = op(true,true)
          if (v)
            sparse += X._2(xn)
          xn += 1
          yn += 1
        } else if (X._2(xn) < Y._2(yn)) {
          val v = op(true,false)
          if (v)
            sparse += X._2(xn)
          xn += 1
        } else {
          val v = op(false,true)
          if (v)
            sparse += Y._2(yn)
          yn += 1
        }
      }
      while (xn < X._1(i+1)) {
        val v = op(true,false)
        if (v)
          sparse += X._2(xn)
        xn += 1
      }
      while (yn < Y._1(i+1)) {
        val v = op(false,true)
        if (v)
          sparse += Y._2(yn)
        yn += 1
      }
      i += 1
      dense(i) = sparse.length
    }
    (dense,sparse.toArray)
  }

  // merge two sparse tensors using the monoid op/zero
  @specialized
  final def merge_tensors[T:ClassTag]
          ( X: (Array[Int],Array[T]), Y: (Array[Int],Array[T]),
            op: (T,T) => T, zero: T ): (Array[Int],Array[T]) = {
    val sparse = new mutable.ArrayBuffer[Int](block_dim_size)
    val values = new mutable.ArrayBuffer[T](block_dim_size)
    var xn = 0
    var yn = 0
    while (xn < X._1.length && yn < Y._1.length) {
        if (X._1(xn) == Y._1(yn)) {
          val v = op(X._2(xn),Y._2(yn))
          if (v != zero) {
            sparse += X._1(xn)
            values += v
          }
          xn += 1
          yn += 1
        } else if (X._1(xn) < Y._1(yn)) {
          val v = op(X._2(xn),zero)
          if (v != zero) {
            sparse += X._1(xn)
            values += v
          }
          xn += 1
        } else {
          val v = op(zero,Y._2(yn))
          if (v != zero) {
            sparse += Y._1(yn)
            values += v
          }
          yn += 1
        }
      }
      while (xn < X._1.length) {
        val v = op(X._2(xn),zero)
        if (v != zero) {
          sparse += X._1(xn)
          values += v
        }
        xn += 1
      }
      while (yn < Y._1.length) {
        val v = op(zero,Y._2(yn))
        if (v != zero) {
          sparse += Y._1(yn)
          values += v
        }
        yn += 1
      }
    (sparse.toArray,values.toArray)
  }

  // merge two boolean sparse tensors using the monoid op/zero
  final def merge_tensors ( X: Array[Int], Y: Array[Int],
                            op: (Boolean,Boolean) => Boolean, zero: Boolean ): Array[Int] = {
    val sparse = new mutable.ArrayBuffer[Int](block_dim_size)
    var xn = 0
    var yn = 0
    while (xn < X.length && yn < Y.length) {
        if (X(xn) == Y(yn)) {
          val v = op(true,true)
          if (v)
            sparse += X(xn)
          xn += 1
          yn += 1
        } else if (X(xn) < Y(yn)) {
          val v = op(true,false)
          if (v)
            sparse += X(xn)
          xn += 1
        } else {
          val v = op(false,true)
          if (v)
            sparse += Y(yn)
          yn += 1
        }
      }
      while (xn < X.length) {
        val v = op(true,false)
        if (v)
          sparse += X(xn)
        xn += 1
      }
      while (yn < Y.length) {
        val v = op(false,true)
        if (v)
          sparse += Y(yn)
        yn += 1
      }
    sparse.toArray
  }

  // Create a dense array and initialize it with the values of the tensor init (if not null).
  // It converts the sparse tensor init to a complete dense array where missing values are zero
  @specialized
  final def array_buffer[T:ClassTag] ( dsize: Int, ssize: Int, zero: T,
                                       init: (Array[Int],Array[Int],Array[T]) = null ): Array[T] = {
    val buffer: Array[T] = Array.tabulate[T](dsize*ssize)( i => zero )
    if (init != null) {
      val (dense,sparse,values) = init
      0.until(dense.length-1).par.foreach {
        i => { var j = dense(i)
               while ( j < dense(i+1) ) {
                  buffer(i*ssize+sparse(j)) = values(j)
                  j += 1
               }
             }
      }
    }
    buffer
  }

  // Create a dense boolean array and initialize it with the values of the boolean tensor init (if not null).
  // It converts the sparse tensor init to a complete dense array where missing values are zero
  final def array_buffer_bool ( dsize: Int, ssize: Int, init: (Array[Int],Array[Int]) = null ): Array[Boolean] = {
    val buffer: Array[Boolean] = Array.tabulate(dsize*ssize)( i => false )
    if (init != null) {
      val (dense,sparse) = init
      0.until(dense.length-1).par.foreach {
        i => { var j = dense(i)
               while ( j < dense(i+1) ) {
                  buffer(i*ssize+sparse(j)) = true
                  j += 1
               }
             }
      }
    }
    buffer
  }

  // Create a dense array and initialize it with the values of the sparse tensor init (if not null).
  // It converts the sparse tensor init to a complete dense array where missing values are zero
  @specialized
  final def array_buffer_sparse[T:ClassTag] ( ssize: Int, zero: T, init: (Array[Int],Array[T]) = null ): Array[T] = {
    val buffer: Array[T] = Array.tabulate[T](ssize)( i => zero )
    if (init != null) {
      val (sparse,values) = init
      sparse.indices.par.foreach {
        j => buffer(sparse(j)) = values(j)
      }
    }
    buffer
  }

  // Create a dense boolean array and initialize it with the values of the sparse boolean tensor init (if not null).
  // It converts the sparse tensor init to a complete dense array where missing values are zero
  final def array_buffer_sparse_bool ( ssize: Int, init: Array[Int] = null ): Array[Boolean] = {
    val buffer: Array[Boolean] = Array.tabulate(ssize)( i => false )
    if (init != null) {
      val sparse = init
      sparse.indices.par.foreach {
        j => buffer(sparse(j)) = true
      }
    }
    buffer
  }

  @specialized
  final def array_buffer_dense[T:ClassTag] ( dsize: Int, zero: T, init: Array[T] = null ): Array[T] = {
    if (init == null)
      Array.tabulate[T](dsize)( i => zero )
    else init.clone
  }

  @specialized
  final def arraySet[T] ( b: mutable.ArrayBuffer[T], i: Int, v: T ): Unit = {
    var j = b.length
    while (j <= i) {
      b.append(v)
      j += 1
    }
  }

  final def range ( n1: Long, n2: Long, n3: Long ): List[Long]
    = n1.to(n2,n3).toList

  final def inRange ( i: Long, n1: Long, n2: Long, n3: Long ): Boolean
    = i>=n1 && i<= n2 && (i-n1)%n3 == 0

  final def unique_values ( f: Int => Int ): mutable.HashSet[Int] = {
    val s = mutable.HashSet[Int]()
    var i = 0
    while (i < block_dim_size) {
      s += f(i)
      i += 1
    }
    s
  }

  final def unique_values ( f: (Int,Int) => Int ): mutable.HashSet[Int] = {
    var s = mutable.HashSet[Int]()
    var i = 0
    while (i < block_dim_size) {
      var j = 0
      while (j < block_dim_size) {
        s += f(i,j)
        j += 1
      }
      i += 1
    }
    s
  }

  final def unique_values ( f: (Int,Int,Int) => Int ): mutable.HashSet[Int] = {
    var s = mutable.HashSet[Int]()
    var i = 0
    while (i < block_dim_size) {
      var j = 0
      while (j < block_dim_size) {
        var k = 0
        while (k < block_dim_size) {
          s += f(i,j,k)
          k += 1
        }
        j += 1
      }
      i += 1
    }
    s
  }

  /* binary search rows for key between the indices from (inclusive) and to (exclusive) */
  @specialized
  final def binarySearch[T] ( key: Int, from: Int, to: Int,
                              rows: Array[Int], values: Array[T], zero: T ): T = {
    val row = java.util.Arrays.binarySearch(rows,from,to,key)
    if (row < 0)
      zero
    else values(row)
  }

  /* binary search rows for key between the indices from (inclusive) and to (exclusive) */
  final def binarySearch ( key: Int, from: Int, to: Int, rows: Array[Int] ): Boolean
    = java.util.Arrays.binarySearch(rows,from,to,key) >= 0

  /* sort both rows and values starting from from */
  final def sort[T] ( from: Int, rows: mutable.ArrayBuffer[Int], values: mutable.ArrayBuffer[T] ): Unit = {
    val len = values.length-from
    if (len <= 1)
      return
    var arr = new mutable.ArrayBuffer[(Int,T)](len)
    var i = 0
    while (i < len) {
      arr.append( (rows(from+i),values(from+i)) )
      i += 1
    }
    arr = arr.sortBy(_._1)
    i = 0
    while (i < len) {
      rows(from+i) = arr(i)._1
      values(from+i) = arr(i)._2
      i += 1
    }
  }

  /* sort rows starting from from */
  final def sort ( from: Int, rows: mutable.ArrayBuffer[Int] ): Unit = {
    val len = rows.length-from
    if (len <= 1)
      return
    var arr = Array.ofDim[Int](len)
    var i = 0
    while (i < len) {
      arr(i) = rows(from+i)
      i += 1
    }
    scala.util.Sorting.quickSort(arr)
    i = 0
    while (i < len) {
      rows(from+i) = arr(i)
      i += 1
    }
  }

  /* map code after cogroup (for each executor) in a groubBy join */
  @specialized
  final def groupByJoin_mapper[K,T,S,R]
        ( left: Iterable[((K,Int),T)],      // left tensors
          right: Iterable[((K,Int),S)],     // right tensors
          left_blocks: Int,                    // each grid cell contains left_blocks*right_blocks tensors
          mult: (T,S) => List[((Int,Int),R)],  // multiply two tensors
          combine: (R,R) => R                  // add two tensors
        ): List[((Int,Int),R)]
      = { val aleft = left.toArray
          val aright = right.toArray
          val grid = mutable.HashMap[(Int,Int),R]()
          for { i <- (0 until left_blocks).par
                ((jx,gx),ta) <- aleft if gx%left_blocks == i
                ((jy,gy),tb) <- aright if jx == jy } {
              val prods = mult(ta,tb)
              val key = (gx,gy)
              if (prods.nonEmpty) {
                val tile = grid.synchronized {
                               grid.getOrElse(key,null)
                           }
                val sum = if (tile != null)
                            combine(tile.asInstanceOf[R],prods.head._2)
                          else prods.head._2
                grid.synchronized {
                    grid += (key -> sum)
                }
              }
          }
          grid.toList
        }

  final def update_array[T] ( a: Object, u: T ): T = u

  final def increment_array[T] ( a: Object, op: String, u: T ): T = u

  final def rangeVar ( x: Int ): Int = x

  // caching is eager for RDDs but lazy for DataFrames
  final def cache[T] ( x: RDD[T] ): RDD[T] = x.cache()

  // forces df to materialize in memory and evaluate all transformations
  // (noop write format doesn't have much overhead)
  final def cache[T] ( x: DiabloDataFrame[T] ): DiabloDataFrame[T] = {
    x.write.mode("overwrite").format("noop").save()
    x
  }
}
