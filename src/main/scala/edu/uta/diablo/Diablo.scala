/*
 * Copyright © 2020-2021 University of Texas at Arlington
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
package edu.uta

import scala.language.experimental.macros
import org.apache.spark.{SparkContext,Partitioner,HashPartitioner}
import org.apache.spark.rdd.RDD
import diablo.Parser.parse
import scala.collection.mutable
import scala.reflect.macros.whitebox
import scala.reflect.macros.whitebox.Context
import scala.reflect.ClassTag

package object diablo {
  var trace = true               // print trace info
  var groupByJoin = false        // experimental SUMMA groupby-join
  var parallel = true            // Yes for multicore parellism
  var block_dim_size = 1000      // size of each dimension of a block tensor
  var number_of_partitions = 10  // num of partitions in shuffling operations

  var spark_context: SparkContext = _

  // An outer-join for 1-1 join relationship
  def outerJoin[K:ClassTag,T:ClassTag] ( xrdd: RDD[(K,T)], yrdd: RDD[(K,T)], f: (T,T) => T ): RDD[(K,T)]
    = xrdd.cache.fullOuterJoin(yrdd.cache,number_of_partitions).map {
            case (k,(Some(x),Some(y)))
              => (k,f(x,y))
            case (k,(Some(x),None))
              => (k,x)
            case (k,(_,Some(y)))
              => (k,y)
      }

  // convert a dense array to a tensor (dense dimensions dn>0 & sparse dimensions sn>0)
  def array2tensor[T:ClassTag] ( dn: Int, sn: Int, zero: T, buffer: Array[T] ): (Array[Int],Array[Int],Array[T]) = {
    val dense = Array.ofDim[Int](dn+1)
    val sparse = new mutable.ArrayBuffer[Int]()
    val values = new mutable.ArrayBuffer[T]()
    var i = 0
    while ( i < dn ) {
      var j = 0
      while ( j < sn ) {
        val v = buffer(i*sn+j)
        if ( v != zero ) {
          sparse.append(j)
          values.append(v)
        }
        j += 1
      }
      i += 1
      dense(i) = sparse.length
    }
    (dense,sparse.toArray,values.toArray)
  }

  // convert a dense boolean array to a boolean tensor (dense dimensions dn>0 & sparse dimensions sn>0)
  def array2tensor_bool ( dn: Int, sn: Int, buffer: Array[Boolean] ): (Array[Int],Array[Int]) = {
    val dense = Array.ofDim[Int](dn+1)
    val sparse = new mutable.ArrayBuffer[Int]()
    var i = 0
    while ( i < dn ) {
      var j = 0
      while ( j < sn ) {
        if ( buffer(i*sn+j) )
          sparse.append(j)
        j += 1
      }
      i += 1
      dense(i) = sparse.length
    }
    (dense,sparse.toArray)
  }

  // convert a dense array to a sparse tensor (dense dimensions dn=0 & sparse dimensions sn>0)
  def array2tensor[T:ClassTag] ( sn: Int, zero: T, buffer: Array[T] ): (Array[Int],Array[T]) = {
    val sparse = new mutable.ArrayBuffer[Int]()
    val values = new mutable.ArrayBuffer[T]()
    var j = 0
    while ( j < sn ) {
      val v = buffer(j)
      if ( v != zero ) {
        sparse.append(j)
        values.append(v)
      }
      j += 1
    }
    (sparse.toArray,values.toArray)
  }

  // convert a dense boolean array to a sparse boolean tensor (dense dimensions dn=0 & sparse dimensions sn>0)
  def array2tensor_bool ( sn: Int, buffer: Array[Boolean] ): Array[Int] = {
    val sparse = new mutable.ArrayBuffer[Int]()
    var j = 0
    while ( j < sn ) {
      if ( buffer(j) )
        sparse.append(j)
      j += 1
    }
    sparse.toArray
  }

  // Create a dense array and initialize it with the values of the tensor init (if not null).
  // It converts the sparse tensor init to a complete dense array where missing values are zero
  def array_buffer[T:ClassTag] ( dsize: Int, ssize: Int, zero: T, init: (Array[Int],Array[Int],Array[T]) = null ): Array[T] = {
    val buffer: Array[T] = Array.tabulate[T](dsize*ssize)( i => zero )
    if (init != null) {
      val (dense,sparse,values) = init
      var i = 0
      while ( i < dense.length-1 ) {
        var j = dense(i)
        while ( j < dense(i+1) ) {
          buffer(i*ssize+sparse(j)) = values(j)
          j += 1
        }
        i += 1
      }
    }
    buffer
  }

  // Create a dense boolean array and initialize it with the values of the boolean tensor init (if not null).
  // It converts the sparse tensor init to a complete dense array where missing values are zero
  def array_buffer_bool ( dsize: Int, ssize: Int, init: (Array[Int],Array[Int]) = null ): Array[Boolean] = {
    val buffer: Array[Boolean] = Array.tabulate(dsize*ssize)( i => false )
    if (init != null) {
      val (dense,sparse) = init
      var i = 0
      while ( i < dense.length-1 ) {
        var j = dense(i)
        while ( j < dense(i+1) ) {
          buffer(i*ssize+sparse(j)) = true
          j += 1
        }
        i += 1
      }
    }
    buffer
  }

  // Create a dense array and initialize it with the values of the sparse tensor init (if not null).
  // It converts the sparse tensor init to a complete dense array where missing values are zero
  def array_buffer_sparse[T:ClassTag] ( ssize: Int, zero: T, init: (Array[Int],Array[T]) = null ): Array[T] = {
    val buffer: Array[T] = Array.tabulate[T](ssize)( i => zero )
    if (init != null) {
      val (sparse,values) = init
      var j = 0
      while ( j < sparse.length ) {
        buffer(sparse(j)) = values(j)
        j += 1
      }
    }
    buffer
  }

  // Create a dense boolean array and initialize it with the values of the sparse boolean tensor init (if not null).
  // It converts the sparse tensor init to a complete dense array where missing values are zero
  def array_buffer_sparse_bool ( ssize: Int, init: Array[Int] = null ): Array[Boolean] = {
    val buffer: Array[Boolean] = Array.tabulate(ssize)( i => false )
    if (init != null) {
      val sparse = init
      var j = 0
      while ( j < sparse.length ) {
        buffer(sparse(j)) = true
        j += 1
      }
    }
    buffer
  }

  def array_buffer_dense[T:ClassTag] ( dsize: Int, zero: T, init: Array[T] = null ): Array[T] = {
    if (init == null)
      Array.tabulate[T](dsize)( i => zero )
    else init.clone
  }

  def arraySet[T] ( b: mutable.ArrayBuffer[T], i: Int, v: T ) {
    var j = b.length
    while (j <= i) {
      b.append(v)
      j += 1
    }
  }

  def range ( n1: Long, n2: Long, n3: Long ): List[Long]
    = n1.to(n2,n3).toList

  def inRange ( i: Long, n1: Long, n2: Long, n3: Long ): Boolean
    = i>=n1 && i<= n2 && (i-n1)%n3 == 0

  def unique_values ( f: Int => Int ): mutable.HashSet[Int] = {
    val s = mutable.HashSet[Int]()
    var i = 0
    while (i < block_dim_size) {
      s += f(i)
      i += 1
    }
    s
  }

  def unique_values ( f: (Int,Int) => Int ): mutable.HashSet[Int] = {
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

  def unique_values ( f: (Int,Int,Int) => Int ): mutable.HashSet[Int] = {
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

  def binarySearch[@specialized T] ( key: Int, from: Int, to: Int,
                                     rows: Array[Int], values: Array[T], zero: T ): T = {
    var low = from
    var high = to-1
    while (low <= high) {
      val mid = (low + high) >>> 1
      val d = rows(mid)
      if (d == key)
        return values(mid)
      else if (d > key)
        high = mid - 1
      else if (d < key)
        low = mid + 1
    }
    zero
  }

  def binarySearch ( key: Int, from: Int, to: Int, rows: Array[Int] ): Boolean = {
    var low = from
    var high = to-1
    while (low <= high) {
      val mid = (low + high) >>> 1
      val d = rows(mid)
      if (d == key)
        return true
      else if (d > key)
        high = mid - 1
      else if (d < key)
        low = mid + 1
    }
    false
  }

  def sort[T] ( from: Int, rows: mutable.ArrayBuffer[Int], values: mutable.ArrayBuffer[T] ) {
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

  def sort ( from: Int, rows: mutable.ArrayBuffer[Int] ) {
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

  def update_array[T] ( a: Object, u: T ): T = u

  def increment_array[T] ( a: Object, op: String, u: T ): T = u

  private var typeMapsLib = false

  def opt ( e: Expr): Expr = Optimizer.optimizeAll(Normalizer.normalizeAll(e))

  def q_impl ( c: Context ) ( query: c.Expr[String] ): c.Expr[Any] = {
    import c.universe.{Expr=>_,Type=>_,_}
    val context: c.type = c
    val cg = new { val c: context.type = context } with CodeGeneration
    val Literal(Constant(s:String)) = query.tree
    // hooks to the Scala compiler
    Typechecker.typecheck_var
       = ( v: String ) => cg.typecheckOpt(Var(v)).map(cg.Tree2Type)
    Typechecker.typecheck_method
       = ( o: Type, m: String, args: List[Type] ) => cg.typecheck_method(o,m,args)
    Typechecker.typecheck_call
       = ( f: String, args: List[Type] ) => cg.typecheck_call(f,args)
    val env: cg.Environment = Nil
    if (!typeMapsLib) {
      TypeMappings.init()
      typeMapsLib = true
    }
    Typechecker.useStorageTypes = false
    val q = parse(s)
    if (trace) println("Imperative program:\n"+Pretty.print(q))
    Typechecker.typecheck(q)
    val sq = Translator.translate(q)
    //if (trace) println("Comprehension:\n"+Pretty.print(sq))
    val n = opt(sq)
    if (trace) println("Normalized comprehension:\n"+Pretty.print(n))
    val le = opt(Lifting.lift(n))
    if (trace) println("Lifted comprehension:\n"+Pretty.print(le))
    Typechecker.clean(le)
    Typechecker.typecheck(le)  // the ComprehensionTranslator needs type info
    val to = opt(ComprehensionTranslator.translate(le))
    val pc = if (parallel) ComprehensionTranslator.parallelize(to) else to
    if (trace) println("Compiled comprehension:\n"+Pretty.print(pc))
    val ec = cg.codeGen(pc,env)
    if (trace) println("Scala code:\n"+showCode(ec))
    val tc = cg.getType(ec,env)
    if (trace) println("Scala type: "+tc)
    context.Expr[Any](ec)
  }

  /** translate an array comprehension to Scala code */
  def q ( query: String ): Any = macro q_impl

  def parami_impl( c: whitebox.Context )(x: c.Expr[Int], b: c.Expr[Int] ): c.Expr[Unit] = {
    import c.universe._
    val Literal(Constant(bv:Int)) = b.tree
    x.tree.toString.split('.').last match {
       case "block_dim_size" => block_dim_size = bv
       case "number_of_partitions" => number_of_partitions = bv
       case p => throw new Error("Wrong param: "+p)
    }
    c.Expr[Unit](q"()")
   }

  /** set compilation parameters */
  def parami ( x:Int, b: Int ): Unit = macro parami_impl

  def param_impl( c: whitebox.Context )(x: c.Expr[Boolean], b: c.Expr[Boolean] ): c.Expr[Unit] = {
    import c.universe._
    val Literal(Constant(bv:Boolean)) = b.tree
    x.tree.toString.split('.').last match {
       case "trace" => trace = bv
       case "groupByJoin" => groupByJoin = bv
       case "parallel" => parallel = bv
       case p => throw new Error("Wrong param: "+p)
    }
    c.Expr[Unit](q"()")
   }

  /** set compilation parameters */
  def param ( x:Boolean, b: Boolean ): Unit = macro param_impl
}
