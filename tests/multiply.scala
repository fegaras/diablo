import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import org.apache.spark.sql._
import org.apache.spark.sql.functions._
import org.apache.spark.sql.expressions.Aggregator
import org.apache.spark.sql.catalyst.encoders.ExpressionEncoder
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._
//import com.github.fommil.netlib.NativeSystemBLAS
import org.apache.log4j._
import org.apache.hadoop.fs._
import scala.collection.Seq
import scala.util.Random
import Math._


object Multiply {
  /* The size of an object */
  def sizeof ( x: AnyRef ): Long = {
    import org.apache.spark.util.SizeEstimator.estimate
    estimate(x)
  }

  def main ( args: Array[String] ) {
    val repeats = args(0).toInt   // how many times to repeat each experiment
    // each matrix has n*m elements
    val n = args(1).toInt
    val m = if (args.length > 2) args(2).toInt else n
    val sparsity = if (args.length > 3) args(3).toDouble else 0.01
    parami(block_dim_size,1000)  // size of each dimension in a block
    val N = 1000
    val validate_output = false
    parami(number_of_partitions,10)

    val conf = new SparkConf().setAppName("tiles")
    spark_context = new SparkContext(conf)
    conf.set("spark.serializer","org.apache.spark.serializer.KryoSerializer")
    conf.set("spark.kryo.registrationRequired","true")
    val spark = SparkSession.builder().config(conf).getOrCreate()
    import spark.implicits._

    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.WARN)

    def randomIJVMatrix ( n: Int, m: Int ): RDD[((Int,Int),Double)] = {
      val max = 10
      val l = Random.shuffle((0 until n).toList)
      val r = Random.shuffle((0 until m).toList)
      spark_context.parallelize(l)
        .flatMap{ i => val rand = new Random()
                       r.map{ j => ((i.toInt,j.toInt),rand.nextDouble()*max) } }
        .cache()
    }

    def testMultiplyIJV (): Double = {
      // matrix multiplication of IJV matrices using Diablo array comprehensions
      val MM = randomIJVMatrix(n,m)
      val NN = randomIJVMatrix(m,n)
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  rdd[ ((i,j),+/v) | ((i,k),mm) <- MM, ((kk,j),nn) <- NN, let v = mm*nn, k == kk, group by (i,j) ]
                  """)
        val x = C.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def randomTile ( nd: Int, md: Int ): DenseMatrix = {
      val max = 10
      val rand = new Random()
      new DenseMatrix(nd,md,Array.tabulate(nd*md){ i => rand.nextDouble()*max })
    }

    def randomMatrix ( rows: Int, cols: Int ): RDD[((Int, Int),org.apache.spark.mllib.linalg.Matrix)] = {
      val l = Random.shuffle((0 until (rows+N-1)/N).toList)
      val r = Random.shuffle((0 until (cols+N-1)/N).toList)
      spark_context.parallelize(for { i <- l; j <- r } yield (i,j),
                                number_of_partitions)
                   .map{ case (i,j) => ((i,j),randomTile(if ((i+1)*N > rows) rows%N else N,
                                                         if ((j+1)*N > cols) cols%N else N)) }
    }

    def randomTileSparse ( nd: Int, md: Int ): SparseMatrix = {
      val max = 10
      val rand = new Random()
      var entries = scala.collection.mutable.ArrayBuffer[(Int,Int,Double)]()
      for (i <- 0 to nd-1; j <- 0 to md-1) {
        if (rand.nextDouble() <= sparsity)
          entries += ((i,j,rand.nextDouble()*max))
      }
      SparseMatrix.fromCOO(nd,md,entries)
    }

    def randomSparseMatrix ( rows: Int, cols: Int ): RDD[((Int, Int),org.apache.spark.mllib.linalg.Matrix)] = {
      val l = Random.shuffle((0 until (rows+N-1)/N).toList)
      val r = Random.shuffle((0 until (cols+N-1)/N).toList)
      spark_context.parallelize(for { i <- l; j <- r } yield (i,j),
                                number_of_partitions)
            .map{ case (i,j) => ((i,j),randomTileSparse(if ((i+1)*N > rows) rows%N else N,
                              if ((j+1)*N > cols) cols%N else N)) }
    }

    val Am = randomMatrix(n,m).cache()
    val Bm = randomMatrix(m,n).cache()

    val A = new BlockMatrix(Am,N,N)
    val B = new BlockMatrix(Bm,N,N)

    val AS = randomSparseMatrix(n,m).cache()
    val BS = randomSparseMatrix(m,n).cache()

    val ASparse = new BlockMatrix(AS,N,N).cache
    val BSparse = new BlockMatrix(BS,N,N).cache

    type tiled_matrix = ((Int,Int),EmptyTuple,RDD[((Int,Int),((Int,Int),EmptyTuple,Array[Double]))])
    val et = EmptyTuple()
    // dense block tensors
    val AA = ((n,m),et,Am.map{ case ((i,j),a) => ((i,j),((a.numRows,a.numCols),et,a.transpose.toArray)) })
    val BB = ((m,n),et,Bm.map{ case ((i,j),a) => ((i,j),((a.numRows,a.numCols),et,a.transpose.toArray)) })
    AA._3.cache
    BB._3.cache

    val rand = new Random()
    def random () = rand.nextDouble()*10

    // sparse block tensors with 99% zeros
    val Az = q("tensor*(n)(m)[ ((i,j),random()) | i <- 0..(n-1), j <- 0..(m-1), random() > (1.0-sparsity)*10 ]")
    Az._3.cache
    val Bz = q("tensor*(m)(n)[ ((i,j),random()) | i <- 0..(n-1), j <- 0..(m-1), random() > (1.0-sparsity)*10 ]")
    Bz._3.cache

    def validate ( M: tiled_matrix ) = {
      if (!validate_output)
        M._3.count()
      else {
        val C = A.multiply(B).toLocalMatrix()
        val CC = M._3.collect
        println("Validating ...")
        for { ((ii,jj),((nd,md),_,a)) <- CC
              i <- 0 until nd
              j <- 0 until md } {
           val ci = ii*N+nd
           if (Math.abs(a(i*md+j)-C(ii*N+i,jj*N+j)) > 0.01)
             println("Element (%d,%d)(%d,%d) is wrong: %.3f %.3f"
                     .format(ii,jj,i,j,a(i*md+j),C(ii*N+i,jj*N+j)))
        }
      }
    }

    // forces df to materialize in memory and evaluate all transformations
    // (noop write format doesn't have much overhead)
    def force ( df: DataFrame ) {
      df.write.mode("overwrite").format("noop").save()
    }

    def map ( m: BlockMatrix, f: Double => Double ): BlockMatrix
      = new BlockMatrix(m.blocks.map{ case (i,a) => (i,new DenseMatrix(N,N,a.toArray.map(f))) },
                        m.rowsPerBlock,m.colsPerBlock)

    // matrix multiplication of tiled matrices in MLlib.linalg
    def testMultiplyMLlibDenseDense (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = A.multiply(B)
        val x = C.blocks.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of Sparse-Dense tiled matrices in MLlib.linalg
    def testMultiplyMLlibSparseDense (): Double = {
      val t = System.currentTimeMillis()
      try {
      val C = ASparse.multiply(B)
      val x = C.blocks.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of Sparse-Sparse tiled matrices in MLlib.linalg
    def testMultiplyMLlibSparseSparse (): Double = {
      val t = System.currentTimeMillis()
      try {
      val C = ASparse.multiply(BSparse)
      val x = C.blocks.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using Diablo array comprehensions (in RDD)
    def testMultiplyDiabloDAC (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n,n)[ ((i,j),+/c) | ((i,k),a) <- AA, ((kk,j),b) <- BB, k == kk, let c = a*b, group by (i,j) ]
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using Diablo array comprehensions (in DataFrame SQL)
    def testMultiplyDiabloDF (): Double = {
      param(data_frames,true)
      val t = System.currentTimeMillis()
      // generate DataFrame tiles from RDD tiles
      try {
        val C = q("""
                  tensor*(n,n)[ ((i,j),+/c) | ((i,k),a) <- AA, ((kk,j),b) <- BB, k == kk, let c = a*b, group by (i,j) ]
                  """)
        force(C._3)
      } catch { case x: Throwable => println(x); return -1.0 }
      param(data_frames,false)
      (System.currentTimeMillis()-t)/1000.0
    }

    def testMultiplyDiabloDF2 (): Double = {
      val aDF = (AA._1,AA._2,AA._3.toDF.asInstanceOf[DiabloDataFrame[((Int,Int),((Int,Int),EmptyTuple,Array[Double]))]])
      val bDF = (BB._1,BB._2,BB._3.toDF.asInstanceOf[DiabloDataFrame[((Int,Int),((Int,Int),EmptyTuple,Array[Double]))]])
      param(data_frames,true)
      val t = System.currentTimeMillis()
      // generate DataFrame tiles from DataFrame tiles
      try {
        val C = q("""
                  tensor*(n,n)[ ((i,j),+/c) | ((i,k),a) <- aDF, ((kk,j),b) <- bDF, k == kk, let c = a*b, group by (i,j) ]
                  """)
        force(C._3)
      } catch { case x: Throwable => println(x); return -1.0 }
      param(data_frames,false)
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using Diablo array comprehensions - no in-tile parallelism
    def testMultiplyDiabloDACs (): Double = {
      param(parallel,false)
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n,n)[ ((i,j),+/c) | ((i,k),a) <- AA, ((kk,j),b) <- BB, k == kk, let c = a*b, group by (i,j) ]
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      param(parallel,true)
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of sparse tiled matrices using Diablo array comprehensions
    def testMultiplyDiabloDACsparse (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n,n)[ ((i,j),+/c) | ((i,k),a) <- Az, ((kk,j),b) <- Bz, k == kk, let c = a*b, group by (i,j) ]
                  """)
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of sparse-dense tiled matrices using Diablo array comprehensions
    def testMultiplyDiabloDACsparseDense (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n,n)[ ((i,j),+/c) | ((i,k),a) <- Az, ((kk,j),b) <- BB, k == kk, let c = a*b, group by (i,j) ]
                  """)
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of dense tiled matrices giving a sparse matrix using Diablo array comprehensions
    def testMultiplyDiabloDACsparseOut (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n)(n)[ ((i,j),+/c) | ((i,k),a) <- AA, ((kk,j),b) <- BB, k == kk, let c = a*b, group by (i,j) ]
                  """)
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of sparse-dense tiled matrices giving a sparse matrix using Diablo array comprehensions
    def testMultiplyDiabloDACsparseDenseSparseOut (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n)(n)[ ((i,j),+/c) | ((i,k),a) <- Az, ((kk,j),b) <- BB, k == kk, let c = a*b, group by (i,j) ]
                  """)
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of sparse-sparse tiled matrices giving a sparse matrix using Diablo array comprehensions
    def testMultiplyDiabloDACsparseSparseSparseOut (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n)(n)[ ((i,j),+/c) | ((i,k),a) <- Az, ((kk,j),b) <- Bz, k == kk, let c = a*b, group by (i,j) ]
                  """)
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using Diablo groupBy-join on sparse matrices giving dense
    def testMultiplyDiabloGBJ (): Double = {
      val t = System.currentTimeMillis()
      param(groupByJoin,true)
      try {
        val C = q("""
                  tensor*(n,n)[ ((i,j),+/c) | ((i,k),a) <- Az, ((kk,j),b) <- Bz, k == kk, let c = a*b, group by (i,j) ]
                  """)
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      param(groupByJoin,false)
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using loops
    def testMultiplyDiabloLoop (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  var CC = tensor*(n,n)[ ((i,j),0.0) | i <- 0..n-1, j <- 0..n-1 ];

                  for i = 0, n-1 do
                     for k = 0, m-1 do
                        for j = 0, n-1 do
                           CC[i,j] += AA[i,k]*BB[k,j];
                  CC;
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using loops in DataFrame
    def testMultiplyDiabloLoopDF (): Double = {
      param(data_frames,true)
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  var CC = tensor*(n,n)[ ((i,j),0.0) | i <- 0..n-1, j <- 0..n-1 ];

                  for i = 0, n-1 do
                     for k = 0, m-1 do
                        for j = 0, n-1 do
                           CC[i,j] += AA[i,k]*BB[k,j];
                  CC;
                  """)
        param(data_frames,false)
        force(C._3)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices - hand-written
    def testMultiplyCode (): Double = {
      val t: Long = System.currentTimeMillis()
      try {
        val C = ((n,m),et,
                 AA._3.map{ case ((i,k),a) => (k,(i,a)) }
                       .join( BB._3.map{ case ((kk,j),b) => (kk,(j,b)) } )
                       .map{ case (_,((i,((na,ma),_,a)),(j,((nb,mb),_,b))))
                               => val V = Array.ofDim[Double](na*mb)
                                  for { i <- (0 until na).par } {
                                     var k = 0
                                     while (k<ma) {
                                       var j = 0
                                       while (j<mb) {
                                         V(i*mb+j) += a(i*ma+k)*b(k*mb+j)
                                         j += 1
                                       }
                                       k += 1
                                     }
                                  }
                                  ((i,j),((na,mb),et,V))
                           }
                       .reduceByKey{ (tx: ((Int,Int),EmptyTuple,Array[Double]),
                                      ty: ((Int,Int),EmptyTuple,Array[Double])) => (tx,ty) match {
                                     case (((nx,mx),_,x),(_,_,y))
                                       => val V = Array.ofDim[Double](nx*mx)
                                          for { i <- (0 until nx).par } {
                                             var j = 0
                                             while (j<mx) {
                                               V(i*mx+j) = x(i*mx+j)+y(i*mx+j)
                                               j += 1
                                             }
                                          }
                                          ((nx,mx),et,V)
                                   }})
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled MLlib matrices - hand-written
    def testMultiplyMLlibCode (): Double = {
      val t: Long = System.currentTimeMillis()
      try {
        val C = ((n,n),et,
                 Am.map{ case ((i,k),a) => (k,(i,a)) }
                       .join( Bm.map{ case ((kk,j),b) => (kk,(j,b)) } )
                       .map{ case (_,((i,a),(j,b)))
                               => ((i,j),a.multiply(b.asInstanceOf[DenseMatrix])) }
                       .reduceByKey{ ( x: DenseMatrix, y: DenseMatrix )
                                       => val V = Array.ofDim[Double](x.numRows*x.numCols)
                                          for { i <- (0 until x.numRows).par
                                                j <- 0 until x.numCols }
                                             V(i*x.numCols+j) = x(i,j)+y(i,j)
                                          new DenseMatrix(x.numRows,x.numCols,V) })
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled Breeze matrices - hand-written
    def testMultiplyBreezeCode (): Double = {
      import breeze.linalg._
      def randomTile ( nd: Int, md: Int ): DenseMatrix[Double] = {
        val max = 10
        val rand = new Random()
        new DenseMatrix(nd,md,Array.tabulate(nd*md){ i => rand.nextDouble()*max })
      }
      def randomMatrix ( rows: Int, cols: Int ): RDD[((Int, Int),DenseMatrix[Double])] = {
        val l = Random.shuffle((0 until (rows+N-1)/N).toList)
        val r = Random.shuffle((0 until (cols+N-1)/N).toList)
        spark_context.parallelize(for { i <- l; j <- r } yield (i,j))
            .map{ case (i,j) => ((i,j),randomTile(if ((i+1)*N > rows) rows%N else N,
                                                  if ((j+1)*N > cols) cols%N else N)) }
      }
      val Am = randomMatrix(n,m).cache()
      val Bm = randomMatrix(m,n).cache()
      val t: Long = System.currentTimeMillis()
      try {
        val C = ((n,n),et,
                 Am.map{ case ((i,k),a) => (k,(i,a)) }
                       .join( Bm.map{ case ((kk,j),b) => (kk,(j,b)) } )
                       .map{ case (_,((i,a),(j,b)))
                               => ((i,j),a*b) }
                       .reduceByKey(_+_))
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using groupBy-join - hand-written
    def testMultiplyCodeGBJ (): Double = {
      val t = System.currentTimeMillis()
      val cn = Math.ceil(n*1.0/N).toInt
      try {
        val C = ((n,n),et,
                 AA._3.flatMap{ case ((i,k),a) => (0 until cn).map(j => ((i,j),(k,a))) }
                  .cogroup( BB._3.flatMap{ case ((kk,j),b) => (0 until cn).map(i => ((i,j),(kk,b))) } )
                  .flatMap{ case ((ci,cj),(as,bs))
                              => if (as.isEmpty || bs.isEmpty)
                                   Nil
                                 else { val c = Array.ofDim[Double](N*N)
                                        var ns = 0; var ms = 0
                                        for { (k1,((na,ma),_,a)) <- as
                                              (k2,((nb,mb),_,b)) <- bs if k2 == k1
                                              i <- (0 until na).par } {
                                           var k = 0
                                           ns = na
                                           ms = mb
                                           while (k<ma && k<nb) {
                                             var j = 0
                                             while (j<mb) {
                                               c(i*ms+j) += a(i*ma+k)*b(k*mb+j)
                                               j += 1
                                             }
                                             k += 1
                                           }
                                        }
                                        List(((ci,cj),((ns,ms),et,Array.tabulate(ns*ms){ i => c(i) })))
                                      }
                                    })
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    val ADF = Am.map{ case ((i,j),v) => (i,j,v) }.toDF("I", "J", "TILE")
    val BDF = Bm.map{ case ((i,j),v) => (i,j,v) }.toDF("I", "J", "TILE")

    ADF.createOrReplaceTempView("A")
    BDF.createOrReplaceTempView("B")

    def mult_tiles ( a: DenseMatrix, b: DenseMatrix ): DenseMatrix
      = a.multiply(b.asInstanceOf[DenseMatrix])
    spark.udf.register("mult_tiles", udf(mult_tiles(_,_)))

    val sum_tiles =  new Aggregator[DenseMatrix,DenseMatrix,DenseMatrix] {
      def zero: DenseMatrix = new DenseMatrix(N,N,Array.ofDim[Double](N*N))
      def merge ( b1: DenseMatrix, b2: DenseMatrix ): DenseMatrix = {
        val c = b1.values
        for { i <- (0 until b1.numRows).par
              j <- 0 until b1.numCols
            } c(i*b1.numCols+j) += b2(i,j)
        new DenseMatrix(b1.numRows,b1.numCols,c)
      }
      def reduce ( a: DenseMatrix, b: DenseMatrix ): DenseMatrix = {
        val c = a.values
        for { i <- (0 until a.numRows).par if i < b.numRows
              j <- 0 until a.numCols if j < b.numCols
            } c(i*a.numCols+j) += b(i,j)
        new DenseMatrix(a.numRows,a.numCols,c)
      }
      def finish ( buf: DenseMatrix ): DenseMatrix = buf
      def bufferEncoder: Encoder[DenseMatrix] = ExpressionEncoder()
      def outputEncoder: Encoder[DenseMatrix] = ExpressionEncoder()
    }
    spark.udf.register("sum_tiles", udaf(sum_tiles))

    def testMultiplySQL (): Double = {
      var t = System.currentTimeMillis()
      try {
        val C = spark.sql(""" SELECT A.I, B.J, sum_tiles(mult_tiles(A.TILE,B.TILE)) AS TILE
                              FROM A JOIN B ON A.J = B.I
                              GROUP BY A.I, B.J
                          """)
        force(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def tile_sum ( a: Seq[DenseMatrix] ): DenseMatrix = {
      val nd = a.head.numRows
      val md = a.head.numCols
      val s = Array.ofDim[Double](nd*md)
      for { x <- a
            i <- (0 until nd).par
            j <- 0 until md }
        s(i*md+j) += x(i,j)
      new DenseMatrix(nd,md,s)
    }
    spark.udf.register("tile_sum", udf(tile_sum(_)))

    def testMultiplySQL2 (): Double = {
      var t = System.currentTimeMillis()
      try {
        val C = spark.sql(""" SELECT A.I, B.J, tile_sum(collect_list(mult_tiles(A.TILE,B.TILE))) AS TILE
                              FROM A JOIN B ON A.J = B.I
                              GROUP BY A.I, B.J
                          """)
        force(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    val tile_size = sizeof(((1,1),randomTile(N,N))).toDouble
    println("@@@ number of tiles: "+(n/N)+"*"+(m/N)+" = "+((n/N)*(m/N)))
    println("@@@@ dense matrix size: %.2f GB".format(tile_size*(n/N)*(m/N)/(1024.0*1024.0*1024.0)))
    val sparse_tile = q("tensor(N)(N)[ ((i,j),random()) | i <- 0..(N-1), j <- 0..(N-1), random() >  (1.0-sparsity)*10 ]")
    val sparse_tile_size = sizeof(sparse_tile).toDouble
    println("@@@@ sparsity: %.3f,  sparse matrix size: %.2f MB".format(sparsity,sparse_tile_size*(n/N)*(m/N)/(1024.0*1024.0)))

    def test ( name: String, f: => Double ) {
      val cores = Runtime.getRuntime().availableProcessors()
      var i = 0
      var j = 0
      var s = 0.0
      while ( i < repeats && j < 10 ) {
        val t = f
        j += 1
        if (t > 0.0) {   // if f didn't crash
          i += 1
          println("Try: "+i+"/"+j+" time: "+t)
          s += t
        }
      }
      if (i > 0) s = s/i
      print("*** %s cores=%d n=%d m=%d N=%d ".format(name,cores,n,m,N))
      println("tries=%d %.3f secs".format(i,s))
    }

    //test("DIABLO IJV Multiply",testMultiplyIJV)
    test("MLlib Multiply dense-dense",testMultiplyMLlibDenseDense)
    test("MLlib Multiply sparse-dense",testMultiplyMLlibSparseDense)
    test("MLlib Multiply sparse-sparse",testMultiplyMLlibSparseSparse)
    test("DIABLO Multiply",testMultiplyDiabloDAC)
    test("DIABLO Multiply SQL",testMultiplyDiabloDF)
    //test("DIABLO Multiply Sequential",testMultiplyDiabloDACs)
    test("DIABLO Multiply sparse-dense",testMultiplyDiabloDACsparseDense)
    test("DIABLO Multiply sparse-sparse",testMultiplyDiabloDACsparse)
    test("DIABLO Multiply sparse-sparse using groupby-join",testMultiplyDiabloGBJ)
    test("DIABLO Multiply dense-dense giving sparse",testMultiplyDiabloDACsparseOut)
    test("DIABLO Multiply sparse-dense giving sparse",testMultiplyDiabloDACsparseDenseSparseOut)
    test("DIABLO Multiply sparse-sparse giving sparse",testMultiplyDiabloDACsparseSparseSparseOut)
    test("DIABLO loop Multiply",testMultiplyDiabloLoop)
    test("DIABLO loop Multiply SQL",testMultiplyDiabloLoopDF)
    //test("Hand-written groupByJoin Multiply",testMultiplyCodeGBJ)
    test("Hand-written groupBy Multiply",testMultiplyCode)
    test("Hand-written groupBy MLlib Multiply",testMultiplyMLlibCode)
    //test("Hand-written groupBy Breeze Multiply",testMultiplyBreezeCode)
    test("SQL Multiply UDAF",testMultiplySQL)
    test("SQL Multiply UDF",testMultiplySQL2)

    spark_context.stop()
  }
}
