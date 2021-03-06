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


object Multiply extends Serializable {
  /* The size of any serializable object */
  def sizeof ( x: Serializable ): Int = {
    import java.io.{ByteArrayOutputStream,ObjectOutputStream}
    val bs = new ByteArrayOutputStream()
    val os = new ObjectOutputStream(bs)
    os.writeObject(x)
    os.flush()
    os.close()
    bs.toByteArray().length
  }

  def main ( args: Array[String] ) {
    val repeats = args(0).toInt
    val n = args(1).toInt   // each matrix has n*n elements
    val m = n
    parami(block_dim_size,1000)  // size of each dimension
    val N = 1000
    val validate_output = false

    val conf = new SparkConf().setAppName("tiles")
    spark_context = new SparkContext(conf)
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

    def randomTile (): DenseMatrix = {
      val max = 10
      val rand = new Random()
      new DenseMatrix(N,N,Array.tabulate(N*N){ i => rand.nextDouble()*max })
    }

    def randomMatrix ( rows: Int, cols: Int ): RDD[((Int, Int),org.apache.spark.mllib.linalg.Matrix)] = {
      val l = Random.shuffle((0 until (rows+N-1)/N).toList)
      val r = Random.shuffle((0 until (cols+N-1)/N).toList)
      spark_context.parallelize(for { i <- l; j <- r } yield (i,j))
        .map{ case (i,j) => ((i,j),randomTile()) }
    }

    val Am = randomMatrix(n,m).cache()
    val Bm = randomMatrix(n,m).cache()

    val A = new BlockMatrix(Am,N,N)
    val B = new BlockMatrix(Bm,N,N)

    type tiled_matrix = (Int,Int,RDD[((Int,Int),(Int,Int,Array[Double]))])

    // dense block tensors
    val AA = (n,m,Am.map{ case ((i,j),a) => ((i,j),(N,N,a.transpose.toArray)) })
    val BB = (n,m,Bm.map{ case ((i,j),a) => ((i,j),(N,N,a.transpose.toArray)) })
    var CC = AA

    // sparse block tensors with no zeros
    val As = q("tensor*(n)(m)[ ((i,j),a) | ((i,j),a) <- AA ]")
    val Bs = q("tensor*(n)(m)[ ((i,j),b) | ((i,j),b) <- BB ]")

    val rand = new Random()
    def random () = rand.nextDouble()*10

    val Az = q("tensor*(n)(m)[ ((i,j),random()) | i <- 0..(n-1), j <- 0..(m-1), random() > 9.9 ]")
    val Bz = q("tensor*(n)(m)[ ((i,j),random()) | i <- 0..(n-1), j <- 0..(m-1), random() > 9.9 ]")

    def validate ( M: tiled_matrix ) {
      if (!validate_output)
        M._3.count()
      else {
        val C = A.multiply(B).toLocalMatrix()
        val CC = M._3.collect
        println("Validating ...")
        for { ((ii,jj),(_,_,a)) <- CC
              i <- 0 until N
              j <- 0 until N }
           if (ii*N+i < M._1 && jj*N+j < M._2
               && Math.abs(a(i*N+j)-C(ii*N+i,jj*N+j)) > 0.01)
             println("Element (%d,%d)(%d,%d) is wrong: %.3f %.3f"
                     .format(ii,jj,i,j,a(i*N+j),C(ii*N+i,jj*N+j)))
      }
    }

    def map ( m: BlockMatrix, f: Double => Double ): BlockMatrix
      = new BlockMatrix(m.blocks.map{ case (i,a) => (i,new DenseMatrix(N,N,a.toArray.map(f))) },
                        m.rowsPerBlock,m.colsPerBlock)

    // matrix multiplication of tiled matrices in MLlib.linalg
    def testMultiplyMLlib (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = A.multiply(B)
        val x = C.blocks.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using Diablo array comprehensions
    def testMultiplyDiabloDAC (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n,m)[ ((i,j),+/c) | ((i,k),a) <- AA, ((kk,j),b) <- BB, k == kk, let c = a*b, group by (i,j) ]
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using Diablo array comprehensions - no in-tile parallelism
    def testMultiplyDiabloDACs (): Double = {
      param(parallel,false)
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n,m)[ ((i,j),+/c) | ((i,k),a) <- AA, ((kk,j),b) <- BB, k == kk, let c = a*b, group by (i,j) ]
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
                  tensor*(n,m)[ ((i,j),+/c) | ((i,k),a) <- Az, ((kk,j),b) <- Bz, k == kk, let c = a*b, group by (i,j) ]
                  """)
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using loops
    def testMultiplyDiabloLoop (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  for i = 0, n-1 do
                     for j = 0, n-1 do {
                         CC[i,j] = 0.0;
                         for k = 0, n-1 do
                             CC[i,j] += AA[i,k]*BB[k,j];
                     };
                  CC;
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices - hand-written
    def testMultiplyCode (): Double = {
      val t: Long = System.currentTimeMillis()
      try {
        val C = (n,m,AA._3.map{ case ((i,k),(_,_,a)) => (k,(i,a)) }
                       .join( BB._3.map{ case ((kk,j),(_,_,b)) => (kk,(j,b)) } )
                       .map{ case (_,((i,a),(j,b)))
                               => val V = Array.ofDim[Double](N*N)
                                  for { i <- (0 until N).par } {
                                     var k = 0
                                     while (k<N) {
                                       var j = 0
                                       while (j<N) {
                                         V(i*N+j) += a(i*N+k)*b(k*N+j)
                                         j += 1
                                       }
                                       k += 1
                                     }
                                  }
                                  ((i,j),V)
                           }
                       .reduceByKey{ case (x,y)
                                       => val V = Array.ofDim[Double](N*N)
                                          for { i <- (0 until N).par } {
                                             var j = 0
                                             while (j<N) {
                                               V(i*N+j) = x(i*N+j)+y(i*N+j)
                                               j += 1
                                             }
                                          }
                                          V
                                   }
                       .map{ case (k,v) => (k,(N,N,v)) })
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled MLlib matrices - hand-written
    def testMultiplyMLlibCode (): Double = {
      val t: Long = System.currentTimeMillis()
      try {
        val C = (n,m,Am.map{ case ((i,k),a) => (k,(i,a)) }
                       .join( Bm.map{ case ((kk,j),b) => (kk,(j,b)) } )
                       .map{ case (_,((i,a),(j,b)))
                               => ((i,j),a.multiply(b.asInstanceOf[DenseMatrix])) }
                       .reduceByKey{ case (x,y)
                                       => val V = Array.ofDim[Double](N*N)
                                          for { i <- (0 until N).par
                                                j <- 0 until N }
                                             V(i*N+j) = x(i,j)+y(i,j)
                                          new DenseMatrix(N,N,V) })
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled Breeze matrices - hand-written
    def testMultiplyBreezeCode (): Double = {
      import breeze.linalg._
      def randomTile (): DenseMatrix[Double] = {
        val max = 10
        val rand = new Random()
        new DenseMatrix(N,N,Array.tabulate(N*N){ i => rand.nextDouble()*max })
      }
      def randomMatrix ( rows: Int, cols: Int ): RDD[((Int, Int),DenseMatrix[Double])] = {
        val l = Random.shuffle((0 until (rows+N-1)/N).toList)
        val r = Random.shuffle((0 until (cols+N-1)/N).toList)
        spark_context.parallelize(for { i <- l; j <- r } yield (i,j))
          .map{ case (i,j) => ((i,j),randomTile()) }
      }
      val Am = randomMatrix(n,m).cache()
      val Bm = randomMatrix(n,m).cache()
      val t: Long = System.currentTimeMillis()
      try {
        val C = (n,m,Am.map{ case ((i,k),a) => (k,(i,a)) }
                       .join( Bm.map{ case ((kk,j),b) => (kk,(j,b)) } )
                       .map{ case (_,((i,a),(j,b)))
                               => ((i,j),a*b) }
                       .reduceByKey{ case (x,y) => x+y })
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using groupBy-join - hand-written
    def testMultiplyCodeGBJ (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = (n,m,AA._3.flatMap{ case ((i,k),(_,_,a)) => (0 until n/N).map(j => ((i,j),(k,a))) }
                          .cogroup( BB._3.flatMap{ case ((k,j),(_,_,b)) => (0 until n/N).map(i => ((i,j),(k,b))) } )
                          .mapValues{ case (as,bs)
                                     => val c = Array.ofDim[Double](N*N)
                                        for { (k1,a) <- as
                                              (k2,b) <- bs if k2 == k1
                                              i <- (0 until N).par } {
                                           var k = 0
                                           while (k<N) {
                                             var j = 0
                                             while (j<N) {
                                               c(i*N+j) += a(i*N+k)*b(k*N+j)
                                               j += 1
                                             }
                                             k += 1
                                           }
                                        }
                                        (N,N,c)
                                    })
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    val spark = SparkSession.builder().config(conf).getOrCreate()
    import spark.implicits._

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
        for { i <- (0 until N).par
              j <- 0 until N
            } c(i*N+j) += b2(i,j)
        new DenseMatrix(N,N,c)
      }
      def reduce ( buf: DenseMatrix, a: DenseMatrix ): DenseMatrix = {
        val c = buf.values
        for { i <- (0 until N).par
              j <- 0 until N
            } c(i*N+j) += a(i,j)
        new DenseMatrix(N,N,c)
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
        //println(C.queryExecution)
        val result = new BlockMatrix(C.rdd.map{ case Row( i:Int, j: Int, m: DenseMatrix ) => ((i,j),m) },N,N)
        result.blocks.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def tile_sum ( a: Seq[DenseMatrix] ): DenseMatrix = {
      val s = Array.ofDim[Double](N*N)
      for { x <- a
            i <- (0 until N).par
            j <- 0 until N }
        s(i*N+j) += x(i,j)
      new DenseMatrix(N,N,s)
    }
    spark.udf.register("tile_sum", udf(tile_sum(_)))

    def testMultiplySQL2 (): Double = {
      var t = System.currentTimeMillis()
      try {
        val C = spark.sql(""" SELECT A.I, B.J, tile_sum(collect_list(mult_tiles(A.TILE,B.TILE))) AS TILE
                              FROM A JOIN B ON A.J = B.I
                              GROUP BY A.I, B.J
                          """)
        //println(C.queryExecution)
        val result = new BlockMatrix(C.rdd.map{ case Row( i:Int, j: Int, m: DenseMatrix ) => ((i,j),m) },N,N)
        result.blocks.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    println("@@@@ IJV matrix size: %.2f GB".format(sizeof(((1,1),0.0D)).toDouble*n*m/(1024.0*1024.0*1024.0)))
    val tile_size = sizeof(((1,1),randomTile())).toDouble
    println("@@@@ tile matrix size: %.2f GB".format(tile_size*(n/N)*(m/N)/(1024.0*1024.0*1024.0)))
    println("@@@@ sparse partition sizes: "+Az._3.map{ case (_,(_,_,(_,a,_))) => a.length }.collect.toList)

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
      print("*** %s cores=%d n=%d N=%d ".format(name,cores,n,N))
      println("tries=%d %.3f secs".format(i,s))
    }

    //test("DIABLO IJV Multiply",testMultiplyIJV)
    test("MLlib Multiply",testMultiplyMLlib)
    test("DIABLO groupByJoin Multiply",testMultiplyDiabloDAC)
    //test("DIABLO groupByJoin Multiply sequential",testMultiplyDiabloDACs)
    test("DIABLO Multiply sparse",testMultiplyDiabloDACsparse)
    test("DIABLO loop Multiply",testMultiplyDiabloLoop)
    test("Hand-written groupByJoin Multiply",testMultiplyCodeGBJ)
    test("Hand-written groupBy Multiply",testMultiplyCode)
    test("Hand-written groupBy MLlib Multiply",testMultiplyMLlibCode)
    test("Hand-written groupBy Breeze Multiply",testMultiplyBreezeCode)
    test("SQL Multiply UDAF",testMultiplySQL)
    test("SQL Multiply UDF",testMultiplySQL2)

    spark_context.stop()
  }
}
