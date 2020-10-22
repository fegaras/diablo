import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._
import org.apache.log4j._
import org.apache.hadoop.fs._
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
    val gbj = args(2) == "1"  // groupByJoin only
    parami(tileSize,1000) // each tile has size N*N
    val N = 1000
    val validate_output = false

    val conf = new SparkConf().setAppName("tiles")
    val spark_context = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.ERROR)

    def randomIJVMatrix ( n: Int, m: Int ): RDD[((Int,Int),Double)] = {
      val max = 10
      val l = Random.shuffle((0 until n).toList)
      val r = Random.shuffle((0 until m).toList)
      spark_context.parallelize(l)
        .flatMap{ i => val rand = new Random()
                       r.map{ j => ((i.toInt,j.toInt),rand.nextDouble()*max) } }
        .cache()
    }

    val MM = randomIJVMatrix(n,m)
    val NN = randomIJVMatrix(n,m)

    def testMultiplyIJV(): Double = {
      // matrix multiplication of IJV matrices using Diablo array comprehensions
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  rdd[ ((i,j),+/v) | ((i,k),m) <- MM, ((kk,j),n) <- NN, let v = m*n, k == kk, group by (i,j) ]
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

    val AA = (n,m,Am.map{ case ((i,j),a) => ((i,j),a.transpose.toArray) })
    val BB = (n,m,Bm.map{ case ((i,j),a) => ((i,j),a.transpose.toArray) })
    var CC = AA

    def map ( m: BlockMatrix, f: Double => Double ): BlockMatrix
      = new BlockMatrix(m.blocks.map{ case (i,a) => (i,new DenseMatrix(N,N,a.toArray.map(f))) },
                        m.rowsPerBlock,m.colsPerBlock)

    // matrix multiplication of tiled matrices in MLlib.linalg
    def testMultiplyMLlib(): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = A.multiply(B)
        val x = C.blocks.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using Diablo array comprehensions
    def testMultiplyDiabloDAC(): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tiled(n,m)[ ((i,j),+/c) | ((i,k),m) <- AA, ((kk,j),n) <- BB, k == kk, let c = m*n, group by (i,j) ]
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using Diablo array comprehensions - no in-tile parallelism
    def testMultiplyDiabloDACs(): Double = {
      param(parallel,false)
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tiled(n,m)[ ((i,j),+/c) | ((i,k),m) <- AA, ((kk,j),n) <- BB, k == kk, let c = m*n, group by (i,j) ]
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      param(parallel,true)
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using Diablo array comprehensions - no groupBy-join
    def testMultiplyDiabloDACn(): Double = {
      param(groupByJoin,false)
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tiled(n,m)[ ((i,j),+/c) | ((i,k),m) <- AA, ((kk,j),n) <- BB, k == kk, let c = m*n, group by (i,j) ]
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      param(groupByJoin,true)
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using loops
    def testMultiplyDiabloLoop(): Double = {
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

    def mult ( x: Array[Double], y: Array[Double] ): Array[Double] = {
       val V = Array.ofDim[Double](N*N)
       for { i <- (0 until N).par }
           for { j <- 0 until N }
               for { k <- 0 until N }
                   V(i*N+j) += x(i*N+k)*y(k*N+j)
       V
    }

    def add ( x: Array[Double], y: Array[Double] ): Array[Double] = {
       val V = Array.ofDim[Double](N*N)
       for { i <- (0 until N).par
             j <- 0 until N }
           V(i*N+j) = x(i*N+j)+y(i*N+j)
       V
    }

    // matrix multiplication of IJV matrices - hand-written
    def testMultiplyCodeIJV (): Double = {
      val t: Long = System.currentTimeMillis()
      try {
        val C = (n,m,AA._3.map{ case ((i,k),a) => (k,(i,a)) }
                       .join( BB._3.map{ case ((kk,j),b) => (kk,(j,b)) } )
                       .map{ case (_,((i,a),(j,b))) => ((i,j),mult(a,b)) }
                       .reduceByKey(add))
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix multiplication of tiled matrices using groupBy-join - hand-written
    def testMultiplyCode (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = (n,m,AA._3.flatMap{ case ((i,k),a) => (0 until n/N).map(j => ((i,j),(k,a))) }
                          .cogroup( BB._3.flatMap{ case ((k,j),b) => (0 until n/N).map(i => ((i,j),(k,b))) } )
                          .mapValues{ case (as,bs)
                                     => val c = Array.ofDim[Double](N*N)
                                        for { (k1,a) <- as
                                              (k2,b) <- bs if k2 == k1
                                              i <- (0 until N).par
                                              k <- 0 until N
                                              j <- 0 until N
                                            } c(i*N+j) += a(i*N+k)*b(k*N+j)
                                   c
                                 })
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def validate ( M: (Int,Int,RDD[((Int,Int),Array[Double])]) ) {
      if (!validate_output)
        M._3.count()
      else {
        val C = A.multiply(B).toLocalMatrix()
        val MM = M._3.collect
        for { ((ii,jj),a) <- MM;
              i <- 0 until N;
              j <- 0 until N }
           if (ii*N+i < M._1 && jj*N+j < M._2
               && Math.abs(a(i*N+j)-C(ii*N+i,jj*N+j)) > 0.01)
             println("Element (%d,%d)(%d,%d) is wrong: %.3f %.3f"
                     .format(ii,jj,i,j,a(i*N+j),C(ii*N+i,jj*N+j)))
      }
    }

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
      print("*** %s cores=%d n=%d N=%d %.2f GB ".format(name,cores,n,N,(8.0*n.toDouble*n)/(1024.0*1024.0*1024.0)))
      println("tries=%d %.3f secs".format(i,s))
    }

    //test("DIABLO IJV Multiply",testMultiplyIJV)
    test("MLlib Multiply",testMultiplyMLlib)
    test("DIABLO groupByJoin Multiply",testMultiplyDiabloDAC)
    test("DIABLO groupByJoin Multiply sequential",testMultiplyDiabloDACs)
    test("DIABLO groupBy Multiply",testMultiplyDiabloDACn)
    test("DIABLO loop Multiply",testMultiplyDiabloLoop)
    test("Hand-written groupByJoin Multiply",testMultiplyCode)
    
/*
    if (!gbj) {
      test("MLlib Multiply",testMultiplyMLlib)
      test("DIABLO groupBy Multiply",testMultiplyDiabloDACn)
    }
    test("DIABLO groupByJoin Multiply",testMultiplyDiabloDAC)
*/
    spark_context.stop()
  }
}
