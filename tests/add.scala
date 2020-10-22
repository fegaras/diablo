import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._
import org.apache.log4j._
import org.apache.hadoop.fs._
import scala.util.Random
import Math._

object Add {
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
    parami(tileSize,1000) // each tile has size N*N
    val N = 1000
    val validate_output = false

    val conf = new SparkConf().setAppName("tiles")
    val spark_context = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.ERROR)

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

    val AA = (n,n,Am.map{ case ((i,j),a) => ((i,j),a.transpose.toArray) })
    val BB = (n,n,Bm.map{ case ((i,j),a) => ((i,j),a.transpose.toArray) })
    var CC = AA

    // matrix addition of tiled matrices in MLlib.linalg
    def testAddMLlib: Double = {
      val t = System.currentTimeMillis()
      try {
        val C = A.add(B)
        val x = C.blocks.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix addition of tiled matrices using Diablo array comprehensions
    def testAddDiabloDAC: Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tiled(n,m)[ ((i,j),m+n) | ((i,j),m) <- AA, ((ii,jj),n) <- BB, ii == i, jj == j ];
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix addition of tiled matrices using loops
    def testAddDiabloDACloop: Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  for i = 0, n-1 do
                     for j = 0, m-1 do
                        CC[i,j] = AA[i,j]+BB[i,j];
                  CC;
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    // matrix addition of tiled matrices using Diablo array comprehensions - no in-tile parallelism
    def testAddDiabloS: Double = {
      param(parallel,false)
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tiled(n,m)[ ((i,j),m+n) | ((i,j),m) <- AA, ((ii,jj),n) <- BB, ii == i, jj == j ]
                  """)
        validate(C)
      } catch { case x: Throwable => println(x); return -1.0 }
      param(parallel,true)
      (System.currentTimeMillis()-t)/1000.0
    }

    def validate ( M: (Int,Int,RDD[((Int,Int),Array[Double])]) ) {
      if (!validate_output)
        M._3.count()
      else {
        val C = A.add(B).toLocalMatrix()
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

    test("MLlib Add",testAddMLlib)
    test("DIABLO Add",testAddDiabloDAC)
    test("DIABLO loop Add",testAddDiabloDACloop)

    spark_context.stop()
  }
}
