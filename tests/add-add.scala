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


object AddAdd {
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

    val rand = new Random()
    def random () = rand.nextDouble()*10

    val AA = q("tensor*(n,n)[ ((i,j),random()) | i <- 1..n, j <- 1..n ]")
    val BB = q("tensor*(n,n)[ ((i,j),random()) | i <- 1..n, j <- 1..n ]")
    val CC = q("tensor*(n,n)[ ((i,j),random()) | i <- 1..n, j <- 1..n ]")


    def testAddAdd (): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = q("""
                  tensor*(n,n)[ ((i,j),a+b+c) | ((i,j),a) <= AA, ((ii,jj),b) <= BB, ((iii,jjj),c) <- CC,
                                              ii==i, jj==j, iii==i, jjj==j ]
                  """)
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testAddAddN (): Double = {
      val t = System.currentTimeMillis()
      param(mapPreserve,false)
      try {
        val C = q("""
                  tensor*(n,n)[ ((i,j),a+b+c) | ((i,j),a) <= AA, ((ii,jj),b) <= BB, ((iii,jjj),c) <- CC,
                                              ii==i, jj==j, iii==i, jjj==j ]
                  """)
        C._3.count()
      } catch { case x: Throwable => println(x); return -1.0 }
      param(mapPreserve,true)
      (System.currentTimeMillis()-t)/1000.0
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
      print("*** %s cores=%d n=%d m=%d N=%d ".format(name,cores,n,m,N))
      println("tries=%d %.3f secs".format(i,s))
    }


    test("add/add with preserves",testAddAdd)
    test("add/add",testAddAddN)

    spark_context.stop()
  }
}
