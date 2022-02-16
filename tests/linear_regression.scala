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


object LinearRegression extends Serializable {
  /* The size of an object */
  def sizeof ( x: AnyRef ): Long = {
    import org.apache.spark.util.SizeEstimator.estimate
    estimate(x)
  }

  def main ( args: Array[String] ) {
    val conf = new SparkConf().setAppName("tiles")
    val sc = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.WARN)
    val spark = SparkSession.builder().config(conf).getOrCreate()
    import spark.implicits._

    parami(number_of_partitions,10)
    parami(block_dim_size,1000)
    param(data_frames,false)

    val repeats = args(0).toInt
    val N = 1000
	
    val lrate = 0.0005
    val n = args(1).toInt
    val m = args(2).toInt
    val numIter = args(3).toInt
    val rand = new Random()
    val X = sc.textFile(args(4))
              .map( line => { val a = line.split(",").toList
              				if(rand.nextDouble() > 0.99) ((a(0).toInt,a(1).toInt),a(2).toDouble)
              				else ((a(0).toInt,a(1).toInt), 0.0) } ).cache
    val y = sc.textFile(args(5))
              .map( line => { val a = line.split(",").toList
                             if(rand.nextDouble() > 0.99) (a(0).toInt,a(1).toDouble) 
                             else (a(0).toInt,0.0) } ).cache
	
    def testHandWrittenLoopLR(): Double = {
      val t = System.currentTimeMillis()
      val input = Array.tabulate(n*m){i => 0.0}
      for (((i,j),v) <- X.collect)
          input(i*m+j) = v
      val output = Array.tabulate(n){i => 0.0}
      for ((i,v) <- y.collect)
	  	output(i) = v
      var theta = Array.tabulate(m){i => 1.0}
      for (itr <- 0 until numIter) {
	  	var dev_sum = Array.tabulate(m){i => 0.0}
	  	for (i <- 0 until m) {
	  		for (j <- 0 until n) {
	  			var xt = 0.0
	  			for (k <- 0 until m) {
	  				xt += theta(k) * input(j*m+k)
	  			}
	  			dev_sum(i) += (xt - output(j)) * input(j*m+i)
	  		}
	  	}
	  	for (i <- 0 until m) {
	  		theta(i) -= (1.0 / n) * lrate * dev_sum(i)
	  	}
	  }
	  //println("Theta: ")
	  //theta.map(println)
	  (System.currentTimeMillis()-t)/1000.0
	}
/*
    def testDiabloLoopLR(): Double = {
    	var theta = sc.parallelize(0 to m-1).map(i => (i,1.0)).cache
        val A = q("tensor*(n,m)[((i,j),v) | ((i,j),v) <- input]")
        val B = q("tensor*(n)[(i,v) | (i,v) <- output]")
        val W = q("tensor*(m)[(i,v) | (i,v) <- theta]")
    	val input = X
    	val output = y
    	val t = System.currentTimeMillis()
    	val theta1 = q("""
			var itr = 0;
			while(itr < numIter) {
				var x_theta = tensor*(n)[(i,0.0) | (i,v) <- output];
				var d_theta = tensor*(m)[(i,0.0) | (i,v) <- theta];
				for i = 0, n-1 do {
					for j = 0, m-1 do {
						x_theta[i] += W[j]*A[i,j];
					}
					x_theta[i] -= B[i];
				}
				for i = 0, m-1 do {
					for j = 0, n-1 do {
						d_theta[i] += x_theta[j]*A[j,i];
					}
					W[i] -= (1.0/n)*lrate*d_theta[i];
				}
				itr += 1;
			}
			W; // rdd[(i,v) | (i,v) <- W];
		""")
		//println("Theta:")
	  	theta1._2.rdd.count()
	  	(System.currentTimeMillis()-t)/1000.0
    }
*/
    def testDiabloLR(): Double = {
    	var theta = sc.parallelize(0 to m-1).map(i => (i,1.0)).cache
    	val input = X
    	val output = y
        val A = q("tensor*(n,m)[((i,j),v) | ((i,j),v) <- input]")
	val B = q("tensor*(n)[(i,v) | (i,v) <- output]")
	var W = q("tensor*(m)[(i,v) | (i,v) <- theta]")
        A._3.cache; B._3.cache; W._3.cache
    	val t = System.currentTimeMillis()
    	val theta1 = q("""
			var itr = 0;
			while (itr < numIter) {
				var x_theta = tensor*(n)[(i,+/v) | ((i,j),a) <- A, (jj,w) <- W, j==jj, let v=w*a, group by i];
				var x_theta_minus_y = tensor*(n)[(i,a-b) | (i,a) <- x_theta, (ii,b) <- B, i==ii];
				var d_theta = tensor*(m)[(j,+/v) | ((i,j),a) <- A, (ii,b) <- x_theta_minus_y, i==ii, let v=a*b, group by j];
				W = tensor*(m)[(i,a-(1.0/n)*lrate*b) | (i,a) <- W, (ii,b) <- d_theta, i==ii];
			  	itr += 1;
                                cache(W);
			};
			W;
		""")
	  //println("Theta: ")
	  theta1._3.count()
	  (System.currentTimeMillis()-t)/1000.0
    }
    
    def testMLlibLR(): Double = {
    	var theta = new CoordinateMatrix(sc.parallelize(0 to m-1).map(i => MatrixEntry(i,0,1.0))).toBlockMatrix(N,1).cache
    	val input = new CoordinateMatrix(X.map{ case ((i,j),v) => MatrixEntry(i,j,v)}).toBlockMatrix(N,N).cache
        val output = new CoordinateMatrix(y.map{ case (i,v) => MatrixEntry(i,0,v)}).toBlockMatrix(N,1).cache
    	val t = System.currentTimeMillis()
		for(itr <- 0 until numIter) {
			var d_theta = input.transpose.multiply(input.multiply(theta).subtract(output))
			d_theta = new CoordinateMatrix(d_theta.toCoordinateMatrix().entries.map(entry => MatrixEntry(entry.i,entry.j,entry.value*lrate*(1.0/n)))).toBlockMatrix(N,1).cache
			theta = theta.subtract(d_theta)
		}
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
      print("*** %s cores=%d N=%d ".format(name,cores,N))
      println("tries=%d %.3f secs".format(i,s))
    }

    test("Handwritten-Loop Linear Regression",testHandWrittenLoopLR)
    //test("Diablo loop Linear Regression",testDiabloLoopLR)
    test("Diablo Linear Regression",testDiabloLR)
    test("MLlib Linear Regression",testMLlibLR)
    
    sc.stop()
  }
}
