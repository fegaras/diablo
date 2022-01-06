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
    val conf = new SparkConf().setAppName("tiles")
    val sc = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.WARN)
	
	parami(number_of_partitions,10)
    parami(block_dim_size,1000)
	val repeats = args(0).toInt
	val N = 1000
	
	val lrate = 0.0005
    val n = 900000
    val test_size = 100000
    val m = 100
    val numIter = args(1).toInt
    val rand = new Random()
    val X_train = sc.textFile(args(2))
              .map( line => { val a = line.split(",").toList
              				((a(0).toInt,a(1).toInt),a(2).toDouble)} ).cache
    val y_train = sc.textFile(args(3))
              .map( line => { val a = line.split(",").toList
                             (a(0).toInt,a(1).toDouble)} ).cache
	
	val X_test = sc.textFile(args(4))
              .map( line => { val a = line.split(",").toList
              				((a(0).toInt,a(1).toInt),a(2).toDouble)} ).cache
    val y_test = sc.textFile(args(5))
              .map( line => { val a = line.split(",").toList
                             (a(0).toInt,a(1).toDouble)} ).cache
	
	def testHandWrittenLoopLR(): Double = {
		val t = System.currentTimeMillis()
		val input = Array.tabulate(n*m){i => 0.0}
		for (((i,j),v) <- X_train.collect)
			input(i*m+j) = v
		val output = Array.tabulate(n){i => 0.0}
		for ((i,v) <- y_train.collect)
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
		val test_input = Array.tabulate(test_size*m){i => 0.0}
		for (((i,j),v) <- X_test.collect)
			test_input(i*m+j) = v
		val test_output = Array.tabulate(test_size){i => 0.0}
		for ((i,v) <- y_test.collect)
			test_output(i) = v
		var cost = 0.0
		for (i <- 0 until m) {
			for (j <- 0 until test_size) {
				var xt = 0.0
				for (k <- 0 until m) {
					xt += theta(k) * test_input(j*m+k)
				}
				cost += (0.5/test_size)*(xt - test_output(j)) * (xt - test_output(j))
			}
		}
		println("Cost: "+cost)
		(System.currentTimeMillis()-t)/1000.0
	}

    def testDiabloLoopLR(): Double = {
    	val t = System.currentTimeMillis()
    	var theta = sc.parallelize(0 to m-1).map(i => (i,1.0)).cache
    	val input1 = X_train
    	val output1 = y_train
    	val input2 = X_test
    	val output2 = y_test
    	val cost = q("""
			var A = tensor*(n)(m)[((i,j),v) | ((i,j),v) <- input1];
			var B = tensor*(n)[(i,v) | (i,v) <- output1];
			var W = tensor*(m)[(i,v) | (i,v) <- theta];
			var itr = 0;
			while(itr < numIter) {
				var x_theta = tensor*(n)[(i,0.0) | (i,v) <- output1];
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
			var A1 = tensor*(test_size)(m)[((i,j),v) | ((i,j),v) <- input2];
			var B1 = tensor*(test_size)[(i,v) | (i,v) <- output2];
			var cost_val = 0.0;
			var x_theta = tensor*(test_size)[(i,0.0) | (i,v) <- output2];
			var d_theta = tensor*(m)[(i,0.0) | (i,v) <- theta];
			for i = 0, test_size-1 do {
				for j = 0, m-1 do {
					x_theta[i] += W[j]*A1[i,j];
				}
				x_theta[i] -= B1[i];
				cost_val += (0.5/test_size)*x_theta[i]*x_theta[i];
			}
			cost_val;
		""")
		println("Cost: "+cost)
	  	(System.currentTimeMillis()-t)/1000.0
    }
    
    def testDiabloLR(): Double = {
    	val t = System.currentTimeMillis()
    	var theta = sc.parallelize(0 to m-1).map(i => (i,1.0)).cache
    	val input1 = X_train
    	val output1 = y_train
    	val input2 = X_test
    	val output2 = y_test
    	val cost = q("""
			var A = tensor*(n)(m)[((i,j),v) | ((i,j),v) <- input1];
			var B = tensor*(n)[(i,v) | (i,v) <- output1];
			var W = tensor*(m)[(i,v) | (i,v) <- theta];
			var itr = 0;
			while (itr < numIter) {
				var x_theta = tensor*(n)[(i,+/v) | ((i,j),a) <- A, (jj,w) <- W, j==jj, let v=w*a, group by i];
				var x_theta_minus_y = tensor*(n)[(i,a-b) | (i,a) <- x_theta, (ii,b) <- B, i==ii];
				var d_theta = tensor*(m)[(j,+/v) | ((i,j),a) <- A, (ii,b) <- x_theta_minus_y, i==ii, let v=a*b, group by j];
				W = tensor*(m)[(i,a-(1.0/n)*lrate*b) | (i,a) <- W, (ii,b) <- d_theta, i==ii];
			  	itr += 1;
			};
			var A1 = tensor*(test_size)(m)[((i,j),v) | ((i,j),v) <- input2];
			var B1 = tensor*(test_size)[(i,v) | (i,v) <- output2];
			var x_theta = tensor*(test_size)[(i,+/v) | ((i,j),a) <- A1, (jj,w) <- W, j==jj, let v=w*a, group by i];
			var x_theta_minus_y = tensor*(test_size)[(i,a-b) | (i,a) <- x_theta, (ii,b) <- B1, i==ii];
			var cost_val = +/[ v | (i, xty) <- x_theta_minus_y, let v = (0.5/test_size)*xty*xty];
			cost_val;
		""")
	  	println("Cost: "+cost)
	  	(System.currentTimeMillis()-t)/1000.0
    }
    
    def testMLlibLR(): Double = {
    	val t = System.currentTimeMillis()
    	var theta = new CoordinateMatrix(sc.parallelize(0 to m-1).map(i => MatrixEntry(i,0,1.0))).toBlockMatrix(N,1).cache
    	val input1 = new CoordinateMatrix(X_train.map{ case ((i,j),v) => MatrixEntry(i,j,v)}).toBlockMatrix(N,N).cache
		val output1 = new CoordinateMatrix(y_train.map{ case (i,v) => MatrixEntry(i,0,v)}).toBlockMatrix(N,1).cache
		for(itr <- 0 until numIter) {
			val x_theta_minus_y = input1.multiply(theta).subtract(output1)
			var d_theta = input1.transpose.multiply(x_theta_minus_y)
			d_theta = new CoordinateMatrix(d_theta.toCoordinateMatrix().entries
							.map(entry => MatrixEntry(entry.i, entry.j, entry.value * lrate * (1.0/n)))).toBlockMatrix(N,1).cache
			theta = theta.subtract(d_theta)
		}
		val input2 = new CoordinateMatrix(X_test.map{ case ((i,j),v) => MatrixEntry(i,j,v)}).toBlockMatrix(N,N).cache
		val output2 = new CoordinateMatrix(y_test.map{ case (i,v) => MatrixEntry(i,0,v)}).toBlockMatrix(N,1).cache
		val x_theta_minus_y = input2.multiply(theta).subtract(output2)
		val cost = x_theta_minus_y.toCoordinateMatrix().entries
						.map(e => (0.5/n)*e.value*e.value).reduce(_+_)
	  	println("Cost: "+cost)
	  	(System.currentTimeMillis()-t)/1000.0
    }

    val spark = SparkSession.builder().config(conf).getOrCreate()
    import spark.implicits._

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
    test("Diablo loop Linear Regression",testDiabloLoopLR)
    test("Diablo Linear Regression",testDiabloLR)
    test("MLlib Linear Regression",testMLlibLR)
    
    sc.stop()
  }
}