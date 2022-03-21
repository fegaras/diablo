import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import org.apache.spark.sql._
import org.apache.spark.sql.functions._
import org.apache.spark.sql.expressions.Aggregator
import org.apache.spark.sql.catalyst.encoders.ExpressionEncoder
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._
import org.apache.spark.ml.regression.LinearRegression
import org.apache.spark.ml.feature.LabeledPoint
import org.apache.spark.ml.linalg.Vectors
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
    val conf = new SparkConf().setAppName("linear_regression")
    spark_context = new SparkContext(conf)
	val spark = SparkSession.builder().config(conf).getOrCreate()
    import spark.implicits._
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.WARN)
	
    parami(number_of_partitions,100)
    parami(block_dim_size,1000)
    val repeats = args(0).toInt
    val N = 1000
	val validate = false
	
    val lrate = 1.0
    val total_size = args(1).toInt
    val n = (0.8*total_size).toInt
    val test_size = total_size-n
    val m = 100
    val numIter = 10
    val rand = new Random()
    val X_train = spark_context.textFile(args(2))
              .map( line => { val a = line.split(",").toList
              				((a(0).toInt,a(1).toInt),a(2).toDouble)} ).cache
    val y_train = spark_context.textFile(args(3))
              .map( line => { val a = line.split(",").toList
                             (a(0).toInt,a(1).toDouble)} ).cache
	val X_test = spark_context.textFile(args(4))
              .map( line => { val a = line.split(",").toList
              				((a(0).toInt,a(1).toInt),a(2).toDouble)} ).cache
    val y_test = spark_context.textFile(args(5))
              .map( line => { val a = line.split(",").toList
                             (a(0).toInt,a(1).toDouble)} ).cache
    
    def testDiabloLR(): Double = {
		var theta = spark_context.parallelize(0 to m-1).map(i => (i,1.0)).cache
    	val input1 = X_train
    	val output1 = y_train
    	val input2 = X_test
    	val output2 = y_test
		val A = q("tensor*(n,m)[((i,j),v) | ((i,j),v) <- input1 ]")
		A._3.cache
		val B = q("tensor*(n)[(i,v) | (i,v) <- output1]")
		B._3.cache
		var W = q("tensor*(m)[(i,v) | (i,v) <- theta]")
		W._3.cache
		val t = System.currentTimeMillis()
    	q("""
			var itr = 0;
			while (itr < numIter) {
				var x_theta = tensor*(n)[(i,+/v) | ((i,j),a) <- A, (jj,w) <- W, j==jj, let v=w*a, group by i];
				var x_theta_minus_y = tensor*(n)[(i,a-b) | (i,a) <- x_theta, (ii,b) <- B, i==ii];
				var d_theta = tensor*(m)[(j,+/v) | ((i,j),a) <- A, (ii,b) <- x_theta_minus_y, i==ii, let v=a*b, group by j];
				W = tensor*(m)[(i,a-(1.0/n)*lrate*b) | (i,a) <- W, (ii,b) <- d_theta, i==ii];
				cache(W);
			  	itr += 1;
			};
		""")
		if(validate) {
			val cost = q("""
				var A1 = tensor*(test_size,m)[((i,j),v) | ((i,j),v) <- input2];
				var B1 = tensor*(test_size)[(i,v) | (i,v) <- output2];
				var x_theta = tensor*(test_size)[(i,+/v) | ((i,j),a) <- A1, (jj,w) <- W, j==jj, let v=w*a, group by i];
				var x_theta_minus_y = tensor*(test_size)[(i,a-b) | (i,a) <- x_theta, (ii,b) <- B1, i==ii];
				var cost_val = +/[ v | (i, xty) <- x_theta_minus_y, let v = (0.5/test_size)*xty*xty];
				cost_val;
			""")
			println("Cost: "+cost)
		}
		W._3.count
	  	(System.currentTimeMillis()-t)/1000.0
    }

    def testMLlibLR(): Double = {
    	def vect ( a: Iterable[Double] ): org.apache.spark.ml.linalg.Vector = {
		  val s = Array.ofDim[Double](n*m)
		  var count = 0
		  for(x <- a) {
			s(count) = x
			count += 1
		  }
		  Vectors.dense(s)
		}

		// Load training data
		X_train.map{case ((i,j),v) => (i,v)}.groupByKey()
				.map{case (i,v) => (i, vect(v))}.toDF.createOrReplaceTempView("X_d")
		y_train.toDF.createOrReplaceTempView("Y_d")
		X_test.map{case ((i,j),v) => (i,v)}.groupByKey()
				.map{case (i,v) => (i, vect(v))}.toDF.createOrReplaceTempView("X_test_d")
		y_test.toDF.createOrReplaceTempView("Y_test_d")

		val training_data = spark.sql("select Y_d._2 as label, X_d._2 as features from X_d join Y_d on X_d._1=Y_d._1")
			.rdd.map{row => LabeledPoint(
		  	row.getAs[Double]("label"),
		  	row.getAs[org.apache.spark.ml.linalg.Vector]("features")
		)}.toDF.cache()

		val t = System.currentTimeMillis()
		val lr = new LinearRegression()
          .setMaxIter(numIter)
          .setFitIntercept(false)
          .setRegParam(1.0)

        val lrModel = lr.fit(training_data)
		println(lrModel.summary.meanSquaredError)
		if(validate) {
			val test_data = spark.sql("select Y_test_d._2 as label, X_test_d._2 as features from X_test_d join Y_test_d on X_test_d._1=Y_test_d._1")
				.rdd.map{row => LabeledPoint(
				row.getAs[Double]("label"),
				row.getAs[org.apache.spark.ml.linalg.Vector]("features")
			)}.toDF.cache()
			val predictions = lrModel.transform(test_data)
			predictions.rdd.count()
			println(lrModel.evaluate(test_data).meanSquaredError)
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
			  if(i > 1) s += t
			}
		}
		if (i > 0) s = s/(i-1)
		print("*** %s cores=%d n=%d m=%d N=%d ".format(name,cores,total_size,m,N))
		println("tries=%d %.3f secs".format(i,s))
    }

    test("Diablo Linear Regression",testDiabloLR)
    test("MLlib Linear Regression",testMLlibLR)

    spark_context.stop()
  }
}
