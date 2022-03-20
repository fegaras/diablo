import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import org.apache.spark.sql._
import org.apache.spark.sql.functions._
import org.apache.spark.sql.expressions.Aggregator
import org.apache.spark.sql.catalyst.encoders.ExpressionEncoder
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._
import org.apache.spark.ml.classification.LogisticRegression
import org.apache.spark.ml.feature.LabeledPoint
import org.apache.spark.ml.linalg.Vectors
import org.apache.spark.ml.evaluation.BinaryClassificationEvaluator
import org.apache.log4j._
import org.apache.hadoop.fs._
import scala.collection.Seq
import scala.util.Random
import Math._

object NeuralNetwork extends Serializable {
	/* The size of an object */
	def sizeof ( x: AnyRef ): Long = {
		import org.apache.spark.util.SizeEstimator.estimate
		estimate(x)
	}

	def main ( args: Array[String] ) {
		val conf = new SparkConf().setAppName("neural_network")
		spark_context = new SparkContext(conf)
		conf.set("spark.logConf","false")
		conf.set("spark.eventLog.enabled","false")
		LogManager.getRootLogger().setLevel(Level.WARN)
		
		parami(number_of_partitions,100)
		parami(block_dim_size,1000)
		val repeats = args(0).toInt
		val N = 1000
		val validate = false
		
		val learning_rate = 2.0
		val total_size = args(1).toInt
		val n = (0.8*total_size).toInt
		val test_size = total_size - n
		val m = 3
		val epochs = 10

		val input1 = spark_context.textFile(args(2))
		          .map( line => { val a = line.split(",").toList
		          				((a(0).toInt,a(1).toInt),a(2).toDouble)} ).cache
		val input2 = spark_context.textFile(args(3))
		          .map( line => { val a = line.split(",").toList
		                         (a(0).toInt,a(1).toDouble) } ).cache
		val input3 = spark_context.textFile(args(4))
		          .map( line => { val a = line.split(",").toList
		          				((a(0).toInt,a(1).toInt),a(2).toDouble) } ).cache
		val input4 = spark_context.textFile(args(5))
		          .map( line => { val a = line.split(",").toList
		                         (a(0).toInt,a(1).toDouble) } ).cache
		
		val X = Array.tabulate(n*m){i => 0.0}
		for (((i,j),v) <- input1.collect)
			X(i*m+j) = v
		val Y = Array.tabulate(n){i => 0.0}
		for ((i,v) <- input2.collect)
			Y(i) = v
		val X_test = Array.tabulate(test_size*m){i => 0.0}
		for (((i,j),v) <- input3.collect)
			X_test(i*m+j) = v
		val Y_test = Array.tabulate(test_size){i => 0.0}
		for ((i,v) <- input4.collect)
			Y_test(i) = v

		val nn_architecture = List((m, 8), (8, 1))
		
		def mat_multiply(A: Array[Double], B: Array[Double], a_n:Int, a_m:Int, b_m:Int): Array[Double] = {
			var res = Array.tabulate(a_n*b_m){i => 0.0}
			for (i <- 0 until a_n) {
		  		for (j <- 0 until b_m) {
		  			var xt = 0.0
		  			for (k <- 0 until a_m) {
		  				xt += A(i*a_m+k) * B(k*b_m+j)
		  			}
		  			res(i*b_m+j) += xt
		  		}
		  	}
		  	res
		}
		
		def mat_add(A: Array[Double], B: Array[Double], a_n:Int, a_m:Int): Array[Double] = {
			var res = Array.tabulate(a_n*a_m){i => 0.0}
			for (i <- 0 until a_n) {
		  		for (j <- 0 until a_m) {
		  			res(i*a_m+j) = A(i*a_m+j) + B(i)
		  		}
		  	}
		  	res
		}
		
		def mat_transpose(A: Array[Double], a_n: Int, a_m: Int): Array[Double] = {
			var res = Array.tabulate(a_n*a_m){i => 0.0}
			for (i <- 0 until a_n) {
		  		for (j <- 0 until a_m) {
		  			res(j*a_n+i) = A(i*a_m+j)
		  		}
		  	}
		  	res
		}
		
		def ln(x: Double): Double = math.log10(x)/math.log10(math.exp(1.0))
		val rand = new Random()
		def random(): Double = (rand.nextDouble()-0.5)*0.2

		var weights: Array[Array[Double]] = Array()
		
		for (idx <- 0 until nn_architecture.size) {
			val layer_input_size = nn_architecture(idx)._1
			val layer_output_size = nn_architecture(idx)._2
			
			val W = Array.tabulate(layer_input_size*layer_output_size){i => random()}
			weights = weights ++ Array(W)
		}
		
		def getMax(z: Double) = math.max(0.0,z)
		def getExp(z: Double) = math.exp(z)
		def getVal(z: Double, a: Double) = if(z <= 0.0) 0.0 else a

		def testDiabloNN(): Double = {
			var cost_history = Array.tabulate(epochs){i => 0.0}
			var acc_history = Array.tabulate(epochs){i => 0.0}
			val X_1 = input1
			val y_1 = input2
			val X_2 = input3
			val y_2 = input4
			val layer1 = nn_architecture(0)._2
			val layer2 = nn_architecture(1)._2
			
			val weights1 = spark_context.parallelize(for(i <- 0 to m-1; j <- 0 to layer1-1) yield ((i,j),weights(0)(i*layer1+j))).cache()
			val weights2 = spark_context.parallelize(for(i <- 0 to layer1-1; j <- 0 to layer2-1) yield ((i,j),weights(1)(i*layer2+j))).cache()
			val X_d = q("tensor*(n,m)[ ((i,j),v) | ((i,j),v) <- X_1 ]")
			X_d._3.cache
			val Y_d = q("tensor*(n,1)[ ((i,j),v) | (i,v) <- y_1, j <- 0..0 ]")
			Y_d._3.cache
			val X_test_d = q("tensor*(test_size,m)[ ((i,j),v) | ((i,j),v) <- X_2 ]")
			X_test_d._3.cache
			val Y_test_d = q("tensor*(test_size,1)[ ((i,j),v) | (i,v) <- y_2, j <- 0..0 ]")
			Y_test_d._3.cache
			val t = System.currentTimeMillis()
			val Y_hat = q("""
				var w1 = tensor*(m,layer1)[ ((i,j),v) | ((i,j),v) <- weights1 ];
				var w2 = tensor*(layer1,layer2)[((i,j),v) | ((i,j),v) <- weights2 ];
				cache(w1);
				cache(w2);
				var itr = 0;
				while(itr < epochs) {
					var Z_curr1 = tensor*(n,layer1)[ ((i,j),+/v) | ((i,k),a) <- X_d, ((kk,j),w) <- w1,
		                                       kk == k, let v = w*a, group by (i,j) ];
		            var A_curr1 = tensor*(n,layer1)[ ((i,j),getMax(z)) | ((i,j),z) <- Z_curr1 ];
		            
		            var Z_curr2 = tensor*(n,layer2)[ ((i,j),+/v) | ((i,k),a) <- A_curr1, ((kk,j),w) <- w2,
		                                       kk == k, let v = w*a, group by (i,j) ];
		            var A_curr2 = tensor*(n,layer2)[ ((i,j),1/(1+getExp(-z))) | ((i,j),z) <- Z_curr2 ];
					var dA_curr = tensor*(n,layer2)[ ((i,j),((-y/y_hat)+(1-y)/(1-y_hat))) | ((i,j),y) <- Y_d, ((ii,jj),y_hat) <- A_curr2,
                    							i == ii, j == jj ];
                 	var dZ_curr = tensor*(n,layer2)[ ((i,j), dA*sig*(1-sig)) | ((i,j),dA) <- dA_curr, ((ii,jj),z) <- Z_curr2,
                    							i == ii, j == jj, let sig = 1/(1+getExp(-z)) ];
                    var dW_curr = tensor*(layer1,layer2)[ ((j,jj), +/v) | ((i,j),a) <- A_curr1, ((ii,jj),z) <- dZ_curr,
                    							i == ii, let v = z*a, group by (j,jj) ];
                    
                    var w2_update = tensor*(layer1,layer2)[((i,j),w-learning_rate*dw/n) | ((i,j),w) <- w2, ((ii,jj),dw) <- dW_curr,
                    							i==ii, j==jj ];
                    
                    var dA_curr2 = tensor*(n,layer1)[ ((i,ii),+/v) | ((i,j),z) <- dZ_curr, ((ii,jj),w) <- w2,
                    							j == jj, let v = w*z, group by (i,ii) ];
                 	var dZ_curr2 = tensor*(n,layer1)[ ((i,j), v) | ((i,j),z) <- Z_curr1, ((ii,jj),a) <- dA_curr2,
												i == ii, j == jj, let v = getVal(z,a) ];
                    var dW_curr2 = tensor*(m,layer1)[ ((j,jj), +/v) | ((i,j),a) <- X_d, ((ii,jj),z) <- dZ_curr2,
                    							i == ii, let v = z*a, group by (j,jj) ];
                    
                    var w1_update = tensor*(m,layer1)[((i,j),w-learning_rate*dw/n) | ((i,j),w) <- w1, ((ii,jj),dw) <- dW_curr2,
                    							i==ii, j==jj ];
                    w2 = w2_update;
                    w1 = w1_update;
					cache(w1);
					cache(w2);
					itr += 1;
				}
				var ret = tensor*(test_size,1)[ ((i,j),random()) | i <- 0..(test_size-1), j <- 0..0 ];
				if(validate) {
					var Z_curr1 = tensor*(test_size,layer1)[ ((i,j),+/v) | ((i,k),a) <- X_test_d, ((kk,j),w) <- w1,
		                                       kk == k, let v = w*a, group by (i,j) ];
		            var A_curr1 = tensor*(test_size,layer1)[ ((i,j),getMax(z)) | ((i,j),z) <- Z_curr1 ];
		            
		            var Z_curr2 = tensor*(test_size,layer2)[ ((i,j),+/v) | ((i,k),a) <- A_curr1, ((kk,j),w) <- w2,
		                                       kk == k, let v = w*a, group by (i,j) ];
		            var A_curr2 = tensor*(test_size,layer2)[ ((i,j),1/(1+getExp(-z))) | ((i,j),z) <- Z_curr2 ];
					ret = A_curr2;
				}
				rdd[ ((i,j),v) | ((i,j),v) <- ret ];
			""")
			if(validate) {
				val Y_pred = Y_hat.map{ case ((i,j),y) => (i, if(y > 0.5) 1 else 0)}
				val count = Y_pred.join(input4).map{ case (i, (y1, y2)) => if(y1==y2) 1.0 else 0.0}.reduce(_+_)
				println("Test Accuracy: "+count/test_size)
			}
		  	(System.currentTimeMillis()-t)/1000.0
		}

		def testDiabloNN1(): Double = {
			var cost_history = Array.tabulate(epochs){i => 0.0}
			var acc_history = Array.tabulate(epochs){i => 0.0}
			val X_1 = input1
			val y_1 = input2
			val X_2 = input3
			val y_2 = input4
			val number_of_layers = nn_architecture.size
			val layer1 = nn_architecture(0)._2
			val layer2 = nn_architecture(1)._2

			val weights1 = spark_context.parallelize(for(i <- 0 to m-1; j <- 0 to layer1-1) yield ((i,j),weights(0)(i*layer1+j))).cache()
			val weights2 = spark_context.parallelize(for(i <- 0 to layer1-1; j <- 0 to layer2-1) yield ((i,j),weights(1)(i*layer2+j))).cache()
			val X_d = q("tensor*(n,m)[ ((i,j),v) | ((i,j),v) <- X_1 ]")
			X_d._3.cache
			val Y_d = q("tensor*(n,1)[ ((i,j),v) | (i,v) <- y_1, j <- 0..0 ]")
			Y_d._3.cache
			val X_test_d = q("tensor*(test_size,m)[ ((i,j),v) | ((i,j),v) <- X_2 ]")
			X_test_d._3.cache
			val Y_test_d = q("tensor*(test_size,1)[ ((i,j),v) | (i,v) <- y_2, j <- 0..0 ]")
			Y_test_d._3.cache
			var w_arr: Array[RDD[((Int,Int),Double)]] = Array()
			for (idx <- 0 until number_of_layers) {
				val layer1 = nn_architecture(idx)._1
				val layer2 = nn_architecture(idx)._2
				val weights1 = spark_context.parallelize(for(i <- 0 to layer1-1; j <- 0 to layer2-1) yield ((i,j),weights(idx)(i*layer2+j))).cache()
				w_arr = w_arr :+ weights1
			}
			var Z_arr: Array[RDD[((Int, Int), Double)]] = Array.ofDim[RDD[((Int, Int), Double)]](number_of_layers)
			var A_arr: Array[RDD[((Int, Int), Double)]] = Array.ofDim[RDD[((Int, Int), Double)]](number_of_layers)
			
			val t = System.currentTimeMillis()
			for(itr <- 0 until epochs) {
				var A_curr1 = X_d
				for(l <- 0 to number_of_layers-1) {
					A_arr(l) = q("rdd[ ((i,j),v) | ((i,j),v) <- A_curr1 ]")
					var w1 = w_arr(l)
					val m1 = nn_architecture(l)._1
					val m2 = nn_architecture(l)._2
					var w2 = q("tensor*(m1,m2)[ ((i,j),w) | ((i,j),w) <- w1]")
					w2._3.cache
					var Z_curr1 = q("""tensor*(n,m2)[ ((i,j),+/v) | ((i,k),a) <- A_curr1, ((kk,j),w) <- w2,
											kk == k, let v = w*a, group by (i,j) ]""")
					Z_curr1._3.cache
					if(l == number_of_layers-1) {
						A_curr1 = q("""tensor*(n,m2)[ ((i,j),1/(1+getExp(-z))) | ((i,j),z) <- Z_curr1 ]""")
					}
					else {
						A_curr1 = q("""tensor*(n,m2)[ ((i,j),getMax(z)) | ((i,j),z) <- Z_curr1 ]""")
					}
					A_curr1._3.cache
					Z_arr(l) = q("rdd[ ((i,j),v) | ((i,j),v) <- Z_curr1 ]")
				}
				var dA_prev = q("""tensor*(n,1)[ ((i,j),((-y/y_hat)+(1-y)/(1-y_hat))) | ((i,j),y) <- Y_d, ((ii,jj),y_hat) <- A_curr1,
                    							i == ii, j == jj ]""")
				for(l <- 0 to number_of_layers-1) {
					var idx = number_of_layers - 1 - l
					var dA_curr = dA_prev
					val m1 = nn_architecture(idx)._1
					val m2 = nn_architecture(idx)._2
					val Z_curr1 = Z_arr(idx)
					val A_curr1 = A_arr(idx)
					val Z_curr2 = q("tensor*(n,m2)[ ((i,j),v) | ((i,j),v) <- Z_curr1 ]")
					val A_curr2 = q("tensor*(n,m1)[ ((i,j),v) | ((i,j),v) <- A_curr1 ]")
					val w1 = w_arr(idx)
					var w2 = q("tensor*(m1,m2)[ ((i,j),w) | ((i,j),w) <- w1]")
					w2._3.cache
					var dZ_curr = q("""tensor*(n,m2)[ ((i,j), v) | ((i,j),a) <- dA_curr, ((ii,jj),z) <- Z_curr2,
											i == ii, j == jj, let v = getVal(z,a) ]""")
					if(idx == number_of_layers - 1) {
						dZ_curr = q("""tensor*(n,m2)[ ((i,j), dA*sig*(1-sig)) | ((i,j),dA) <- dA_curr, ((ii,jj),z) <- Z_curr2,
											i == ii, j == jj, let sig = 1/(1+getExp(-z)) ]""")
					}
					dZ_curr._3.cache
					var dW_curr = q("""tensor*(m1,m2)[ ((j,jj), +/v) | ((i,j),a) <- A_curr2, ((ii,jj),z) <- dZ_curr,
											i == ii, let v = z*a, group by (j,jj) ]""")
					dW_curr._3.cache
					dA_prev = q("""tensor*(n,m1)[ ((i,ii),+/v) | ((i,j),z) <- dZ_curr, ((ii,jj),w) <- w2,
											j == jj, let v = w*z, group by (i,ii) ]""")
					dA_prev._3.cache
					var w_update = q("""tensor*(m1,m2)[((i,j),w-learning_rate*dw/n) | ((i,j),w) <- w2, ((ii,jj),dw) <- dW_curr,
											i==ii, j==jj ]""")
					w_update._3.cache
					w_arr(idx) = q("rdd[ ((i,j),v) | ((i,j),v) <- w_update ]")
					w_arr(idx).cache
				}
			}
			if(validate) {
				var A_curr1 = X_test_d
				for(l <- 0 to number_of_layers-1) {
					var w1 = w_arr(l)
					val m1 = nn_architecture(l)._1
					val m2 = nn_architecture(l)._2
					var w2 = q("tensor*(m1,m2)[ ((i,j),w) | ((i,j),w) <- w1]")
					var Z_curr1 = q("""tensor*(test_size,m2)[ ((i,j),+/v) | ((i,k),a) <- A_curr1, ((kk,j),w) <- w2,
											kk == k, let v = w*a, group by (i,j) ]""")
					if(l == number_of_layers-1) {
						A_curr1 = q("""tensor*(test_size,m2)[ ((i,j),1/(1+getExp(-z))) | ((i,j),z) <- Z_curr1 ]""")
					}
					else {
						A_curr1 = q("""tensor*(test_size,m2)[ ((i,j),getMax(z)) | ((i,j),z) <- Z_curr1 ]""")
					}
				}
				val Y_hat = q("rdd[ ((i,j),v) | ((i,j),v) <- A_curr1 ]")
				val Y_pred = Y_hat.map{ case ((i,j),y) => (i, if(y > 0.5) 1 else 0)}
				val count = Y_pred.join(input4).map{ case (i, (y1, y2)) => if(y1==y2) 1.0 else 0.0}.reduce(_+_)
				println("Test Accuracy: "+count/test_size)
			}
		  	(System.currentTimeMillis()-t)/1000.0
		}
		
		val spark = SparkSession.builder().config(conf).getOrCreate()
		import spark.implicits._
		
		def testMLlibNN(): Double = {
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
			input1.map{case ((i,j),v) => (i,v)}.groupByKey()
					.map{case (i,v) => (i, vect(v))}.toDF.createOrReplaceTempView("X_d")
			input2.toDF.createOrReplaceTempView("Y_d")
			input3.map{case ((i,j),v) => (i,v)}.groupByKey()
					.map{case (i,v) => (i, vect(v))}.toDF.createOrReplaceTempView("X_test_d")
			input4.toDF.createOrReplaceTempView("Y_test_d")

			val training_data = spark.sql("select Y_d._2 as label, X_d._2 as features from X_d join Y_d on X_d._1=Y_d._1")
				.rdd.map{row => LabeledPoint(
			  	row.getAs[Double]("label"),
			  	row.getAs[org.apache.spark.ml.linalg.Vector]("features")
			)}.toDF.cache()

			val t = System.currentTimeMillis()
			val lr = new LogisticRegression()
			  .setMaxIter(epochs)
			  .setRegParam(0.3)
			  .setElasticNetParam(0.8)

			// Fit the model
			val lrModel = lr.fit(training_data)

			if(validate) {
				val test_data = spark.sql("select Y_test_d._2 as label, X_test_d._2 as features from X_test_d join Y_test_d on X_test_d._1=Y_test_d._1")
					.rdd.map{row => LabeledPoint(
					row.getAs[Double]("label"),
					row.getAs[org.apache.spark.ml.linalg.Vector]("features")
				)}.toDF.cache()
				val predictions = lrModel.transform(test_data)
				val evaluator = new BinaryClassificationEvaluator()
				val accuracy = evaluator.evaluate(predictions)
				println("Test Accuracy: "+accuracy)
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
					if(i > 0) s += t
					i += 1
					println("Try: "+i+"/"+j+" time: "+t)
				}
			}
			if (i > 0) s = s/(i-1)
			print("*** %s cores=%d n=%d m=%d N=%d ".format(name,cores,total_size,m,N))
			println("tries=%d %.3f secs".format(i,s))
		}

		test("Diablo Comprehension Neural Network",testDiabloNN)
		test("Diablo Comprehension Neural Network loops",testDiabloNN1)
		test("MLlib Logistic Regression Neural Network",testMLlibNN)
		
		spark_context.stop()
	}
}
