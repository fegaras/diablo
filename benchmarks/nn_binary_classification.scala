import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import org.apache.spark.sql._
import org.apache.spark.sql.functions._
import org.apache.spark.sql.expressions.Aggregator
import org.apache.spark.sql.catalyst.encoders.ExpressionEncoder
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._
import org.apache.spark.ml.feature.LabeledPoint
import org.apache.spark.ml.linalg.Vectors
import org.apache.spark.ml.classification.MultilayerPerceptronClassifier
import org.apache.spark.ml.evaluation.MulticlassClassificationEvaluator
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
		
		val learning_rate = 0.5
		val total_size = args(1).toInt
		val n = (0.8*total_size).toInt
		val test_size = total_size - n
		val m = 101
		val epochs = 10

		val input1 = spark_context.textFile(args(2),number_of_partitions)
		          .map( line => { val a = line.split(",").toList
		          				((a(0).toInt,a(1).toInt),a(2).toDouble)} ).cache
		val input2 = spark_context.textFile(args(3),number_of_partitions)
		          .map( line => { val a = line.split(",").toList
		                         (a(0).toInt,a(1).toDouble) } ).cache
		val input3 = spark_context.textFile(args(4),number_of_partitions)
		          .map( line => { val a = line.split(",").toList
		          				((a(0).toInt,a(1).toInt),a(2).toDouble) } ).cache
		val input4 = spark_context.textFile(args(5),number_of_partitions)
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

		val nn_architecture = List((m, 32), (32, 8), (8, 1))

		val rand = new Random()
		def random(): Double = (rand.nextDouble()-0.5)

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
		def getSigmoid(z: Double) = 1/(1+math.exp(-z))

		def testDiabloNN(): Double = {
			var cost_history = Array.tabulate(epochs){i => 0.0}
			var acc_history = Array.tabulate(epochs){i => 0.0}
			val X_1 = input1
			val y_1 = input2
			val X_2 = input3
			val y_2 = input4
			val number_of_layers = nn_architecture.size
			val layer1 = nn_architecture(0)._2
			val layer2 = nn_architecture(1)._2

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
			
			val t = System.currentTimeMillis()
			for(itr <- 0 until epochs) {
				var Z_arr: Array[RDD[((Int, Int), Double)]] = Array.ofDim[RDD[((Int, Int), Double)]](number_of_layers)
				var A_arr: Array[RDD[((Int, Int), Double)]] = Array.ofDim[RDD[((Int, Int), Double)]](number_of_layers)

				var A_curr1 = X_d
				for(l <- 0 to number_of_layers-1) {
					A_arr(l) = q("rdd[ ((i,j),v) | ((i,j),v) <- A_curr1 ]")
					var w1 = w_arr(l)
					val m1 = nn_architecture(l)._1
					val m2 = nn_architecture(l)._2
					var w2 = q("tensor*(m1,m2)[ ((i,j),w) | ((i,j),w) <- w1]")
					var Z_curr1 = q("""tensor*(n,m2)[ ((i,j),+/v) | ((i,k),a) <- A_curr1, ((kk,j),w) <- w2,
											kk == k, let v = w*a, group by (i,j) ]""")
					if(l < number_of_layers-1) {
						A_curr1 = q("""tensor*(n,m2)[ ((i,j),getMax(z)) | ((i,j),z) <- Z_curr1 ]""")
					}
					else {
						A_curr1 = q("""tensor*(n,m2)[ ((i,j),1/(1+getExp(-z))) | ((i,j),z) <- Z_curr1 ]""")
					}
					A_curr1._3.cache
					Z_arr(l) = q("rdd[ ((i,j),v) | ((i,j),v) <- Z_curr1 ]")
				}
				var dA_prev = q("""tensor*(n,1)[ ((i,j),(2.0/n)*(y_hat-y)) | ((i,j),y) <- Y_d, ((ii,jj),y_hat) <- A_curr1,
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
					var dZ_curr = q("""tensor*(n,m2)[ ((i,j), v) | ((i,j),a) <- dA_curr, ((ii,jj),z) <- Z_curr2,
											i == ii, j == jj, let v = getVal(z,a) ]""")
					if(idx == number_of_layers - 1) {
						dZ_curr = q("""tensor*(n,m2)[ ((i,j), dA*sig*(1-sig)) | ((i,j),dA) <- dA_curr, ((ii,jj),z) <- Z_curr2,
											i == ii, j == jj, let sig = 1/(1+getExp(-z)) ]""")
					}
					var dW_curr = q("""tensor*(m1,m2)[ ((j,jj), +/v) | ((i,j),a) <- A_curr2, ((ii,jj),z) <- dZ_curr,
											i == ii, let v = z*a, group by (j,jj) ]""")
					dA_prev = q("""tensor*(n,m1)[ ((i,ii),+/v) | ((i,j),z) <- dZ_curr, ((ii,jj),w) <- w2,
											j == jj, let v = w*z, group by (i,ii) ]""")
					dA_prev._3.cache
					var w_update = q("""tensor*(m1,m2)[((i,j),w-learning_rate*dw) | ((i,j),w) <- w2, ((ii,jj),dw) <- dW_curr,
											i==ii, j==jj ]""")
					w_arr(idx) = q("rdd[ ((i,j),v) | ((i,j),v) <- w_update ]")
					w_arr(idx).cache
				}
			}
			for(l <- 0 to number_of_layers-1)
				w_arr(l).count
			if(validate) {
				var A_curr1 = X_test_d
				for(l <- 0 to number_of_layers-1) {
					var w1 = w_arr(l)
					val m1 = nn_architecture(l)._1
					val m2 = nn_architecture(l)._2
					var w2 = q("tensor*(m1,m2)[ ((i,j),w) | ((i,j),w) <- w1]")
					var Z_curr1 = q("""tensor*(test_size,m2)[ ((i,j),+/v) | ((i,k),a) <- A_curr1, ((kk,j),w) <- w2,
											kk == k, let v = w*a, group by (i,j) ]""")
					if(l < number_of_layers-1) {
						A_curr1 = q("""tensor*(test_size,m2)[ ((i,j),getMax(z)) | ((i,j),z) <- Z_curr1 ]""")
					}
					else {
						A_curr1 = q("""tensor*(test_size,m2)[ ((i,j),1/(1+getExp(-z))) | ((i,j),z) <- Z_curr1 ]""")
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

		// forces df to materialize in memory and evaluate all transformations
		// (noop write format doesn't have much overhead)
		def force ( df: DataFrame ) {
			df.write.mode("overwrite").format("noop").save()
		}

		def testMLlibNN(): Double = {
			def vect ( a: Iterable[Double] ): org.apache.spark.ml.linalg.Vector = {
			  val s = Array.ofDim[Double](m)
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
			force(training_data)

			val layers = Array[Int](m, 32, 8, 2)

			// create the trainer and set its parameters
			val trainer = new MultilayerPerceptronClassifier()
				.setLayers(layers)
				.setBlockSize(N)
				.setSeed(1234L)
				.setMaxIter(epochs)

			val t = System.currentTimeMillis()
			// train the model
			val model = trainer.fit(training_data)
			// Summarize the model over the training set and print out some metrics
			val trainingSummary = model.summary
			println(s"numIterations: ${trainingSummary.totalIterations}")
			println(s"objectiveHistory: [${trainingSummary.objectiveHistory.mkString(",")}]")
			println(s"Accuracy: ${trainingSummary.accuracy}")

			// compute accuracy on the test set
			if(validate) {
				val test_data = spark.sql("select Y_test_d._2 as label, X_test_d._2 as features from X_test_d join Y_test_d on X_test_d._1=Y_test_d._1")
					.rdd.map{row => LabeledPoint(
					row.getAs[Double]("label"),
					row.getAs[org.apache.spark.ml.linalg.Vector]("features")
				)}.toDF.cache()
				force(test_data)
				val predictions = model.transform(test_data)
				val evaluator = new MulticlassClassificationEvaluator().setMetricName("accuracy")
				val accuracy = evaluator.evaluate(predictions)
				println("Test Accuracy: "+accuracy)
			}
			(System.currentTimeMillis()-t)/1000.0
		}

		def convertMatrix(mat1: Matrix, f:Double=>Double): Matrix = {
			var arr = Array[Double]()
			for(v <- mat1.colIter; i <- 0 to v.size-1) {
				arr = arr :+ f(v(i))
			}
			Matrices.dense(mat1.numRows, mat1.numCols, arr)
		}

		def convertMatrix1(mat1: Matrix, mat2: Matrix): Matrix = {
			var arr = Array[Double]()
			var col1 = 0
			var col2 = 0
			for(p <- mat1.colIter) {
				col2 = 0
				for(q <- mat2.colIter) {
					if(col1 == col2) {
						for(i <- 0 to p.size-1) {
							val sig = 1/(1+math.exp(-p(i)))
							arr = arr :+ q(i)*sig*(1-sig)
						}
					}
					col2 += 1
				}
				col1 += 1
			}
			Matrices.dense(mat1.numRows, mat1.numCols, arr)
		}

		def convertMatrix2(mat1: Matrix, mat2: Matrix): Matrix = {
			var arr = Array[Double]()
			var col1 = 0
			var col2 = 0
			for(p <- mat1.colIter) {
				col2 = 0
				for(q <- mat2.colIter) {
					if(col1 == col2) {
						for(i <- 0 to p.size-1) {
							var tmp = q(i)
							if(p(i) <= 0.0)
								tmp = 0.0
							arr = arr :+ tmp
						}
					}
					col2 += 1
				}
				col1 += 1
			}
			Matrices.dense(mat1.numRows, mat1.numCols, arr)
		}

		def testMLlibHandWrittenNN(): Double = {
			val t = System.currentTimeMillis()
			val number_of_layers = nn_architecture.length
			var w_arr: Array[BlockMatrix] = Array()

			for (idx <- 0 until number_of_layers) {
				val layer_input_size = nn_architecture(idx)._1
				val layer_output_size = nn_architecture(idx)._2
				val W = new CoordinateMatrix(spark_context.parallelize(for(i <- 0 to layer_input_size-1; j <- 0 to layer_output_size-1) 
					yield (MatrixEntry(i,j, weights(idx)(i*layer_output_size+j))))).toBlockMatrix(N,N).cache
				w_arr = w_arr ++ Array(W)
			}

			for (itr <- 0 until epochs) {
				var A_history: Array[BlockMatrix] = Array()
				var Z_history: Array[BlockMatrix] = Array()
				var A_curr = new CoordinateMatrix(input1.map{ case ((i,j),v) => MatrixEntry(i,j,v)}).toBlockMatrix(N,N).cache

				for (idx <- 0 until number_of_layers) {
					var A_prev = A_curr
					var W_curr = w_arr(idx)
					var Z_curr = A_prev.multiply(W_curr)
					if(idx < number_of_layers - 1) {
						// relu
						val A_curr_blocks = Z_curr.blocks.map{ case ((i,j),v) => ((i,j), convertMatrix(v,math.max(0.0,_)))}
						A_curr = new BlockMatrix(A_curr_blocks, N, N)
					}
					else {
						// sigmoid
						val A_curr_blocks = Z_curr.blocks.map{ case ((i,j),v) => ((i,j),convertMatrix(v,getSigmoid))}
						A_curr = new BlockMatrix(A_curr_blocks, N, N)
					}
					A_history = A_history++Array(A_prev)
					Z_history = Z_history++Array(Z_curr)
				}
				val Y_hat = A_curr
				val y_train = new CoordinateMatrix(input2.map{ case (i,v) => MatrixEntry(i,0,v)}).toBlockMatrix(N,N).cache
				val dA_prev_blocks = Y_hat.subtract(y_train).blocks.map{ case ((i,j),v) => ((i,j),convertMatrix(v,_*(2.0/n)))}
				var dA_prev = new BlockMatrix(dA_prev_blocks, N, N).cache

				var weight_grads: Array[BlockMatrix] = Array()
				for (idx <- number_of_layers-1 to 0 by -1) {
					var dA_curr = dA_prev

					var A_prev = A_history(idx)
					var Z_curr = Z_history(idx)
					var W_curr = w_arr(idx)

					var dZ_curr = Z_curr
					if(idx < number_of_layers-1) {
						// relu
						val dZ_curr_blocks = Z_curr.blocks.join(dA_curr.blocks).map{ case (i,(z,da)) => (i,convertMatrix2(z,da))}
						dZ_curr = new BlockMatrix(dZ_curr_blocks,N,N).cache
					}
					else {
						// sigmoid
						val dZ_curr_blocks = Z_curr.blocks.join(dA_curr.blocks).map{ case (i,(z,da)) => (i,convertMatrix1(z,da))}
						dZ_curr = new BlockMatrix(dZ_curr_blocks,N,N).cache
					}
					var dW_curr_blocks = A_prev.transpose.multiply(dZ_curr).blocks
													.map{ case ((i,j),v) => ((i,j),convertMatrix(v,_*learning_rate))}
					dA_prev = dZ_curr.multiply(W_curr.transpose)
					val dW_curr = new BlockMatrix(dW_curr_blocks, N, N)
					weight_grads = weight_grads++Array(dW_curr)
				}
				for (idx <- 0 until number_of_layers) {
					w_arr(idx) = w_arr(idx).subtract(weight_grads(number_of_layers-1-idx))
					w_arr(idx).cache
				}
			}
			for (idx <- 0 until number_of_layers)
				w_arr(idx).blocks.count
			if(validate) {
				var A_curr = new CoordinateMatrix(input3.map{ case ((i,j),v) => MatrixEntry(i,j,v)}).toBlockMatrix(N,N).cache
				for (idx <- 0 until number_of_layers) {
					var A_prev = A_curr
					var W_curr = w_arr(idx)
					var Z_curr = A_prev.multiply(W_curr)
					if(idx < number_of_layers - 1) {
						// relu
						val A_curr_blocks = Z_curr.blocks.map{ case ((i,j),v) => ((i,j), convertMatrix(v,math.max(0.0,_)))}
						A_curr = new BlockMatrix(A_curr_blocks, N, N)
					}
					else {
						// sigmoid
						val A_curr_blocks = Z_curr.blocks.map{ case ((i,j),v) => ((i,j),convertMatrix(v,getSigmoid))}
						A_curr = new BlockMatrix(A_curr_blocks, N, N)
					}
				}
				var Y_hat = A_curr.toCoordinateMatrix().entries.map{ case e => (e.i,e.value)}
				var count = Y_hat.map{ case (i,y) => (i, if(y > 0.5) 1 else 0)}.join(input4.map{case (i,y) => (i.toLong, y)})
					.map{ case (i,(y,y_t)) => if(y==y_t) 1.0 else 0.0}.reduce(_+_)
				println("Test Accuracy: "+count/test_size)
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

		test("MLlib Neural Network",testMLlibNN)
		test("Diablo Comprehension Neural Network",testDiabloNN)
		test("MLlib Handwritten Neural Network",testMLlibHandWrittenNN)

		spark_context.stop()
	}
}
