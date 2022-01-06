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
		
		val learning_rate = 2.0
		val total_size = 1000
		val n = (0.8*total_size).toInt
		val test_size = total_size - n
		val m = 2
		val epochs = args(1).toInt

		val input1 = sc.textFile(args(2))
		          .map( line => { val a = line.split(",").toList
		          				((a(0).toInt,a(1).toInt),a(2).toDouble)} ).cache
		val input2 = sc.textFile(args(3))
		          .map( line => { val a = line.split(",").toList
		                         (a(0).toInt,a(1).toDouble) } ).cache
		val input3 = sc.textFile(args(4))
		          .map( line => { val a = line.split(",").toList
		          				((a(0).toInt,a(1).toInt),a(2).toDouble) } ).cache
		val input4 = sc.textFile(args(5))
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

		val nn_architecture = List((2, 25), (25, 1))
		
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
		
		var sweights: Array[Array[Double]] = Array()
		var sbiases: Array[Array[Double]] = Array()
		var weights: Array[Array[Double]] = Array()
		var biases: Array[Array[Double]] = Array()
		
		for (idx <- 0 until 2) {
			val layer_input_size = nn_architecture(idx)._1
			val layer_output_size = nn_architecture(idx)._2
			
			val W = Array.tabulate(layer_output_size * layer_input_size){i => random()}
			weights = weights ++ Array(W)
			sweights = sweights ++ Array(W.clone)
			val B = Array.tabulate(layer_output_size * 1){i => random()}
			biases = biases ++ Array(B)
			sbiases = sbiases ++ Array(B.clone)
		}

		def testHandWrittenNN(): Double = {
			val t = System.currentTimeMillis()
			val number_of_layers = nn_architecture.length
			var cost_history = Array.tabulate(epochs){i => 0.0}
			var acc_history = Array.tabulate(epochs){i => 0.0}
			
			for (itr <- 0 until epochs) {
				var A_history: Array[Array[Double]] = Array()
				var Z_history: Array[Array[Double]] = Array()
				var A_curr = mat_transpose(X, n, m)
				
				for (idx <- 0 until number_of_layers) {
					var A_prev = A_curr
					var W_curr = weights(idx)
					var b_curr = biases(idx)
					var a_m = nn_architecture(idx)._2
					var b_m = nn_architecture(idx)._1
					var Z_curr = mat_add(mat_multiply(W_curr, A_prev, a_m, b_m, n), b_curr, a_m, n)
					if(idx == number_of_layers - 1) {
						// sigmoid
						var res = Array.tabulate(a_m*n){j => 0.0}
						for(j <- 0 until a_m*n)
							res(j) = 1/(1+math.exp(-Z_curr(j)))
						A_curr = res
					}
					else {
						// relu
						var res = Array.tabulate(a_m*n){j => 0.0}
						for(j <- 0 until a_m*n)
							res(j) = math.max(0.0,Z_curr(j))
						A_curr = res
					}
					
					A_history = A_history++Array(A_prev)
					Z_history = Z_history++Array(Z_curr)
				}
				val Y_hat = A_curr
				
				var dA_prev = Array.tabulate(n) {j => 0.0}
				var count = 0.0
				for(j <- 0 until n) {
					dA_prev(j) = (-Y(j)/Y_hat(j) + (1-Y(j))/(1-Y_hat(j)))
					cost_history(itr) += (Y(j)*ln(Y_hat(j)) + (1-Y(j))*ln(1-Y_hat(j)))
					var pr_to_cl = 0
					if(Y_hat(j) > 0.5)
						pr_to_cl = 1
					if(pr_to_cl == Y(j))
						count += 1.0
				}
				cost_history(itr) *= (-1.0/n)
				acc_history(itr) = count/n
				
				var weight_grads: Array[Array[Double]] = Array()
				var bias_grads: Array[Array[Double]] = Array()
				for (idx <- number_of_layers-1 to 0 by -1) {
					var dA_curr = dA_prev
					var A_prev = A_history(idx)
					var Z_curr = Z_history(idx)
					var W_curr = weights(idx)
					var b_curr = biases(idx)
					
					var a_m = nn_architecture(idx)._2
					var b_m = nn_architecture(idx)._1
					var dZ_curr = Array.tabulate(a_m*n) {j => 0.0}
					if(idx == number_of_layers-1) {
						// sigmoid
						for(j <- 0 until a_m*n) {
							var sig = 1/(1+math.exp(-Z_curr(j)))
							dZ_curr(j) = dA_curr(j) * sig * (1-sig)
						}
					}
					else {
						// relu
						for(j <- 0 until a_m*n) {
							if(Z_curr(j) <= 0.0)
								dZ_curr(j) = 0.0
							else
								dZ_curr(j) = dA_curr(j)
						}
					}
					var dW_curr = mat_multiply(dZ_curr, mat_transpose(A_prev, b_m, n), a_m, n, b_m)
					for(j <- 0 until a_m*b_m)
						dW_curr(j) = dW_curr(j) / n

					var db_curr = Array.tabulate(a_m) {j => 0.0}
					for(j <- 0 until a_m) {
						for(k <- 0 until n)
							db_curr(j) += dZ_curr(j*n+k)
						db_curr(j) = db_curr(j) / n
					}
					dA_prev = mat_multiply(mat_transpose(W_curr, a_m, b_m), dZ_curr, b_m, a_m, n)

					weight_grads = weight_grads++Array(dW_curr)
					bias_grads = bias_grads++Array(db_curr)
				}
				for (idx <- 0 until number_of_layers) {
					for(j <- 0 until weights(idx).length) {
						weights(idx)(j) -= learning_rate * weight_grads(number_of_layers-1-idx)(j)
					}
					for(j <- 0 until biases(idx).length) {
						biases(idx)(j) -= learning_rate * bias_grads(number_of_layers-1-idx)(j)
					}
				}
			}
			var A_curr = mat_transpose(X_test, test_size, m)
			for (idx <- 0 until number_of_layers) {
				var A_prev = A_curr
				var W_curr = weights(idx)
				var b_curr = biases(idx)
				var a_m = nn_architecture(idx)._2
				var b_m = nn_architecture(idx)._1
				var Z_curr = mat_add(mat_multiply(W_curr, A_prev, a_m, b_m, test_size), b_curr, a_m, test_size)
				if(idx == number_of_layers - 1) {
					// sigmoid
					var res = Array.tabulate(a_m*test_size){j => 0.0}
					for(j <- 0 until a_m*test_size)
						res(j) = 1/(1+math.exp(-Z_curr(j)))
					A_curr = res
				}
				else {
					// relu
					var res = Array.tabulate(a_m*test_size){j => 0.0}
					for(j <- 0 until a_m*test_size)
						res(j) = math.max(0.0,Z_curr(j))
					A_curr = res
				}
			}
			var Y_hat = A_curr
			println("Y_hat")
			Y_hat.map(println)
			var count = 0.0
			for(j <- 0 until test_size) {
				var pr_to_cl = 0
				if(Y_hat(j) > 0.5)
					pr_to_cl = 1
				if(pr_to_cl == Y_test(j))
					count += 1.0
			}
			println("Test Accuracy: "+count/test_size)
			(System.currentTimeMillis()-t)/1000.0
		}
		
		def getMax(z: Double) = math.max(0.0,z)
		def getExp(z: Double) = math.exp(z)
		def getVal(z: Double, a: Double) = if(z <= 0.0) 0.0 else a

		def testDiabloNN(): Double = {
			val t = System.currentTimeMillis()
			var cost_history = Array.tabulate(epochs){i => 0.0}
			var acc_history = Array.tabulate(epochs){i => 0.0}
			val X_1 = input1
			val y_1 = input2
			val X_2 = input3
			val y_2 = input4
			val layer1 = nn_architecture(0)._2
			val layer2 = nn_architecture(1)._2
			
			val weights1 = sc.parallelize(for(i <- 0 to layer1-1; j <- 0 to m-1) yield ((i,j),sweights(0)(i*m+j))).cache()
			val weights2 = sc.parallelize(for(i <- 0 to layer2-1; j <- 0 to layer1-1) yield ((i,j),sweights(1)(i*layer1+j))).cache()
			val bias1 = sc.parallelize(for(i <- 0 to layer1-1) yield (i,sbiases(0)(i))).cache()
			val bias2 = sc.parallelize(for(i <- 0 to layer2-1) yield (i,sbiases(1)(i))).cache()
			val Y_hat = q("""
				var X_d = tensor*(m)(n)[ ((i,j),v) | ((j,i),v) <- X_1 ];
				var Y_d = tensor*(n)[ (i,v) | (i,v) <- y_1 ];
				var w1 = tensor*(layer1)(m)[ ((i,j),v) | ((i,j),v) <- weights1 ];
				var b1 = tensor*(layer1)[(i,v) | (i,v) <- bias1 ];
				var w2 = tensor*(layer2,layer1)[((i,j),v) | ((i,j),v) <- weights2 ];
				var b2 = tensor*(layer2)[(i,v) | (i,v) <- bias2 ];
				var itr = 0;
				while(itr < epochs) {
					var tmp_Z1 = tensor*(layer1,n)[ ((i,j),+/v) | ((i,k),w) <- w1, ((kk,j),a) <- X_d,
		                                       kk == k, let v = w*a, group by (i,j) ];
		            var Z_curr1 = tensor*(layer1,n)[ ((i,j),z+b) | ((i,j),z) <- tmp_Z1, (ii,b) <- b1,
		                                       i == ii];
		            var A_curr1 = tensor*(layer1,n)[ ((i,j),getMax(z)) | ((i,j),z) <- Z_curr1 ];
		            
		            var tmp_Z2 = tensor*(layer2,n)[ ((i,j),+/v) | ((i,k),w) <- w2, ((kk,j),a) <- A_curr1,
		                                       kk == k, let v = w*a, group by (i,j) ];
		            var Z_curr2 = tensor*(n)[ (j,+/v) | ((i,j),z) <- tmp_Z2, (ii,b) <- b2,
		                                       i == ii, let v = z+b, group by j];
		            var A_curr2 = tensor*(n)[ (i,1/(1+getExp(-z))) | (i,z) <- Z_curr2 ];
					var dA_curr = tensor*(n)[ (i,((-y/y_hat)+(1-y)/(1-y_hat))) | (i,y) <- Y_d, (ii,y_hat) <- A_curr2,
                    							i == ii ];
                 	var dZ_curr_1 = tensor*(n)[ (i, dA*sig*(1-sig)) | (i,dA) <- dA_curr, (ii,z) <- Z_curr2,
                    							i == ii, let sig = 1/(1+getExp(-z)) ];
                    
                    var dZ_curr = tensor*(layer2,n)[ ((i,j), v1) | i <- 0..0, (j,v1) <- dZ_curr_1];
                    var dW_curr = tensor*(layer2,layer1)[ ((i,ii), +/v) | ((i,j),z) <- dZ_curr, ((ii,jj),a) <- A_curr1,
                    							j == jj, let v = z*a, group by (i,ii) ];
                    var db_curr = tensor*(layer2)[ (i, +/z) | ((i,j),z) <- dZ_curr, group by i ];
                    
                    var w2_update = tensor*(layer2,layer1)[((i,j),w-learning_rate*dw/n) | ((i,j),w) <- w2, ((ii,jj),dw) <- dW_curr,
                    							i==ii, j==jj ];
                   	var b2_update = tensor*(layer2)[(i,b-learning_rate*db/n) | (i,b) <- b2, (ii,db) <- db_curr,
                    							i==ii ];
                    
                    var dA_curr2 = tensor*(layer1,n)[ ((j,jj),+/v) | ((i,j),w) <- w2, ((ii,jj),z) <- dZ_curr,
                    							i == ii, let v = w*z, group by (j,jj) ];
                 	var dZ_curr2 = tensor*(layer1,n)[ ((i,j), v) | ((i,j),z) <- Z_curr1, ((ii,jj),a) <- dA_curr2,
												i == ii, j == jj, let v = getVal(z,a) ];
                    var dW_curr2 = tensor*(layer1,m)[ ((i,ii), +/v) | ((i,j),z) <- dZ_curr2, ((ii,jj),a) <- X_d,
                    							j == jj, let v = z*a, group by (i,ii) ];
                    var db_curr2 = tensor*(layer1)[ (i, +/z) | ((i,j),z) <- dZ_curr2, group by i ];
                    
                    var w1_update = tensor*(layer1,m)[((i,j),w-learning_rate*dw/n) | ((i,j),w) <- w1, ((ii,jj),dw) <- dW_curr2,
                    							i==ii, j==jj ];
                   	var b1_update = tensor*(layer1)[(i,b-learning_rate*db/n) | (i,b) <- b1, (ii,db) <- db_curr2,
                    							i==ii ];
                    w2 = w2_update;
                    b2 = b2_update;
                    w1 = w1_update;
                    b1 = b1_update;
                    							
					itr += 1;
				}
				var X_test_d = tensor*(m)(test_size)[ ((i,j),v) | ((j,i),v) <- X_2 ];
				var Y_test_d = tensor*(test_size)[ (i,v) | (i,v) <- y_2 ];
				var tmp_Z1 = tensor*(layer1,test_size)[ ((i,j),+/v) | ((i,k),w) <- w1, ((kk,j),a) <- X_test_d,
                                           kk == k, let v = w*a, group by (i,j) ];
                var Z_curr1 = tensor*(layer1,test_size)[ ((i,j),z+b) | ((i,j),z) <- tmp_Z1, (ii,b) <- b1,
                                           i == ii];
                var A_curr1 = tensor*(layer1,test_size)[ ((i,j),getMax(z)) | ((i,j),z) <- Z_curr1 ];
                
                var tmp_Z2 = tensor*(layer2,test_size)[ ((i,j),+/v) | ((i,k),w) <- w2, ((kk,j),a) <- A_curr1,
                                           kk == k, let v = w*a, group by (i,j) ];
                var Z_curr2 = tensor*(test_size)[ (j,+/v) | ((i,j),z) <- tmp_Z2, (ii,b) <- b2,
                                           i == ii, let v = z+b, group by j];
                var A_curr2 = tensor*(test_size)[ (i,1/(1+getExp(-z))) | (i,z) <- Z_curr2 ];
                rdd[ (i,v) | (i,v) <- A_curr2 ];
			""")
			val Y_pred = Y_hat.map{ case (i,y) => (i, if(y > 0.5) 1 else 0)}
			val count = Y_pred.join(input4).map{ case (i, (y1, y2)) => if(y1==y2) 1.0 else 0.0}.reduce(_+_)
			println("Test Accuracy: "+count/test_size)
		  	(System.currentTimeMillis()-t)/1000.0
		}
		
		def rddToBlockMatrix(arr: RDD[((Long,Long), Double)]): BlockMatrix = {
			new CoordinateMatrix(arr.map{ case ((i,j),v) => MatrixEntry(i,j,v)}).toBlockMatrix().cache()
		}
		
		def blockMatrixTordd(mat: BlockMatrix): RDD[((Long,Long), Double)] = {
			mat.toCoordinateMatrix().entries.map(e => ((e.i,e.j),e.value))
		}
		
		def rddToBlockMatrix1(arr: RDD[(Long, Double)]): BlockMatrix = {
			new CoordinateMatrix(arr.map{ case (i,v) => MatrixEntry(i,0,v)}).toBlockMatrix().cache()
		}
		
		def blockMatrixTordd1(mat: BlockMatrix): RDD[(Long, Double)] = {
			mat.toCoordinateMatrix().entries.map(e => (e.i,e.value))
		}
		
		def testMLlibHandWrittenNN(): Double = {
			val t = System.currentTimeMillis()
			val number_of_layers = nn_architecture.length
			var weights: Array[RDD[((Long,Long), Double)]] = Array()
			var biases: Array[RDD[(Long, Double)]] = Array()
			var cost_history = Array.tabulate(epochs){i => 0.0}
			var acc_history = Array.tabulate(epochs){i => 0.0}
			
			for (idx <- 0 until number_of_layers) {
				val layer_input_size = nn_architecture(idx)._1
				val layer_output_size = nn_architecture(idx)._2
				val W = sc.parallelize(for(i <- 0 to layer_output_size-1; j <- 0 to layer_input_size-1) 
					yield ((i.toLong,j.toLong), sweights(idx)(i*m+j)))
				weights = weights ++ Array(W)
				val B = sc.parallelize(for(i <- 0 to layer_output_size-1)
					yield (i.toLong, sbiases(idx)(i)))
				biases = biases ++ Array(B)
			}
			
			for (itr <- 0 until epochs) {
				var A_history: Array[RDD[((Long,Long), Double)]] = Array()
				var Z_history: Array[RDD[((Long,Long), Double)]] = Array()
				var A_curr = input1.map{ case ((i,j),v) => ((j.toLong,i.toLong),v)}
				
				for (idx <- 0 until number_of_layers) {
					var A_prev = A_curr
					var W_curr = weights(idx)
					var b_curr = biases(idx)
					var a_m = nn_architecture(idx)._2
					var b_m = nn_architecture(idx)._1
					var Z_curr = blockMatrixTordd(rddToBlockMatrix(W_curr).multiply(rddToBlockMatrix(A_prev)))
									.map{ case ((i,j),v) => (i,(j,v))}.join(b_curr).map{case (i, ((j,v),b)) => ((i,j),v+b)}
					if(idx == number_of_layers - 1) {
						// sigmoid
						A_curr = Z_curr.map{ case ((i,j),v) => ((i,j),1/(1+math.exp(-v)))}
					}
					else {
						// relu
						A_curr = Z_curr.map{ case ((i,j),v) => ((i,j), math.max(0.0,v))}
					}
					
					A_history = A_history++Array(A_prev)
					Z_history = Z_history++Array(Z_curr)
				}
				var Y_hat = A_curr.map{ case ((i,j),a) => (j,a)}
				
				var dA_prev = input2.map{case (i,y) => (i.toLong, y)}.join(Y_hat)
								.map{ case (i,(y,y_hat)) => ((0L,i),-y/y_hat+(1-y)/(1-y_hat))}
				
				var weight_grads: Array[RDD[((Long,Long), Double)]] = Array()
				var bias_grads: Array[RDD[(Long, Double)]] = Array()
				for (idx <- number_of_layers-1 to 0 by -1) {
					var dA_curr = dA_prev
					
					var A_prev = A_history(idx)
					var Z_curr = Z_history(idx)
					var W_curr = weights(idx)
					var b_curr = biases(idx)
					
					var a_m = nn_architecture(idx)._2
					var b_m = nn_architecture(idx)._1
					var dZ_curr = Z_curr
					if(idx == number_of_layers-1) {
						// sigmoid
						dZ_curr = Z_curr.join(dA_curr).map{ case (i,(z,da)) => {
										val sig = 1/(1+math.exp(-z))
										(i,da*sig*(1-sig))
									}}
					}
					else {
						// relu
						dZ_curr = Z_curr.join(dA_curr).map{ case (i,(z,da)) => {
										var dz = da
										if(z <= 0.0)
											dz = 0.0
										(i,dz)
									}}
					}
					val dZ_curr_block = rddToBlockMatrix(dZ_curr)
					var dW_curr = blockMatrixTordd(dZ_curr_block.multiply(rddToBlockMatrix(A_prev.map{case ((i,j),v) => ((j,i),v)})))
					var db_curr = dZ_curr.map{ case ((i,j),dz) => (i,dz)}.reduceByKey(_+_)
					dA_prev = blockMatrixTordd(rddToBlockMatrix(W_curr.map{case ((i,j),v) => ((j,i),v)}).multiply(dZ_curr_block))
					
					weight_grads = weight_grads++Array(dW_curr)
					bias_grads = bias_grads++Array(db_curr)
				}
				for (idx <- 0 until number_of_layers) {
					weights(idx) = weights(idx).join(weight_grads(number_of_layers-1-idx)).map{ case (i,(w,dw)) => (i, w-learning_rate*dw/n)}
					biases(idx) = biases(idx).join(bias_grads(number_of_layers-1-idx)).map{ case (i,(b,db)) => (i, b-learning_rate*db/n)}
				}
			}
			var A_curr = input3.map{ case ((i,j),v) => ((j.toLong,i.toLong),v)}
			for (idx <- 0 until number_of_layers) {
				var A_prev = A_curr
				var W_curr = weights(idx)
				var b_curr = biases(idx)
				var a_m = nn_architecture(idx)._2
				var b_m = nn_architecture(idx)._1
				var Z_curr = blockMatrixTordd(rddToBlockMatrix(W_curr).multiply(rddToBlockMatrix(A_prev)))
									.map{ case ((i,j),v) => (i,(j,v))}.join(b_curr).map{case (i, ((j,v),b)) => ((i,j),v+b)}
				if(idx == number_of_layers - 1) {
					// sigmoid
					A_curr = Z_curr.map{ case ((i,j),a) => ((i,j),1/(1+math.exp(-a)))}
				}
				else {
					// relu
					A_curr = Z_curr.map{ case ((i,j),a) => ((i,j),math.max(0.0,a))}
				}
			}
			var Y_hat = A_curr.map{ case ((i,j),a) => (j,a)}
			var count = Y_hat.map{ case (i,y) => (i, if(y > 0.5) 1 else 0)}.join(input4.map{case (i,y) => (i.toLong, y)})
				.map{ case (i,(y,y_t)) => if(y==y_t) 1.0 else 0.0}.reduce(_+_)
			println("Test Accuracy: "+count/test_size)
			(System.currentTimeMillis()-t)/1000.0
		}
		
		val spark = SparkSession.builder().config(conf).getOrCreate()
		import spark.implicits._
		
		def testMLlibNN(): Double = {
			val t = System.currentTimeMillis()
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

			val lr = new LogisticRegression()
			  .setMaxIter(epochs)
			  .setRegParam(0.3)
			  .setElasticNetParam(0.8)

			// Fit the model
			val lrModel = lr.fit(training_data)

			val test_data = spark.sql("select Y_test_d._2 as label, X_test_d._2 as features from X_test_d join Y_test_d on X_test_d._1=Y_test_d._1")
				.rdd.map{row => LabeledPoint(
			  	row.getAs[Double]("label"),
			  	row.getAs[org.apache.spark.ml.linalg.Vector]("features")
			)}.toDF.cache()
			val predictions = lrModel.transform(test_data)
			val evaluator = new BinaryClassificationEvaluator()
			val accuracy = evaluator.evaluate(predictions)
			println("Test Accuracy: "+accuracy)
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

		test("Handwritten Neural Network",testHandWrittenNN)
		test("Diablo Comprehension Neural Network",testDiabloNN)
		test("MLlib Handwritten Neural Network",testMLlibHandWrittenNN)
		test("MLlib Logistic Regression Neural Network",testMLlibNN)
		
		sc.stop()
	}
}
