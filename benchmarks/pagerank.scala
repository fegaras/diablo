import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import Math._
import org.apache.log4j._
import scala.collection.Seq
import org.apache.spark.graphx.{Edge, Graph, GraphLoader}
import org.apache.spark.sql._
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._

object PageRank {
  def main ( args: Array[String] ) {
    val conf = new SparkConf().setAppName("PageRank")
    spark_context = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.ERROR)
    val spark = SparkSession.builder().config(conf).getOrCreate()
    import spark.implicits._

    parami(number_of_partitions,10)
    parami(block_dim_size,1024)
    val bSize = 1024
    val repeats = 1
    var N = args(0);  // # of graph nodes
	var b = 0.85;
	val numIter = 10;

    val G = spark_context.textFile(args(1))
              .map( line => { val a = line.split(" ").toList
                              (a(0).toInt,a(1).toInt) } ).cache
	
	def testPageRankDiabloLoop(): Double = {
		val t = System.currentTimeMillis()
		var X = q("""
		  // count outgoing neighbors
		  var C = rdd[ (i,j.length) | (i,j) <- G, group by i ];
		  //var C = tensor*(N)[ (i,j.length) | (i,j) <- G, group by i ];
		  // graph matrix is sparse
		  var E = tensor*(N)(N)[ ((i,j),1.0/c) | (i,j) <- G, (ii,c) <- C, ii == i ];
		  // pagerank
		  var P = tensor*(N)[ (i,1.0/N) | i <- 0..N-1 ];
		  var k = 0;
		  while (k < numIter) {
		    k += 1;
		    var Q = P;
		    for i = 0, N-1 do
		        P[i] = (1-b)/N;
		    for i = 0, N-1 do
		        for j = 0, N-1 do
		            P[i] += b*E[j,i]*Q[j];
		  };
		  // convert pageranks to a plain RDD
		  rdd[ (i,v) | (i,v) <- P ];
		 """)
		// print top-30 pageranks
		X.sortBy(x => x._2,false,1).take(30).foreach(println)
		println(X.count)
		(System.currentTimeMillis()-t)/1000.0
	}
	
	def testPageRankDiablo(): Double = {
		val t = System.currentTimeMillis()
		val graph = G
		var X = q("""
		  // count outgoing neighbors
		  var C = rdd[ (i,j.length) | (i,j) <- graph, group by i ];
		  // graph matrix is sparse
		  var E = tensor*(N)(N)[ ((i,j),1.0/c) | (i,j) <- graph, (ii,c) <- C, ii == i ];
		  // pagerank
		  var P = tensor*(N)[ (i,1.0/N) | i <- 0..N-1 ];
		  var k = 0;
		  while (k < numIter) {
		    k += 1;
		    var Q = P;
		    P = tensor*(N)[ (j,+/v + (1-b)/N) | ((i,j),e) <- E, (ii,q) <- Q, i==ii, let v = b*e*q, group by j ];
		  };
		  // convert pageranks to a plain RDD
		  rdd[ (i,v) | (i,v) <- P ];

		 """)
		// print top-30 pageranks
		println("Ranks:")
		X.sortBy(x => x._2,false,1).take(30).foreach(println)
		println(X.count)
		(System.currentTimeMillis()-t)/1000.0
	}
	
	def testGraphXIJV (): Double = {
          val t = System.currentTimeMillis()
          try {
                val graph = GraphLoader.edgeListFile(spark_context, args(1))
		val ranks = graph.pageRank(0.0001).vertices
		ranks.sortBy(x => x._2,false,1).take(30).map(println)
		println(ranks.count)
          } catch { case x: Throwable => println(x); return -1.0 }
          (System.currentTimeMillis()-t)/1000.0
        }
	
	def testHandWrittenPageRank(): Double = {
		val t = System.currentTimeMillis()
		var C = G.map{ case (i,j) => (i,1)}.reduceByKey(_+_)
		println(C.count)
		var E = G.join(C).map{ case (i,(j,c)) => ((i,j),1.0/c) }
		var P = spark_context.parallelize(0 to N-1).map(i => (i,1.0/N))
		var k = 0
		while(k < numIter) {
			k += 1
			P = E.map{ case ((i,j),e) => (i, (j,e)) }
                             .join(P)
                             .map{ case (i,((j,e),p)) => (j, b*e*p) }
                             .reduceByKey(_+_)
                             .map{case (i,p) => (i,p+(1-b)/N)}
		}
		// print top-30 pageranks
		println("Ranks:")
		P.sortBy(x => x._2,false,1).take(30).foreach(println)
		println(P.count)
		(System.currentTimeMillis()-t)/1000.0
	}
	
	def testMLlibDistPageRank(): Double = {
		val t = System.currentTimeMillis()
		var C = G.map{ case (i,j) => (i,1)}.reduceByKey(_+_)
		var matrix = spark_context.parallelize(for(i <- 0 to N-1; j <- 0 to N-1) yield ((i,j), 0.0))
		var tmp = G.join(C).map{ case (i,(j,c)) => ((i,j),1.0/c)}
		matrix = matrix.join(tmp).map{ case ((i,j),(m,c)) => ((i,j),m+c)}
		val coordMat = new CoordinateMatrix(matrix.map{ case ((i,j),v) => MatrixEntry(i,j,v)})
		// Transform the CoordinateMatrix to a BlockMatrix
		val E = coordMat.toBlockMatrix(bSize,bSize).cache()
		var vector = spark_context.parallelize(for(i <- 0 to N-1) yield MatrixEntry(i,0, 1.0/N))
		val coordVec = new CoordinateMatrix(vector)
		var P = coordVec.toBlockMatrix(bSize,1)
		var k = 0
		while (k < numIter) {
                  k += 1
		  var Q = new CoordinateMatrix(P.toCoordinateMatrix().entries
                                     .map(entry => MatrixEntry(entry.i,entry.j,b*entry.value)))
                                .toBlockMatrix(bSize,1)
		  P = new CoordinateMatrix(E.transpose.multiply(Q).toCoordinateMatrix().entries
                                     .map(entry => MatrixEntry(entry.i,entry.j,entry.value+(1-b)/N)))
                                .toBlockMatrix(bSize,1)
		}
		val vectors = P.toLocalMatrix()
		val ranks = spark_context.parallelize( for(i <- 0 to N-1) yield(i,vectors(i,0)))
		ranks.sortBy(x => x._2,false,1).take(30).foreach(println)
		(System.currentTimeMillis()-t)/1000.0
	}
	
	def testMLlibLocalPageRank(): Double = {
		val t = System.currentTimeMillis()
		var C = G.map{ case (i,j) => (i,1)}.reduceByKey(_+_)
		var arr = Array.tabulate(N*N){ i => 0.0 }
		var tmp = G.join(C).map{ case (i,(j,c)) => ((i,j),1.0/c)}.collect
		for(((i,j), t) <- tmp)
			arr(i*N+j) += t
		val E = new DenseMatrix(N,N,arr)
		var P = new DenseVector(Array.tabulate(N){i => 1.0/N})
		var k = 0
		while(k < numIter) {
			k += 1
			var Q = new DenseVector(P.toArray.map(i => i*b))
			P = new DenseVector(E.multiply(Q).toArray.map{i => i+(1-b)/N})
		}
		// print top-30 pageranks
		val ranks = spark_context.parallelize( for(i <- 0 to N-1) yield (i,P(i)))
		ranks.sortBy(x => x._2,false,1).take(30).foreach(println)
		println(ranks.count)
		(System.currentTimeMillis()-t)/1000.0
	}
	
	def testSparkExample(): Double = {
		val t = System.currentTimeMillis()
		val links = G.distinct().groupByKey().cache()
		var ranks = spark_context.parallelize(0 to N-1).map(i => (i,1.0/N))
		for (i <- 1 to numIter) {
			val contribs = links.join(ranks).values.flatMap{ case (urls, rank) =>
				val size = urls.size
				urls.map(url => (url, rank / size))
			}
			ranks = contribs.reduceByKey(_ + _).mapValues((1-b)/N + b * _)
		}
		ranks.sortBy(x => x._2,false,1).take(30).foreach(println)
		println(ranks.count)
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
    
    test("Diablo loop PageRank",testPageRankDiabloLoop)
    test("Diablo PageRank",testPageRankDiablo)
    test("GraphX",testGraphXIJV)
    test("Hand-written PageRank",testHandWrittenPageRank)
    test("MLlib Local",testMLlibLocalPageRank)
    test("MLlib Distributed",testMLlibDistPageRank)
    test("SparkExample",testSparkExample)
  }
}
