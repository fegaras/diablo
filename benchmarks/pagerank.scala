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
import scala.util.Random

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
    parami(block_dim_size,1000)
    val bSize = 1000
    val repeats = args(0).toInt
	var N = args(1).toInt  // # of graph nodes
	var b = 0.85
	val numIter = 10

    val G = spark_context.textFile(args(2))
              .map( line => { val a = line.split(" ").toList
                              (a(0).toInt,a(1).toInt) } ).cache
	
	def map ( m: BlockMatrix, f: Double => Double ): BlockMatrix
      = new BlockMatrix(m.blocks.map{ case (i,a) => (i,new DenseMatrix(a.numRows,a.numCols,a.toArray.map(f))) },
                        m.rowsPerBlock,m.colsPerBlock)

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
		X.sortBy(x => x._2,false,1).take(30).foreach(println)
		println(X.count)
		(System.currentTimeMillis()-t)/1000.0
	}
	
	def testGraphXIJV (): Double = {
        val t = System.currentTimeMillis()
        try {
            val graph = GraphLoader.edgeListFile(spark_context, args(2))
			val ranks = graph.pageRank(0.0001).vertices
			ranks.sortBy(x => x._2,false,1).take(30).map(println)
			println(ranks.count)
        } catch { case x: Throwable => println(x); return -1.0 }
        (System.currentTimeMillis()-t)/1000.0
    }

	def testGraphXPregel (): Double = {
		val t = System.currentTimeMillis()
		try {
		val graph = GraphLoader.edgeListFile(spark_context, args(2))
		val pagerankGraph: Graph[(Double, Double), Double] = graph
			// Associate the degree with each vertex
			.outerJoinVertices(graph.outDegrees) {
			(vid, vdata, deg) => deg.getOrElse(0)
			}
			// Set the weight on the edges based on the degree
			.mapTriplets( e => 1.0 / e.srcAttr )
			// Set the vertex attributes to (initialPR, delta = 0)
			.mapVertices { (id, attr) => (0.0, 0.0)}
			.cache()
		val ranks = pagerankGraph.pregel((1-b)/b,numIter)(
			(id, attr, msgSum) => {
			val (oldPR, lastDelta) = attr
			val newPR = oldPR + b * msgSum
			(newPR, newPR - oldPR)
			},
			triplet => {
				Iterator((triplet.dstId, triplet.srcAttr._2*triplet.attr))
			},
			(m,n) => m+n
		)
		ranks.vertices.sortBy(x => x._2,false,1).take(30).map(println)
		println(ranks.vertices.count)
		} catch { case x: Throwable => println(x); return -1.0 }
		(System.currentTimeMillis()-t)/1000.0
    }
	
	def testHandWrittenPageRank(): Double = {
		var C = G.map{ case (i,j) => (i,1)}.reduceByKey(_+_)
		var E = G.join(C).map{ case (i,(j,c)) => ((i,j),1.0/c) }
		var P = spark_context.parallelize(0 to N-1).map(i => (i,1.0/N))
		val t = System.currentTimeMillis()
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
		P.sortBy(x => x._2,false,1).take(30).foreach(println)
		println(P.count)
		(System.currentTimeMillis()-t)/1000.0
	}

	def testMLlibDistPageRank(): Double = {
		var C = G.map{ case (i,j) => (i,1)}.reduceByKey(_+_)
		var matrix = G.join(C).map{ case (i,(j,c)) => ((i,j),1.0/c)}
		val coordMat = new CoordinateMatrix(matrix.map{ case ((i,j),v) => MatrixEntry(i,j,v)})
		// Transform the CoordinateMatrix to a BlockMatrix
		val E = coordMat.toBlockMatrix(bSize,bSize).cache()
		val l = Random.shuffle((0 until (N+bSize-1)/bSize).toList)
		var P = new BlockMatrix(spark_context.parallelize(for { i <- l} 
			yield ((i,0),new DenseMatrix(bSize,1,Array.tabulate(bSize){ j => 1.0/N }))),bSize,1).cache
		var k = 0
		val t = System.currentTimeMillis()
		while (k < numIter) {
			k += 1
			var Q = map(P, b*_).cache
			P = map(E.transpose.multiply(Q),_+(1-b)/N).cache
		}
		val vectors = P.toLocalMatrix()
		val ranks = spark_context.parallelize( for(i <- 0 to N-1) yield(i,vectors(i,0)))
		ranks.sortBy(x => x._2,false,1).take(30).foreach(println)
		println(P.blocks.count)
		(System.currentTimeMillis()-t)/1000.0
	}
	
	def testMLlibLocalPageRank(): Double = {
		var C = G.map{ case (i,j) => (i,1)}.reduceByKey(_+_)
		var arr = Array.tabulate(N*N){ i => 0.0 }
		var tmp = G.join(C).map{ case (i,(j,c)) => ((i,j),1.0/c)}.collect
		for(((i,j), t) <- tmp)
			arr(i*N+j) += t
		val E = new DenseMatrix(N,N,arr)
		var P = new DenseVector(Array.tabulate(N){i => 1.0/N})
		val t = System.currentTimeMillis()
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
		val links = G.distinct().groupByKey().cache()
		var ranks = spark_context.parallelize(0 to N-1).map(i => (i,1.0/N))
		val t = System.currentTimeMillis()
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
    test("GraphX",testGraphXPregel)
    test("Hand-written PageRank",testHandWrittenPageRank)
    test("MLlib Local",testMLlibLocalPageRank)
    test("MLlib Distributed",testMLlibDistPageRank)
    test("SparkExample",testSparkExample)
  }
}
