import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._
import org.apache.log4j._
import org.apache.hadoop.fs._
import scala.util.Random
import Math._


object Factorization extends Serializable {
  /* The size of an object */
  def sizeof ( x: AnyRef ): Long = {
    import org.apache.spark.util.SizeEstimator.estimate
    estimate(x)
  }

  val a = 0.002
  val b = 0.02

  def main ( args: Array[String] ) {
    val repeats = args(0).toInt
    val n = args(1).toInt
    val m = args(2).toInt
    val d = args(3).toInt  // number of attributes
    parami(block_dim_size,1000)  // size of each dimension in a block
    val validate_output = false
    val N = 1000

    val conf = new SparkConf().setAppName("tiles")
    spark_context = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.ERROR)

    def randomTile ( nd: Int, md: Int ): DenseMatrix = {
      val max = 10
      val rand = new Random()
      new DenseMatrix(nd,md,Array.tabulate(nd*md){ i => if(rand.nextDouble() > 0.01) 0.0 else rand.nextDouble()*max })
    }

    def randomMatrix ( rows: Int, cols: Int ): RDD[((Int, Int),org.apache.spark.mllib.linalg.Matrix)] = {
      val l = Random.shuffle((0 until (rows+N-1)/N).toList)
      val r = Random.shuffle((0 until (cols+N-1)/N).toList)
      spark_context.parallelize(for { i <- l; j <- r } yield (i,j))
                   .map{ case (i,j) => ((i,j),randomTile(if ((i+1)*N > rows) rows%N else N,
                                                         if ((j+1)*N > cols) cols%N else N)) }
    }

    val Rm = randomMatrix(n,m).cache()
    val Pm = randomMatrix(n,d).cache()
    val Qm = randomMatrix(d,m).cache()

    val R = new BlockMatrix(Rm,N,N)
    val Pinit = new BlockMatrix(Pm,N,N)
    val Qinit = new BlockMatrix(Qm,N,N)

    type tiled_matrix = ((Int,Int),EmptyTuple,RDD[((Int,Int),((Int,Int),EmptyTuple,Array[Double]))])

    val et = EmptyTuple()

    val RR = ((n,m),et,Rm.map{ case ((i,j),a) => ((i,j),((a.numRows,a.numCols),et,a.transpose.toArray)) })
    val PPinit = ((n,d),et,Pm.map{ case ((i,j),a) => ((i,j),((a.numRows,a.numCols),et,a.transpose.toArray)) })
    val QQinit = ((d,m),et,Qm.map{ case ((i,j),a) => ((i,j),((a.numRows,a.numCols),et,a.transpose.toArray)) })

    val rand = new Random()
    def random () = rand.nextDouble()*10

    val RSparse = q("tensor*(n)(m)[ ((i,j),RR[i,j]) | i <- 0..(n-1), j <- 0..(m-1) ]")
    val PinitSparse = q("tensor*(n)(d)[ ((i,j),PPinit[i,j]) | i <- 0..(n-1), j <- 0..(d-1) ]")
    val QinitSparse = q("tensor*(d)(m)[ ((i,j),QQinit[i,j]) | i <- 0..(d-1), j <- 0..(m-1) ]")

    def map ( m: BlockMatrix, f: Double => Double ): BlockMatrix
      = new BlockMatrix(m.blocks.map{ case (i,a) => (i,new DenseMatrix(a.numRows,a.numCols,a.toArray.map(f))) },
                        m.rowsPerBlock,m.colsPerBlock)

    def testFactorizationMLlib (): Double = {
      val t = System.currentTimeMillis()
      var E = R
      var P = Pinit
      var Q = Qinit
      try {
        E = R.subtract(P.multiply(Q))
        P = P.add(map(map(E.multiply(Q.transpose),2*_).subtract(map(P,b*_)),a*_))
        Q = Q.add(map(map(E.transpose.multiply(P),2*_).transpose.subtract(map(Q,b*_)),a*_))
      val x = E.blocks.count+P.blocks.count+Q.blocks.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testFactorizationDiablo (): Double = {
      val t = System.currentTimeMillis()
      var E = RR
      var P = PPinit
      var Q = QQinit
      try {
        q("""
          var E1 = tensor*(n,m)[ ((i,j),+/v) | ((i,k),p) <- P, ((kk,j),q) <- Q,
                                               kk == k, let v = p*q, group by (i,j) ];
          var E2 = tensor*(n,m)[ ((i,j),r-v) | ((i,j),r) <- E, ((ii,jj),v) <- E1,
                                          ii == i, jj == j];
          var P1 = tensor*(n,d)[ ((i,k),+/v)
                          | ((i,j),e) <- E2, ((k,jj),q) <- Q, jj == j,
                            let v = 2*a*e*q, group by (i,k) ];
          var P2 = tensor*(n,d)[ ((i,k),p1+p-a*b*p)
                          | ((i,k),p1) <- P1, ((ii,kk),p) <-P, ii==i,kk==k ];
          P = P2;
          var Q1 = tensor*(d,m)[ ((k,j),+/v)
                          | ((i,j),e) <- E2, ((ii,k),p) <- P, ii == i,
                            let v = 2*a*e*p, group by (k,j) ];
          var Q2 = tensor*(d,m)[ ((k,j),q1+q-a*b*q)
                          | ((k,j),q1) <- Q1, ((kk,jj),q) <-Q, jj==j,kk==k ];
          Q = Q2;
          """)
        validate(P,Q)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testFactorizationDiabloSparseToDense(): Double = {
      val t = System.currentTimeMillis()
      var E = RSparse
      var P = PPinit
      var Q = QQinit
      try {
        val (p2,q2) = q("""
          var E1 = tensor*(n,m)[ ((i,j),+/v) | ((i,k),p) <- P, ((kk,j),q) <- Q,
                                               kk == k, let v = p*q, group by (i,j) ];
          var E2 = tensor*(n,m)[ ((i,j),r-v) | ((i,j),r) <= E, ((ii,jj),v) <- E1,
                                               ii == i, jj == j];
          var P1 = tensor*(n,d)[ ((i,k),+/v)
                               | ((i,j),e) <- E2, ((k,jj),q) <- Q, jj == j,
                                 let v = 2*a*e*q, group by (i,k) ];
          var P2 = tensor*(n,d)[ ((i,k),p1+p-a*b*p)
                               | ((i,k),p1) <- P1, ((ii,kk),p) <-P, ii==i,kk==k ];
          var Q1 = tensor*(d,m)[ ((k,j),+/v)
                               | ((i,j),e) <- E2, ((ii,k),p) <- P, ii == i,
                                 let v = 2*a*e*p, group by (k,j) ];
          var Q2 = tensor*(d,m)[ ((k,j),q1+q-a*b*q)
                               | ((k,j),q1) <- Q1, ((kk,jj),q) <-Q, jj==j,kk==k ];
          (P2,Q2)
          """)
        val x = p2._3.count+q2._3.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testFactorizationDiabloSparseToSparse(): Double = {
      val t = System.currentTimeMillis()
      var E = RSparse
      var P = PinitSparse
      var Q = QinitSparse
      try {
        val (p2,q2) = q("""
          var E1 = tensor*(n,m)[ ((i,j),+/v) | ((i,k),p) <- P, ((kk,j),q) <- Q,
                                               kk == k, let v = p*q, group by (i,j) ];
          var E2 = tensor*(n,m)[ ((i,j),r-v) | ((i,j),r) <= E, ((ii,jj),v) <= E1,
                                               ii == i, jj == j];
          var P1 = tensor*(n,d)[ ((i,k),+/v)
                               | ((i,j),e) <- E2, ((k,jj),q) <- Q, jj == j,
                                 let v = 2*a*e*q, group by (i,k) ];
          var P2 = tensor*(n,d)[ ((i,k),p1+p-a*b*p)
                               | ((i,k),p1) <= P1, ((ii,kk),p) <= P, ii==i,kk==k ];
          var Q1 = tensor*(d,m)[ ((k,j),+/v)
                               | ((i,j),e) <- E2, ((ii,k),p) <- P, ii == i,
                                 let v = 2*a*e*p, group by (k,j) ];
          var Q2 = tensor*(d,m)[ ((k,j),q1+q-a*b*q)
                               | ((k,j),q1) <= Q1, ((kk,jj),q) <= Q, jj==j,kk==k ];
          (P2,Q2)
          """)
        val x = p2._3.count+q2._3.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testFactorizationDiabloSparseToSparseDense(): Double = {
      val t = System.currentTimeMillis()
      var E = RSparse
      var P = PinitSparse
      var Q = QQinit
      try {
        val (p2,q2) = q("""
          var E1 = tensor*(n,m)[ ((i,j),+/v) | ((i,k),p) <- P, ((kk,j),q) <- Q,
                                               kk == k, let v = p*q, group by (i,j) ];
          var E2 = tensor*(n,m)[ ((i,j),r-v) | ((i,j),r) <= E, ((ii,jj),v) <= E1,
                                               ii == i, jj == j];
          var P1 = tensor*(n,d)[ ((i,k),+/v)
                               | ((i,j),e) <- E2, ((k,jj),q) <- Q, jj == j,
                                 let v = 2*a*e*q, group by (i,k) ];
          var P2 = tensor*(n,d)[ ((i,k),p1+p-a*b*p)
                               | ((i,k),p1) <- P1, ((ii,kk),p) <= P, ii==i,kk==k ];
          var Q1 = tensor*(d,m)[ ((k,j),+/v)
                               | ((i,j),e) <- E2, ((ii,k),p) <- P, ii == i,
                                 let v = 2*a*e*p, group by (k,j) ];
          var Q2 = tensor*(d,m)[ ((k,j),q1+q-a*b*q)
                               | ((k,j),q1) <= Q1, ((kk,jj),q) <- Q, jj==j,kk==k ];
          (P2,Q2)
          """)
        val x = p2._3.count+q2._3.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testFactorizationDiabloLoop (): Double = {
      val t = System.currentTimeMillis()
      var E = RR
      var R = RR
      var P = PPinit
      var Q = QQinit
      var pq = E
      try {
        q("""
          for i = 0, n-1 do
             for j = 0, m-1 do {
                pq[i,j] = 0.0;
                for k = 0, d-1 do
                    pq[i,j] += P[i,k]*Q[k,j];
                E[i,j] = R[i,j]-pq[i,j];
                for k = 0, d-1 do {
                    P[i,k] += a*(2*E[i,j]*Q[k,j]-b*P[i,k]);
                    Q[k,j] += a*(2*E[i,j]*P[i,k]-b*Q[k,j]);
                };
             };
          (P,Q);
          """)
        validate(P,Q)
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def validate ( M1: tiled_matrix, M2: tiled_matrix ) = {
      if (!validate_output)
	M1._3.count()+M2._3.count()
      else {
	var P = Pinit
	var Q = Qinit
	var E = R.subtract(P.multiply(Q))
	P = P.add(map(map(E.multiply(Q.transpose),2*_).subtract(map(P,b*_)),a*_))
	Q = Q.add(map(map(E.transpose.multiply(P),2*_).transpose.subtract(map(Q,b*_)),a*_))
	println("Validating ...")
	compareMatrix(M1, P.toLocalMatrix())
	compareMatrix(M2, Q.toLocalMatrix())
	def compareMatrix(A: tiled_matrix, B: Matrix) {
	  var C = A._3.collect
	  for { ((ii,jj),((nd,md),_,a)) <- C
		i <- 0 until nd
		j <- 0 until md } {
	    val ci = ii*N+nd
	    if (Math.abs(a(i*md+j)-B(ii*N+i,jj*N+j)) > 0.3)
	      println("Element (%d,%d)(%d,%d) is wrong: %.3f %.3f".format(ii,jj,i,j,a(i*md+j),B(ii*N+i,jj*N+j)))
	  }
	}
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
      print("*** %s cores=%d n=%d m=%d d=%d N=%d %.2f GB ".format(name,cores,n,m,d,N,
                                               (8.0*n.toDouble*n)/(1024.0*1024.0*1024.0)))
      println("tries=%d %.3f secs".format(i,s))
    }

    test("MLlib Factorization",testFactorizationMLlib)
    test("DIABLO Factorization Dense to Dense",testFactorizationDiablo)
    test("DIABLO Factorization with loops",testFactorizationDiabloLoop)
    test("DIABLO Factorization Sparse to Dense",testFactorizationDiabloSparseToDense)
    test("DIABLO Factorization Sparse to Sparse",testFactorizationDiabloSparseToSparse)
    test("DIABLO Factorization Sparse to Sparse-Dense",testFactorizationDiabloSparseToSparseDense)

    spark_context.stop()
  }
}
