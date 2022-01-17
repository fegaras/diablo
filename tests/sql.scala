import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.sql._
import org.apache.spark.sql.functions._
import Math._

object Test {
  def main ( args: Array[String] ) {
    val conf = new SparkConf().setAppName("Test")
    spark_context = new SparkContext(conf)
    val spark = SparkSession.builder().config(conf).getOrCreate()
    import spark.implicits._
    param(data_frames,true)

    val N = 3000
    val NN = 3000

    var t = System.currentTimeMillis()

    val C = q("""

      var M = tensor(N,NN)[ ((i,j),if (random()>0.5) 0.0 else random()*100) | i <- 0..N-1, j <- 0..NN-1 ];

      var E = tensor*(N)(NN)[ ((i,j),M[i,j]) | i <- 0..N-1, j <- 0..NN-1 ];
      var EE = E;

      //tensor*(N,N)[ ((i,j),(+/c)/c.length) | ((i,k),a) <- E, ((kk,j),b) <- EE, k == kk, let c = a*b, group by (i,j) ];
      tensor*(N,NN)[ ((i,j),a+b) | ((i,j),a) <- E, ((ii,jj),b) <- EE, ii == i, jj == j ];

/*
      var M = tensor(N,NN)[ ((i,j),if (random()>0.5) 0.0 else random()*100) | i <- 0..N-1, j <- 0..NN-1 ];
      var MM = tensor(NN,N)[ ((i,j),if (random()>0.5) 0.0 else random()*100) | i <- 0..NN-1, j <- 0..N-1 ];

      var E = tensor*(N,NN)[ ((i,j),M[i,j]) | i <- 0..N-1, j <- 0..NN-1 ];
      var EE = tensor*(NN,N)[ ((i,j),MM[i,j]) | i <- 0..NN-1, j <- 0..N-1 ];

      tensor*(N,N)[ ((i,j),(+/c)/c.length) | ((i,k),a) <- E, ((kk,j),b) <- EE, k == kk, let c = a*b, group by (i,j) ];


      var M = tensor(N,NN)[ ((i,j),if (random()>0.5) 0 else (random()*100).toInt) | i <- 0..N-1, j <- 0..NN-1 ];
      var MM = tensor(N,NN)[ ((i,j),if (random()>0.5) 0 else (random()*100).toInt) | i <- 0..N-1, j <- 0..NN-1 ];

      var E = tensor*(N,NN)[ ((i,j),M[i,j]) | i <- 0..N-1, j <- 0..NN-1 ];
      var EE = tensor*(N,NN)[ ((i,j),MM[i,j]) | i <- 0..N-1, j <- 0..NN-1 ];

      //var X = tensor*(N,NN)[ ((i,j),a+1) | ((i,j),a) <- E ];
      //tensor*(N,NN)[ ((i,j),a+1) | ((i,j),a) <- E ];

      tensor*(N,NN)[ ((i,j),a+b) | ((i,j),a) <- E, ((ii,jj),b) <- EE, ii == i, jj == j ];
*/
    """)

    C._3.count()
    println("time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

  }
}
