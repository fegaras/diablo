import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import Math._

object Test {
  def main ( args: Array[String] ) {
    val conf = new SparkConf().setAppName("Test")
    spark_context = new SparkContext(conf)

    parami(number_of_partitions,10)
    parami(block_dim_size,10)

    q("""
        var M = tensor*(100,100)[ ((i,j),i*100.0+j) | i <- 0..99, j <- 0..99 ];
        var V = tensor*(100)[ (i,i*100.0) | i <- 0..99 ];
        var N = M;
        var R = M;

        for i = 0, 99 do
            for j = 0, 99 do
               V[i] += M[i,j];

        for i = 0, 99 do
            for j = 0, 99 do
               M[i,j] += 1.0;

        for i = 0, 99 do
            for j = 0, 99 do
               R[i,j] = M[i,j]+N[i,j];

         for i = 0, 99 do
            for j = 0, 99 do {
               R[i,j] = 0.0;
               for k = 0, 99 do
                  R[i,j] += M[i,k]*N[k,j];
            };
    """)

    q("""
          var n = 100;
          var M = tensor*(n,n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ];
          var N = tensor*(n,n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ];
          var R = M;

          for i = 0, M.rows-1 do
              for j = 0, N.cols-1 do {
                   R[i,j] = 0.0;
                   for k = 0, M.cols-1 do
                       R[i,j] += M[i,k]*N[k,j];
              };

          for i = 0, M.rows-1 do
              for j = 0, N.cols-1 do {
                   R[i,j] = Double.MaxValue;
                   for k = 0, M.cols-1 do
                       R[i,j] = min(R[i,j],M[i,k]+N[k,j]);
              };

          R;
        """)

    var t = System.currentTimeMillis()

    val (p,s) = q("""
      var n = 100; var m = n; var l = 10;

      var a = 0.002;
      var b = 0.02;

      var R = tensor*(n,m)[ ((i,j),random()) | i <- 0..n-1, j <- 0..m-1 ];
      var P = tensor*(n,l)[ ((i,j),random()) | i <- 0..n-1, j <- 0..l-1 ];
      var Q = tensor*(l,m)[ ((i,j),random()) | i <- 0..l-1, j <- 0..m-1 ];
      cache(R);
      var pq = R
      var E = R;

      var steps = 0;
      while ( steps < 100 ) {
        steps += 1;
        for i = 0, n-1 do
            for j = 0, m-1 do {
                pq[i,j] = 0.0;
                for k = 0, l-1 do
                    pq[i,j] += P[i,k]*Q[k,j];
                E[i,j] = R[i,j]-pq[i,j];
                for k = 0, l-1 do {
                    P[i,k] += a*(2*E[i,j]*Q[k,j]-b*P[i,k]);
                    Q[k,j] += a*(2*E[i,j]*P[i,k]-b*Q[k,j]);
                };
            };
        cache(E); cache(P); cache(Q);
      };
      (P,Q);
    """)

    println("@@@ "+p._3.count()+" "+s._3.count())
    println("time: "+(System.currentTimeMillis()-t)/1000.0+" secs")
  }
}
