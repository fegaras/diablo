import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import Math._

object Test {
  def main ( args: Array[String] ) {
    val conf = new SparkConf().setAppName("Test")
    val spark_context = new SparkContext(conf)

    parami(tileSize,10) // each tile has size N*N
    val N = 10

    type Tiled = (Int,Int,RDD[((Int,Int),Array[Double])])

    def print ( x: Tiled ) {
      val (n,m,s) = x
      val M = s.collect
      for { ((ii,jj),a) <- M;
            i <- 0 until N;
            j <- 0 until N }
           if (ii*N+i < n && jj*N+j < m)
             println("%d,%d,%.1f".format(ii*N+i,jj*N+j,a(i*N+j)))
    }

    //param(groupByJoin,false)

    q("""
      {
        var L: list[(Int,Double)] = [ (k,(+/i)/i.length.toDouble) | i <- 0..99, group by k: i%10 ];
        var R = [ (i,(+/x)/x.length) | (i,x) <- L, x > 2, x <= 10, group by i ];
        var S = R;
        R = [ (i,x+y) | (i,x) <- S, (j,y) <- R, i == j ];
      };
      {
        var M = matrix(100,100)[ ((i,j),random()) | i <- 0..99, j <- 0..99 ];
        var V = vector(100)[ (j,+/m) | ((i,j),m) <- M, group by j ];
        var N = M;
        M = [ ((i,j),m+1) | ((i,j),m) <- M, m > 10 ];
        M = [ ((j,i),m+1) | ((i,j),m) <- M ];
        M = [ (((i+1)%20,j),m+1) | ((i,j),m) <- M ];
        M = [ ((i,j),m+n) | ((i,j),m) <- M, ((ii,jj),n) <- N, ii == i, jj == j ];
        M = [ (k,+/w) | i <- 0..99, j <- 0..99, let w = 1.0, group by k: (i,j) ];
        M = [ ((i,j),+/v) | ((i,k),m) <- M, ((kk,j),n) <- N, kk == k, let v = m*n, group by (i,j) ];
        V = [ (i,1.0*m.length) | ((i,j),m) <- M, group by i ];
        V = [ (i,(+/m)/m.length) | ((i,j),m) <- M, group by i ];
      };
      {
        var R = rdd[ (i,random()*100) | i <- 0..99 ];
        R = [ (i,+/x) | (i,x) <- R, x > 2, x <= 10, group by i ];
        var S = R;
        R = [ (i,x+y) | (i,x) <- S, (j,y) <- R, i == j, x>3 ];
        R = [ (i,x+y) | (i,x) <- S, (j,y) <- R, x>2, x+y<4 ];
      };
      {
        var M: matrix[Double] = tiled(100,100)[ ((i,j),i*100.0+j) | i <- 0..99, j <- 0..99 ];
        var N = M;
        var Q = M;
        M = [ (k,+/w) | i <- 0..99, j <- 0..99, let w = 1.0, group by k: (i,j) ];
        M = [ ((i,j),+/v) | ((i,k),m) <- M, ((kk,j),n) <- N, kk == k, let v = m*n, group by (i,j) ];
        M = [ (k,+/v) | ((i,k),m) <- M, ((kk,j),n) <- N, kk == k, let v = m*n, group by k:(i,j) ];
        M = [ ((i,j),+/v) | ((jj,l),q) <- Q, ((kk,j),n) <- N, ((i,k),m) <- M, kk == k, jj == j, let v = m*n*q, group by (i,j) ];
        // doesn't give groupByJoin:
        M = [ ((i,j),+/v) | ((i,k),m) <- M, ((kk,j),n) <- N, ((jj,l),q) <- Q, kk == k, jj == j, let v = m*n*q, group by (i,j) ];
        M = [ ((j,i),m) | ((i,j),m) <- M ];
        M = [ ((i,j),m+n) | ((i,j),m) <- M, ((ii,jj),n) <- N, ii == i, jj == j ];
        M = [ ((i,l),m+n*q) | ((i,k),m) <- M, ((kk,j),n) <- N, ((jj,l),q) <- Q, kk == k, jj == j ];
        M = [ ((j%10,i),m) | ((i,j),m) <- M, ((ii,jj),n) <- N, ii == i, jj == j ];
        var V = vector(100)[ (i,+/m) | ((i,j),m) <- M, group by i ];
        var X = matrix(100,100) [ ((j,i),m+1) | ((i,j),m) <- M ];
      };
      {
        var M = tiled(100,100)[ ((i,j),i*100.0+j) | i <- 0..99, j <- 0..99 ];
        var N = M;
        var R = M;

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
      };
      0
    """)

    val X = q("""
          var n = 100;
          var M = tiled(n,n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ];
          var N = tiled(n,n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ];
          var R = M;

          for i = 0, n-1 do
              for j = 0, n-1 do {
                   R[i,j] = 0.0;
                   for k = 0, n-1 do
                       R[i,j] += M[i,k]*N[k,j];
              };
          R;
        """)

    q("""
      var n = 100; var m = n; var l = 10;
      var R = tiled(n,m)[ ((i,j),random()) | i <- 0..n-1, j <- 0..m-1 ];
      var P = tiled(n,l)[ ((i,j),random()) | i <- 0..n-1, j <- 0..l-1 ];
      var Q = tiled(l,m)[ ((i,j),random()) | i <- 0..l-1, j <- 0..m-1 ];
      var pq = R
      var E = R;

      var a = 0.002;
      var b = 0.02;

      for i = 0, n-1 do
          for k = 0, l-1 do
              P[i,k] = random();

      for k = 0, l-1 do
          for j = 0, m-1 do
              Q[k,j] = random();

      var steps = 0;
      while ( steps < 10 ) {
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
      };
      (P,Q);
    """)

  }
}
