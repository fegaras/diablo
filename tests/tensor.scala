import edu.uta.diablo._

object Test {
  def main ( args: Array[String] ) {
    val N = 20

    def f ( i: Int, j: Int = 1 ): Double = (i*11)%3+j*1.1

    var t = System.currentTimeMillis()

    q("""
        var V1 = tensor(N)[ (i,f(i)) | i <- 0..(N-1) ]              // dense vector
        var V2 = tensor()(N)[ (i,f(i)) | i <- 0..(N-1) ]            // sparse vector
        var M1 = tensor(N,N)[ ((i,j),f(i,j)) | i <- 0..(N-1), j <- 0..(N-1) ]     // dense matrix
        var M2 = tensor(N)(N)[ ((i,j),f(i,j)) | i <- 0..(N-1), j <- 0..(N-1) ]    // dense rows, sparse columns
        var M3 = tensor()(N,N)[ ((i,j),f(i,j)) | i <- 0..(N-1), j <- 0..(N-1) ]   // sparse rows & columns

        V1 = [ (i,v+1) | (i,v) <- V1 ];
        V2 = [ (i,v+1) | (i,v) <- V1 ];
        V1 = [ (i,v+1) | (i,v) <- V2 ];
        V2 = [ (i,v+1) | (i,v) <- V2 ];

        // sparse boolean vectors do not need a values vector
        tensor()(N)[ (i,v<10) | (i,v) <- V1 ];
        tensor()(N)[ (i,v<10) | (i,v) <- V2 ];

        M1 = [ ((i,j),m+1) | ((i,j),m) <- M1 ];
        M2 = [ ((i,j),m+1) | ((i,j),m) <- M1 ];
        M3 = [ ((i,j),m+1) | ((i,j),m) <- M1 ];
        M1 = [ ((i,j),m+1) | ((i,j),m) <- M2 ];
        M2 = [ ((i,j),m+1) | ((i,j),m) <- M2 ];
        M3 = [ ((i,j),m+1) | ((i,j),m) <- M2 ];
        M1 = [ ((i,j),m+1) | ((i,j),m) <- M3 ];
        M2 = [ ((i,j),m+1) | ((i,j),m) <- M3 ];
        M3 = [ ((i,j),m+1) | ((i,j),m) <- M3 ];

        // sparse boolean matrices do not need a values vector
        tensor(N)(N)[ ((i,j),m<10) | ((i,j),m) <- M3 ];
        tensor()(N,N)[ ((i,j),m<10) | ((i,j),m) <- M3 ];

        V1 = [ (i,v+w) | (i,v) <- V1, (j,w) <- V1, i==j ];
        V1 = [ (i,v+w) | (i,v) <- V1, (j,w) <- V2, i==j ];
        V1 = [ (i,v+w) | (i,v) <- V2, (j,w) <- V1, i==j ];
        V1 = [ (i,v+w) | (i,v) <- V2, (j,w) <- V2, i==j ];
        V2 = [ (i,v+w) | (i,v) <- V1, (j,w) <- V1, i==j ];
        V2 = [ (i,v+w) | (i,v) <- V1, (j,w) <- V2, i==j ];
        V2 = [ (i,v+w) | (i,v) <- V2, (j,w) <- V1, i==j ];
        V2 = [ (i,v+w) | (i,v) <- V2, (j,w) <- V2, i==j ];

        M1 = [ ((i,j),m+n) | ((i,j),m) <- M1, ((ii,jj),n) <- M1, ii==i, jj==j ];
        M2 = [ ((i,j),m+n) | ((i,j),m) <- M1, ((ii,jj),n) <- M1, ii==i, jj==j ];
        M3 = [ ((i,j),m+n) | ((i,j),m) <- M1, ((ii,jj),n) <- M1, ii==i, jj==j ];
        M1 = [ ((i,j),m+n) | ((i,j),m) <- M1, ((ii,jj),n) <- M2, ii==i, jj==j ];
        M2 = [ ((i,j),m+n) | ((i,j),m) <- M2, ((ii,jj),n) <- M3, ii==i, jj==j ];
        M3 = [ ((i,j),m+n) | ((i,j),m) <- M3, ((ii,jj),n) <- M3, ii==i, jj==j ];

        // use full scans for sparse matrices
        M1 = [ ((i,j),m+n) | ((i,j),m) <= M1, ((ii,jj),n) <= M1, ii==i, jj==j ];
        M2 = [ ((i,j),m+n) | ((i,j),m) <= M1, ((ii,jj),n) <= M1, ii==i, jj==j ];
        M3 = [ ((i,j),m+n) | ((i,j),m) <= M1, ((ii,jj),n) <= M1, ii==i, jj==j ];
        M1 = [ ((i,j),m+n) | ((i,j),m) <= M1, ((ii,jj),n) <= M2, ii==i, jj==j ];
        M2 = [ ((i,j),m+n) | ((i,j),m) <= M2, ((ii,jj),n) <= M3, ii==i, jj==j ];
        M3 = [ ((i,j),m+n) | ((i,j),m) <= M3, ((ii,jj),n) <= M3, ii==i, jj==j ];

        M1 = [ ((i,j),m+n+k) | ((i,j),m) <= M2, ((ii,jj),n) <= M3,((iii,jjj),k) <= M1, ii==i, jj==j, iii==i, jjj==j ];

        tensor(N)(N)[ ((i,j),m+n < 3) | ((i,j),m) <- M2, ((ii,jj),n) <- M3, ii==i, jj==j ];

        V1 = [ (i,+/m) | ((i,j),m) <- M1, group by i ];
        V1 = [ (i,+/m) | ((i,j),m) <- M2, group by i ];
        V1 = [ (i,+/m) | ((i,j),m) <- M3, group by i ];
        V2 = [ (i,+/m) | ((i,j),m) <- M1, group by i ];
        V2 = [ (i,+/m) | ((i,j),m) <- M2, group by i ];
        V2 = [ (i,+/m) | ((i,j),m) <- M3, group by i ];

        V2 = [ (i,(+/m)/m.length) | ((i,j),m) <- M3, group by i ];

        tensor()(N)[ (i,(+/m)<10) | ((i,j),m) <- M2, group by i ];
        tensor()(N)[ (i,((+/m)/m.length,m,m.length,m.length)) | ((i,j),m) <- M2, group by i ];
        tensor()(N)[ (i,(+/m)<10) | ((i,j),m) <- M1, group by i ];
        tensor()(N)[ (i,(+/m)<10) | ((i,j),m) <- M2, group by i ];
        tensor()(N)[ (i,(+/m)<10) | ((i,j),m) <- M3, group by i ];

        M1 = [ ((i,j),+/v) | ((i,k),m) <- M1, ((kk,j),n) <- M1, kk==k, let v = m*n, group by (i,j) ];
        M2 = [ ((i,j),+/v) | ((i,k),m) <- M1, ((kk,j),n) <- M1, kk==k, let v = m*n, group by (i,j) ];
        M3 = [ ((i,j),+/v) | ((i,k),m) <- M1, ((kk,j),n) <- M1, kk==k, let v = m*n, group by (i,j) ];
        M1 = [ ((i,j),+/v) | ((i,k),m) <- M1, ((kk,j),n) <- M2, kk==k, let v = m*n, group by (i,j) ];
        M2 = [ ((i,j),+/v) | ((i,k),m) <- M2, ((kk,j),n) <- M1, kk==k, let v = m*n, group by (i,j) ];
        M3 = [ ((i,j),+/v) | ((i,k),m) <- M2, ((kk,j),n) <- M3, kk==k, let v = m*n, group by (i,j) ];

        tensor(N)(N)[ ((i,j),(+/v)<10) | ((i,k),m) <- M2, ((kk,j),n) <- M3, kk==k, let v = m*n, group by (i,j) ];

        tensor(N)[ (k,(* /m)/m.length) | ((i,j),m) <- M1, m > 3, group by k:i+j, +/m > 10 ];

        tensor(10)[ (i%10,(+/m)/m.length) | ((i,j),m) <- M1, group by i ];
        tensor(10)[ (i%10,(+/m)/m.length) | ((i,j),m) <- M2, group by i ];
        tensor(10)(20)[ (k,+/m) | ((i,j),m) <- M1, group by k: (i%10,j%20) ];
        tensor(10)(20)[ (k,(+/m)<10) | ((i,j),m) <- M2, group by k: (i%10,j%20) ];
        tensor(10)(20)[ (k,((+/m)/m.length,m,m.length,m.length)) | ((i,j),m) <- M1, group by k: (i%10,j%20) ];
        tensor(10)(20)[ (k,((+/m)/m.length,m,m.length,m.length)) | ((i,j),m) <- M2, group by k: (i%10,j%20) ];

        tensor(N,N,10)[ ((i,j,(i+j)%10),m+1) | ((i,j),m) <- M2 ];
        tensor(N,N)(10)[ ((i,j,(i+j)%10),m+1) | ((i,j),m) <- M2 ];
        tensor(N)(N,10)[ ((i,j,(i+j)%10),m+1) | ((i,j),m) <- M2 ];

        tensor(N,N,10)[ ((i,j,(i+j)%10),+/v) | ((i,k),m) <- M1, ((kk,j),n) <- M1, kk==k, let v = m*n, group by (i,j) ];
        tensor(N)(N,10)[ ((i,j,(i+j)%10),+/v) | ((i,k),m) <- M2, ((kk,j),n) <- M1, kk==k, let v = m*n, group by (i,j) ];

        tensor(N,N)[ ((i,j),tensor(N)[ (ii,v+1) | (ii,v) <- V1 ]) | ((i,j),m) <- M1 ];
        tensor(N,N)[ ((i,j),tensor(N)[ (ii,(v+1,i+j)) | (ii,v) <- V2 ]) | ((i,j),m) <- M2 ];
        tensor(N,N)[ ((i,j),m+1) | ((i,j),m) <- M1, +/[ v | (ii,v) <- V1 ] < 10 ];

        tensor(N,N)[ ((ii,jj),(+/a)/a.length)
                   | ((i,j),a) <- M1, di <- (-1)..1, dj <- (-1)..1,
                     let ii = i+di, let jj = j+dj, group by (ii,jj) ];

        tensor(N,N)[ ((ii,jj),(+/a)/a.length)
                   | ((i,j),a) <- M2, di <- (-1)..1, dj <- (-1)..1,
                     let ii = i+di, let jj = j+dj, group by (ii,jj) ];

        tensor(N)[ (i,tensor(N) w) | ((i,j),m) <- M2, let w = (j,m), group by i ];

        map[ (i,v+1) | (i,v) <- V2 ];

        tensor(N,N)[ ((i,j),m+1) | ((i,j),m) <- M1, (+/[ v | ((ii,jj),v) <- M1, ii == i, jj == j ]) < 10 ];

        +/[ m | ((i,j),m) <- M1, (+/[ v | ((ii,jj),v) <- M1, ii == i, jj == j ]) < 10 ];

    """)

      println((System.currentTimeMillis()-t)/1000.0)
  }
}
