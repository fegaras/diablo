# DIABLO: a Data-Intensive Array-Based Loop Optimizer

A compiler from array-based loops to distributed data parallel programs.
Arrays are stored as distributed collections of square tiles.
It works on Apache Spark and Scala's Parallel collections.

### Installation on Spark

DIABLO depends on Scala 2.12 and Spark 3.0. To compile DIABLO, use ``sbt package`` or ``mvn install``.
To test  on Spark:
```bash
export SPARK_HOME= ... path to Spark home ...
cd tests/
./build test.scala
./run Test
```

## Matrix multiplication using loops:

```scala
val X = q("""
          var M = tensor*(n,n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ];
          var N = tensor*(n,n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ];
          var R = M;

          for i = 0, n-1 do
              for j = 0, n-1 do {
                   R[i,j] = 0.0;
                   for k = 0, n-1 do
                       R[i,j] += M[i,k]*N[k,j];
              };
          R;
        """)
```

## Matrix multiplication using array comprehensions:

```scala
val X = q("""
          tensor*(n,n)[ ((i,j),+/v) | ((i,k),m) <- M, ((kk,j),n) <- N, kk == k, let v = m*n, group by (i,j) ];
          """)
```

## Matrix factorization example:

```scala
    q("""
      var R = tensor*(n,m)[ ((i,j),random()) | i <- 0..n-1, j <- 0..m-1 ];
      var P = tensor*(n,l)[ ((i,j),random()) | i <- 0..n-1, j <- 0..l-1 ];
      var Q = tensor*(l,m)[ ((i,j),random()) | i <- 0..l-1, j <- 0..m-1 ];
      var pq = R;
      var E = R;

      var a: Double = 0.002;
      var b: Double = 0.02;

      for i = 0, n-1 do
          for k = 0, l-1 do
              P[i,k] = random();

      for k = 0, l-1 do
          for j = 0, m-1 do
              Q[k,j] = random();

      var steps: Int = 0;
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
```
