# DIABLO: a Data-Intensive Array-Based Loop Optimizer

A compiler from array-based loops to distributed data parallel programs that can run on Apache Spark.
Arrays are stored as distributed collections of blocks of fixed size (ie, square tiles for matrices).
It works on Apache Spark and on Scala's Parallel collections.

### Installation on Spark

DIABLO depends on Scala 2.12.15, Spark 3.2.1, JDK 11, and sbt 1.6.2. To compile DIABLO, use ``sbt package`` or ``mvn install``.
To test  on Spark:
```bash
export SPARK_HOME= ... path to Spark home ...
cd tests/
./build tiled.scala
./run Test
```
## Data Model

### Abstract Types

| type | meaning |
| ---- | ------- |
| array<sub>n</sub>[T] | An array with n dimensions and elements of type T |
| vector[T] | same as array1[T]: a vector |
| matrix[T] | same as array2[T]: a matrix |
| list[T] | a list of elements of type T |
| map[K,T] | a map that maps keys of type K to values of type T |

### Storage Constructors

e: `List[((Int,...,Int),T)]`<br/>
d<sub>i</sub>: `Int`       (dense dimension)<br/>
s<sub>i</sub>: `Int`       (sparse dimension)<br/>

| constructor | abstract type | meaning |
| ---- | ---- | ------- |
| tensor(d<sub>1</sub>,...,d<sub>n</sub>)(s<sub>1</sub>,...,s<sub>m</sub>) e | array<sub>n+m</sub>[T] | a tensor with n dense dimensions and m sparse dimensions |
| tensor(d<sub>1</sub>,...,d<sub>n</sub>) e | array<sub>n</sub>[T]  | same as tensor(d<sub>1</sub>,...,d<sub>n</sub>)() e (a dense tensor) |
| tensor*(d<sub>1</sub>,...,d<sub>n</sub>)(s<sub>1</sub>,...,s<sub>m</sub>) e | array<sub>n+m</sub>[T]  | a distributed block tensor with n dense dimensions and m sparse dimensions |
| tensor*(d<sub>1</sub>,...,d<sub>n</sub>) e | array<sub>n</sub>[T]  | same as tensor*(d<sub>1</sub>,...,d<sub>n</sub>)() e (a distributed block dense tensor) |
| list* v | list[T] | a distributed list, where v: List[T] |
| map* v | map[K,T] | a distributed map, where v: List[(K,T)] |

A dense tensor, tensor(d<sub>1</sub>,...,d<sub>n</sub>) e,  is stored as (d<sub>1</sub>,...,d<sub>n</sub>,v), where v is Array[T] (the array in row-major format).<br/>
A sparse tensor, tensor(d<sub>1</sub>,...,d<sub>n</sub>)(s<sub>1</sub>,...,s<sub>m</sub>) e,
is stored in sparse row format as (d<sub>1</sub>,...,d<sub>n</sub>,s<sub>1</sub>,...,s<sub>m</sub>,dense,sparse,values), where:
* dense: Array[Int] is a dense array with dimensions (d<sub>1</sub>,...,d<sub>n</sub>) in row-major format that points to the sparse array
* sparse: Array[Int] contains the sparse indices
* values: Array[T] contains the tensor values and has the same size as sparse

For example, a 4-dimensional array `A` constructed using `tensor(d1,d2)(s1,s2)` has value
`A[i,j,k,l]` equal to `values[z]` where `sparse[z]=k*s2+l` and `z` is between `dense[i*d2+j]` and `dense[i*d2+j+1]-1`.
The index `z` is found in `sparse` using binary search. If it doesn't exist, it's zero (0, 0.0, false, or null).<br/>
A boolean sparse tensor does not have a `values` array.<br/>
A block tensor, tensor*(d<sub>1</sub>,...,d<sub>n</sub>)(s<sub>1</sub>,...,s<sub>m</sub>) e, is stored as a distributed collection of blocks of type
RDD[(coord,block)], where coord is the block coordinates (of type (Int,...,Int)) and block is a fixed-size tensor constructed
using tensor(N,...,N)(N,...,N). A block has fixed size `block_size` (default is 100M int/float), which means that each dimension N has N<sup>n+m</sup>=`block_size` .

## Matrix multiplication using array comprehensions:

```scala
q("""
     var A = tensor*(n,n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ]     // dense block matrix
     var B = tensor*(n)(n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ]    // dense rows, sparse columns
     tensor*(n,n)[ ((i,j),+/v) | ((i,k),a) <- A, ((kk,j),b) <- B, kk == k, let v = a*b, group by (i,j) ];
 """)
```

## Matrix addition using array comprehensions:
  
Full scans of sparse arrays in which both zero and non-zero elements are used are done with a full scan <= (slower)

```scala
q("""
     var A = tensor*(n)(n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ]     // sparse matrix
     var B = tensor*(n)(n)[ ((i,j),random()) | i <- 0..n-1, j <- 0..n-1 ]     // sparse matrix
     tensor*(n,n)[ ((i,j),a+b) | ((i,j),a) <= A, ((ii,jj),b) <= B, ii == i, jj == j ];
 """)
```

## Matrix multiplication using loops:

```scala
    q("""
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

## Matrix factorization:

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
## Pagerank

The input graph G is an RDD[(Long,Long)]

```scala
      var N = 1100;  // # of graph nodes
      var b = 0.85;

      // count outgoing neighbors
      var C = tensor*(N)[ (i,j.length) | (i,j) <- G, group by i ];

      // graph matrix is sparse
      var E = tensor*(N)(N)[ ((i,j),1.0/c) | (i,j) <- G, (ii,c) <- C, ii == i ];

      // pagerank
      var P = tensor*(N)[ (i,1.0/N) | i <- 0..N-1 ];

      var k = 0;
      while (k < 10) {
        k += 1;
        var Q = P;
        for i = 0, N-1 do
            P[i] = (1-b)/N;
        for i = 0, N-1 do
            for j = 0, N-1 do
                P[i] += b*E[j,i]*Q[j];
      };
```