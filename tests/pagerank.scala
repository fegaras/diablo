import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import Math._

object Test {
  def main ( args: Array[String] ) {
    val conf = new SparkConf().setAppName("Test")
    spark_context = new SparkContext(conf)

    parami(number_of_partitions,10)
    parami(block_dim_size,100)

    val G = spark_context.textFile("graph.txt")
              .map( line => { val a = line.split(",").toList
                              (a(0).toInt,a(1).toInt) } ).cache

    var X = q("""
      var N = 1100;  // # of graph nodes
      var b = 0.85;

      // count outgoing neighbors
      var C = rdd[ (i,j.length) | (i,j) <- G, group by i ];
      //var C = tensor*(N)[ (i,j.length) | (i,j) <- G, group by i ];

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

      // convert pageranks to a plain RDD
      rdd[ (i,v) | (i,v) <- P ];

     """)

     // print top-30 pageranks
     X.sortBy(x => x._2,false,1).take(30).foreach(println)

  }
}
