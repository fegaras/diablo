import edu.uta.diablo._
import org.apache.spark._
import org.apache.spark.rdd._
import Math._

object Test {
  def main ( args: Array[String] ) {
    val conf = new SparkConf().setAppName("Test")
    spark_context = new SparkContext(conf)

    parami(blockSize,100)

    val G = spark_context.textFile("graph.txt")
              .map( line => { val a = line.split(",").toList
                              (a(0).toInt,a(1).toInt) } ).cache

    val P = q("""
      var N = 1100;  // # of graph nodes
      var b = 0.85;

      // pagerank
      var P = tensor*(N)[ (i,1.0/N) | i <- 0..N-1 ];

      // graph matrix is sparse
      var E = tensor*(N)(N)[ ((i,j),true) | (i,j) <- G ];

      // count outgoing neighbors
      var C = tensor*(N)[ (i,0) | i <- 0..N-1 ];
      for i = 0, N-1 do
          for j = 0, N-1 do
             if (E[i,j])
                C[i] += 1;

      var k = 0;
      while (k < 4) {
        k += 1;
        var Q = P;
        for i = 0, N-1 do
            P[i] = (1-b)/N;
        for i = 0, N-1 do
            for j = 0, N-1 do
                if (E[j,i])
                   P[i] += b*Q[j]/C[j];
      };

      // convert pagerank to a plain RDD
      rdd[ (i,v) | (i,v) <- P ];

     """)

     // top-30
     P.sortBy(_._2,false,1).take(30).foreach(println);

  }
}
