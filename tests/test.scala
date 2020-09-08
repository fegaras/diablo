import edu.uta.diablo._

object Test {
  def main ( args: Array[String] ) {

    q("""
       { var k: Int = 1;
         var A: vector[Int];
         var B: vector[Int];
         //[ v+1 | v <- A ];
         for i = 1,10 do
            A[i] = B[i]+1;
         println(A);
       }
    """)

  }
}
