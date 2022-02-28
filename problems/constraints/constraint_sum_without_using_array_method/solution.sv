// QUESTION: Write constraint such that sum of arr[10] is 100 without using .sum method
class myclass #(int unsigned SIZE=10);
  rand bit [7:0] a[SIZE];
  
  function void post_randomize();
    // gives the max value the next element can take
    // since the target is 100, the initial limit is 100
    int limit = 100; 
    foreach( a[i]) begin 
      // if it is the last element, it should get exactly the 'limit'
      // in order to make the sum 100
      if(i == SIZE -1) 
        a[i] = limit;
      else begin 
        // for all other elements, randomize a value within zero and limit
        std::randomize(a[i]) with { a[i] inside {[0:limit]};};
        // after finding a random value for each element, reduce the limit by that value
        limit = limit - a[i];
      end
    end
  endfunction
endclass

module test();

  myclass h;
    
  initial begin 
    h = new();
    assert(h.randomize());
    $display("The array is %p",h.a);
    $display("The array sum is %d",h.a.sum() with ( int'(item)) );
    $finish();
  end 
  
  initial begin
  	$dumpfile("dump.vcd");
  	$dumpvars(1);
  end
endmodule