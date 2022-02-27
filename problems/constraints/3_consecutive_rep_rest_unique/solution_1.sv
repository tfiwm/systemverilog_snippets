// QUESTION: Write constraint for an integer array with 10 elements such that exactly 3 of them are same and rest are unique
class myclass #(int unsigned SIZE=10);
  rand bit [7:0] a[SIZE];
  rand bit [7:0] b;
  
  constraint k {
    // b is the value to be repeated 3 times. 
    // so it should be inside {a}
    b inside {a}; 
    
    foreach(a[i])   
      // sum of int'(item == a[i]) implies the number of occurrences of a[i]
      // that sum should be 3 for all a[i] that equals b - i.e. three occurrences b
      // otherwise, the sum should be 1 - i.e. other possible values can occur 1 time
      a.sum() with (int'(item == a[i])) == ((a[i] == b) ? 3: 1); 
  }
  
  function void post_randomize();
    // the constraint doesn't enforce consecutive repetition, therefore, perform a sort 
    a.sort(); 
  endfunction 
endclass

module test();

  myclass h;
    
  initial begin 
    h = new();
    assert(h.randomize());
    $display("The array is %p",h.a);
    $finish();
  end 
  
  initial begin
  	$dumpfile("dump.vcd");
  	$dumpvars(1);
  end
endmodule