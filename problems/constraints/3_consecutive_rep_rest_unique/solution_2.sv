// QUESTION: Write constraint for an integer array with 10 elements such that exactly 3 of them are same and rest are unique
class myclass #(int unsigned SIZE=8);
  rand bit [2:0] a[SIZE];
  rand bit [2:0] b;
  
  constraint k {
    // b is the value to be repeated 3 times. 
    // so it should be inside {a}
    b inside {a}; 
    // constraint so that the first occurrence of b is not at the last two positions
    foreach(a[i])
      (a[i] == b ) -> (i <= SIZE - 3);
    // all the elements should be unique
    unique {a};
  }

  // as per the constraints all the elements are unique and
  // there is one occurrence of b
  // use post_randomize() to change the next two (or n) elements to 'b' as well
  function void post_randomize();
    //find the first index of b
    int index[$] = a.find_first_index() with (item == b); 
    // update the next to indices to the value of b
    a[index[0] +1] = b;
    a[index[0] +2] = b;
  endfunction
endclass

module test();

  myclass h;
    
  initial begin 
    h = new();
    assert(h.randomize());
    $display("The array is %p",h.a);
    $display("The b is %p",h.b);
    $finish();
  end 
  
  initial begin
  	$dumpfile("dump.vcd");
  	$dumpvars(1);
  end
endmodule