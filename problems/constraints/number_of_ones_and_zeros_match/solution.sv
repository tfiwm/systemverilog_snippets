// 	Write constraints to generate a n bit value such that the number of bits set is equal to number of bits that are zero
class myclass #(parameter WIDTH=32);
  
  rand bit [WIDTH-1:0] a;
  
  constraint b {
    // for equal halves, the WIDTH should be even
    WIDTH % 2 == 0;
    
    // ones should be equal to zeros
    $countones(a) == $countbits(a,0);
  } 
    
  function void post_randomize();
    // verify that the randomization is happening as expected
    verify();
  endfunction 
  
  function void verify();
    // array containing a counter for both ones and zeros
    longint count[2]; 
    
    foreach(a[i]) begin 
      // increment the correct counter
      count[a[i]]++; 
    end
    assert(count[0] == count[1]) else
      $error("Number of ones (%0d) is not equal to number of zeros (%0d)",count[1],count[0]);
  endfunction 
  
  function void show();
    $display("The number is:%b",a);
  endfunction
    
endclass

module tb;
  initial begin
    myclass c = new;
    repeat(10) begin 
      assert(c.randomize());
      c.show();
    end
  end
endmodule