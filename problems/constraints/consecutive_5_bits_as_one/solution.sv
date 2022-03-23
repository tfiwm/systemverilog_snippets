// 	Constraint to randomize a 100 bit var such that always and only 5 consecutive bits are 1s

class myclass;
  
  rand bit [99:0] a;
  // helper variable 
  rand bit [31:0] shift;
  
  constraint b {
    // the mask can be shifted 100-5 times
    shift inside {[0:95]};
    a == (5'b11111<<shift); 
  } 
    
  function void post_randomize();
    // verify that the randomization is happening as expected
    verify();
  endfunction 
  
  function void verify();
    int indices[$];
    foreach(a[i]) begin 
      // save the index position of ones
      if(a[i] == 1) indices.push_front(i); 
    end
    // there should be 5 ones
    assert(indices.size() == 5);
    // the indices should be consecutive
    foreach(indices[i]) begin 
      if(i>0) 
        assert(indices[i] == indices[i-1]+1);
    end
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