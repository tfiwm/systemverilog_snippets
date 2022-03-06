// Randomize an array such that all elements are unique, without using unique construct
class myclass #(parameter SIZE=10);
  rand bit [3:0] a[SIZE];  
  
  constraint k {
    // generate elements in ascending order thereby ensuring that elements are unique
    foreach(a[i]) {
     if(i != SIZE-1) a[i+1] > a[i]; 
    }
  }
  
  function void post_randomize();
    //optional, shuffle to get rid of the ascending order
    a.shuffle();
    // for testing: verify that the generated array is unqiue
    assert(a.unique().size() == $size(a)) else
      $error("Generated array is not unique");
  endfunction 
    
  function void show();
    $display("%p",a);
  endfunction 
    
endclass

module tb;
  initial begin
    myclass c = new;
    repeat(15) begin 
      assert(c.randomize());
      c.show();
    end
  end
endmodule