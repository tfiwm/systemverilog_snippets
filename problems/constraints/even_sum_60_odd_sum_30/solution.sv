// Write SV constraint to limit sum of odd elements of an array to be 30 
// and sum of even elements to be 60
class myclass #(parameter SIZE=16,parameter WIDTH=16); 
  
  rand bit [WIDTH-1:0] a[SIZE];
  
  constraint c1 {
    // sum of elements at even index position == 60
    a.sum() with ( item.index % 2 == 0 ? int'(item) : int'(0)) == 60 ;
    // sum of elements at odd index position == 30
    a.sum() with ( item.index % 2 != 0 ? int'(item) : int'(0)) == 30 ;
  } 
    
  function void post_randomize();
    // verify that the randomization is happening as expected
    verify();
  endfunction 
  
  function void verify();
    int osum,esum;
    foreach(a[i]) begin
      if(i%2 == 0)
        esum+=a[i];
      else 
        osum+=a[i];
    end
    assert(esum == 60) else
      $error("The even sum is expected to be 60 but is actually %0d",esum);
    assert(osum == 30) else
      $error("The odd sum is expected to be 30 but is actually %0d",osum);
  endfunction 
  
  function void show();
    $display("The array is: %p",a);
  endfunction
    
endclass

module tb;
  initial begin
    automatic myclass c = new;
    repeat(100) begin 
      assert(c.randomize());
      c.show();
    end
  end
endmodule