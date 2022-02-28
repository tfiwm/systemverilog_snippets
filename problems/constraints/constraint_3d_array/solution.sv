// QUESTION: write a constraint to set all the dimensions of a 3D array
class myclass #(int unsigned SIZE=10);
  rand bit [7:0] a[][][];
  
  constraint k { 
    a.size() == 4; 
  }
  
  constraint j { 
    foreach(a[i,j]) {
      a[i].size() == 3; 
      a[i][j].size() == 2; 
    }
  }
    
endclass

module test();

  myclass h;
    
  initial begin 
    h = new();
    assert(h.randomize());
    $display("The array is %p",h.a);
    $display("The array size is %d",h.a.size());
    $finish();
  end 
  
  initial begin
  	$dumpfile("dump.vcd");
  	$dumpvars(1);
  end
endmodule