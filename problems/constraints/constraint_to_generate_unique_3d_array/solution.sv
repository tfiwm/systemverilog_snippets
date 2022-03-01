// QUESTION: write a constraint to generate a unique 3x3x3 array without using 'unique'

module test();
  
  parameter int WIDTH = 16;
  parameter int SIZE = 4;
  
  class myclass ;
    
    rand bit [WIDTH-1:0] a[][][];

    // constraint all sizes
    constraint k { 
      a.size() == SIZE; 
    }
    constraint j { 
      foreach(a[i,j]) {
        a[i].size() == SIZE; 
        a[i][j].size() == SIZE; 
      }
    }

  // constraint every element is different from every other, except with itself
  constraint m {
    foreach(a[i,j,k]) 
      foreach(a[i1,j1,k1])  {
        if( k != k1) a[i][j][k] != a[i1][j1][k1]  ;
        if( j != j1) a[i][j][k] != a[i1][j1][k1]  ;
        if( i != i1) a[i][j][k] != a[i1][j1][k1]  ;
      }
  }

  endclass


  myclass h;
  bit [WIDTH-1:0] oned[$];// for verification
        
  initial begin 
    h = new();
    assert(h.randomize());
    $display("The array is %p",h.a);
    $display("The array size is %p", h.a.sum(array) with (array.sum(i) with ($size(i))));
    
    // ensure that the array is unique
    foreach(h.a[i,j,k]) begin 
      oned.push_back(h.a[i][j][k]);
    end
    assert(oned.unique().size() == oned.size()) else
      $error(" The array is not unique");
    
    $finish();
  end 
  
  initial begin
  	$dumpfile("dump.vcd");
  	$dumpvars(1);
  end
endmodule