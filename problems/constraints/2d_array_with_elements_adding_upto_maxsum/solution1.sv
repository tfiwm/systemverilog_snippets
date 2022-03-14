// Write constraints to generate MxN matrix with each element having a value of 0,1 and sum of all elements less the MAX_SUM

class myclass #(parameter ROWS=4,parameter COLS=4, parameter WIDTH=0,parameter MAXSUM=10);
  // 2D array to be randomized
  rand bit [WIDTH-1:0] a[][];  
  
  constraint non_zero_sizes {
    a.size() == ROWS;
    foreach(a[i]) 
      a[i].size() == COLS;
  }
  
  // elements should be either 1 or 0
  constraint one_or_zero {
    foreach(a[i,j]) 
      a[i][j] inside {1,0};
  }
  
  // total sum of the matrix should be == MAXSUM
  constraint sum_less_than_maxsum {
    // reduce array by performing summation of each row
    // for each row, explicitly return sum of that row
    a.sum(arow) with (arow.sum() with ( int'(item))) < MAXSUM;
  }
    
  // verify that the randomization is correct
  function void post_randomize();
    int sum;
    foreach(a[i,j]) begin 
      sum += int'(a[i][j]);
    end
    assert(sum < MAXSUM) else 
      $error("The array sum (%0d) is NOT equal to MAXSUM (%0d)",sum,MAXSUM);
  endfunction 
    
  function void show();
    $display("The array is:");
    foreach(a[i,j]) begin 
      $write("%0d\t",a[i][j]);
      if(j == COLS-1) $display("");
    end
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