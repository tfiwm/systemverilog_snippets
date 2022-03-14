// Write a constraint for a 2d array such that it has a unique max value in each row and that max value should not be equal to any other max value in other rows

class myclass #(parameter ROWS=3,parameter COLS=3, parameter WIDTH=4);
  // 2D array to be randomized
  rand bit [WIDTH-1:0] a[][];  
  // helper array to generate unique max values
  // max_values[0] has to be the max value of the first row a[0]
  rand bit [WIDTH-1:0] max_values[ROWS]; 
  
  // set proper dim sizes
  constraint for_size {
    a.size() == ROWS;
    foreach(a[i]) 
      a[i].size() == COLS;
  }
  
  // make sure that max values are unique among themselves
  constraint for_unique {
    unique {max_values};
  }
  
  // for each row of a, there has to be one occurrence of max value
  constraint for_one_max {
    foreach(a[i]) {
      a[i].sum() with (int'(item == max_values[i])) == 1;
    }
  }
  
  // for each row of a, all other elements should be less than the max_value for that row
  constraint for_unique_max {
    foreach (a[i,j]) {
      a[i][j] <= max_values[i];
    }
  }
  
  // verify that the randomization is correct
  function void post_randomize();
    bit [WIDTH-1:0] max_array[ROWS];
    bit [WIDTH-1:0] unique_max_array[$];
    bit [WIDTH-1:0] arow[COLS];
    bit [WIDTH-1:0] hits[$];
    bit [WIDTH-1:0] amax[$];
    
    foreach(a[i]) begin 
      // find the row max
      arow = a[i];
      amax = arow.max();
      // store max of each row to an array
      // max_arrayy[0] is the max value in zeroth row
      max_array[i] = amax[0];
      
      // count the number of items having a value of max_array[i] in each row
      hits = a[i].find() with (int'(item == max_array[i]));
      // there should only be one max value
      assert( hits.size() == 1) else
        $error("The max value is not unique within its row. hits.size() is %0d",hits.size());
    end
    
    // ensure that the max value is unique among rows
    unique_max_array = max_array.unique();
    assert(unique_max_array.size() == $size(max_array)) else
      $error("The max value is not unique among rows");
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