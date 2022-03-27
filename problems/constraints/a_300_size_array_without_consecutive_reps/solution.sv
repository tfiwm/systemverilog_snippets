// Write a constraint to generate dynamic array of 300 elements. 
// Each element can have value 0/1/2/3/4. 
// Each of the above values should be present more than 40 times in the array. 
// Element 0 can be repeated while 1/2/3/4 are not allowed to repeat consecutively 
// ex: 001342.. allowed(0 can be repeated) ex: 0122431.. not allowed(2 is repeated)

class myclass #(parameter WIDTH=32, parameter SIZE=300, parameter REPS=40,parameter INDEX_OF_REP_RANGE=0); 
  
  rand bit [WIDTH-1] a[];
  // 'values' contain set of possible values
  // The values until INDEX_OF_REP_RANGE index 
  // can get repeated consecutively
  bit [WIDTH-1:0] values[5] = '{0,1,2,3,4};
  
  constraint limit_size {
      a.size() == SIZE;
  } 
  
  constraint limit_values{
    foreach(a[i])
      a[i] inside {values};
  }
  
  // values should repeat more than REPS times
  constraint value_count{
    foreach(values[i])
      a.sum() with ( int'(item == values[i])) > REPS;
  }
  
  constraint prevent_reps{
    foreach(a[i]) 
      if(i < SIZE - 1) 
        // if two adjacent members are same,
        // they should be from the range that 
        // allows consecutive repetition
        (a[i] == a[i+1]) -> (a[i] inside {values[0:INDEX_OF_REP_RANGE]});
  }
    
  function void post_randomize();
    // verify that the randomization is happening as expected
    verify();
  endfunction 
  
  function void verify();
    // count of each value should be > REPS
    foreach(values[i]) begin
      int count = a.sum() with ( int'(item == values[i]));
      assert(count > REPS) else
        $error("The count of %0d should be above %0d, but it turned out to be %0d",values[i],REPS,count);
    end
    
    // all members of a should take a value from values
    foreach(a[i]) begin
      assert( a[i] inside {values}) else
        $error("%0d at index %0d is not inside %p",a[i],i,values);
    end
    
    // size should be SIZE
    assert(a.size() == SIZE) else
      $error("The size is not %0d",SIZE);
    
    // values from index INDEX_OF_REP_RANGE+1 until the end should not repeat consecutively
    foreach(a[i]) begin 
      if(i < SIZE-1)
        if( a[i] == a[i+1])
          assert( a[i] inside {values[0:INDEX_OF_REP_RANGE]}) else
            $error("%0d is repeating consecutively",a[i]);
    end
  endfunction 
  
  function void show();
    $display("The array is: %p",a);
  endfunction
    
endclass

module tb;
  initial begin
    automatic myclass c = new;
    repeat(10) begin 
      assert(c.randomize());
      c.show();
    end
  end
endmodule