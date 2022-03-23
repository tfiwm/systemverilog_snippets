// Implement randc functionality using rand.

class myclass #(parameter WIDTH=10);
  typedef enum { RED, GREEN, BLUE, YELLOW } colors_t;
  rand colors_t mycolor;
  // helper array to keep track of previous occurrences 
  bit is_present[colors_t] = '{RED:0, GREEN:0, BLUE:0, YELLOW:0};
  // variable similar to is_present, 
  // but used to independently verify that randomization is cyclic
  bit tracker[colors_t] = '{RED:0, GREEN:0, BLUE:0, YELLOW:0};
  
  constraint k {
    is_present[mycolor] != 1;
  }
    
  function void post_randomize();
    // save the occurrence of a specific color to an associative array
    is_present[mycolor] = 1;
    // if a cycle has completed, reset is_present
    // a cycle is complete when there is no other color
    // that hasn't occurred in that cycle
    if (is_present.sum() with (int'(item == 0)) == 0) 
      is_present = '{RED:0, GREEN:0, BLUE:0, YELLOW:0};
    // verify that the randomization is happening as expected
    verify();
  endfunction 
  
  function void verify();
    // if a color already exists in the tracker
    // the randomization cycle should be complete
    if(tracker[mycolor] == 1)  begin 
      // a cycle is complete when there is no other color
      // that hasn't occurred in that cycle
      assert( tracker.sum() with (int'(item == 0)) == 0) 
        // when a cycle is complete, reset the tracker to start the next cycle
        tracker = '{RED:0, GREEN:0, BLUE:0, YELLOW:0};
      else begin 
        $display("Colors in this cycle: %p, selected color: %p",tracker,mycolor.name);
        $fatal("Randomization is not cyclic");
      end
    end
    // insert the current color to the tracker
    tracker[mycolor] = 1;
  endfunction 
  
  function void show();
    $display("The color is: %s",mycolor.name()); 
  endfunction
    
endclass

module tb;
  initial begin
    myclass c = new;
    repeat(100) begin 
      assert(c.randomize());
      c.show();
    end
  end
endmodule