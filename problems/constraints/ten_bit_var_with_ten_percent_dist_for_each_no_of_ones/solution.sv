// Write a constraint for a 10 bit variable en so that; 
// -> 10% of the time 1 bit in en is high 
// -> 10% of the time 2 bits in en are high 
// etc. all the way up to 10% of the time all 10 bits in en are high.
class myclass #(parameter WIDTH=10);
  rand bit [WIDTH-1:0] en;
  typedef enum { ONE=1,TWO,THREE,FOUR,FIVE,SIX,SEVEN,EIGHT,NINE,TEN} outcomes_t;
  // counter for each possible number of 1s
  longint outcome_counter[outcomes_t]= '{ONE:0,TWO:0,THREE:0,FOUR:0,FIVE:0,SIX:0,SEVEN:0,EIGHT:0,NINE:0,TEN:0};
  // tracks total randomize() calls
  longint counter;
  
  constraint k {
    // distribute number of ones equally over a total weight of 10 => 10% chance for each case
    $countones(en) dist { [1:WIDTH]:=10};
  }
    
  // verify that the randomization is correct
  // track the count of each case
  function void post_randomize();
    counter++; // total number of randomize() calls
    outcome_counter[outcomes_t'($countones(en))]++; // occurrence of a specific number of 1s
  endfunction 
    
  // calculate the percentage of occurence of each case
  function void show();
    $display("Number of randomize() calls: %0d",counter);
    $display("outcome_counter: %p",outcome_counter);
    foreach(outcome_counter[i]) begin 
      $display("%s: %0.2f %%",i.name,(real'(outcome_counter[i])/counter)*100);
    end
  endfunction 
  
    
endclass

module tb;
  initial begin
    myclass c = new;
    repeat(10000) begin 
      assert(c.randomize());
    end
    c.show(); // calculate the % distribution of each case
  end
endmodule