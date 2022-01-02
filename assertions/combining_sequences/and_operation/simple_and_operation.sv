// Code your testbench here
// or browse Examples
module test();

  bit clk,a,b,c,done;
  
  always #5 clk = ~clk; 
 
  //potential match point: t + 3rd clock tick
  sequence s1;
    a ##1 b[*3] ;
  endsequence

  //potential match point: t + 4th clock tick
  sequence s2;
    a ##2 c[*3];
  endsequence

  //match point: max(t + 3rd, t+ 4th) clock tick
  sequence s1_and_s2;
    @(posedge clk) s1 and s2; 
  endsequence

  property a_implies_s1_and_s2;
    // add 'a' an antecedent to have better control over failure
    // the consequent sequence starts evaluation at the same tick at which 'a' goes high
    @(posedge clk) a |-> (s1 and s2); 
  endproperty 
  a1:assert property (a_implies_s1_and_s2);
    
  property match_point_should_be_4th_tick;
    //confirm that the match point is t + 4th tick
    @(posedge clk) a |-> ##4 s1_and_s2.ended;
  endproperty 
  a2:assert property (match_point_should_be_4th_tick);

  initial begin 
    $display("STARTING SIMULATION");
    pass_stimulus();    
    fail_stimulus();
    $display("ENDING SIMULATION");
    $finish();
  end  
  task pass_stimulus();
    $display("Starting pass stimulus");
    repeat (1) @(negedge clk);
    //set a to one
    a = 1;
    b = 0;
    c =0 ;
    done = 0;
    repeat (1) @(negedge clk);
    a =0 ; // just test for one occurence of 'a'
    b =1 ; // start 'b' transition
    c =0 ;
    repeat (1) @(negedge clk);
    c =1 ; // start 'c' transition in the next tick
    repeat (2) @(negedge clk);
    // no changes in this tick and sequence is going to match in the next tick
    // therefore, pretend that some 'done' gets asserted at match tick
    done = 1 ;
    repeat (1) @(negedge clk);
    b =0 ; // 'b' has been true for 4 ticks, so toggle it
    c =0 ; // 'c' has been true for 3 ticks, so toggle it
    done = 0 ; // disable 'done'
    repeat (10) @(negedge clk);
  endtask 
  task fail_stimulus();
    $display("starting fail stimulus");
    repeat (1) @(negedge clk); // any number of ticks with 'a' == 0 is okay
    a = 1;
    b = 0;
    c =0 ;
    done = 0;
    repeat (1) @(negedge clk);
    a =0 ; // just test for one occurence of 'a'
    b =1 ; // start 'b' transition
    c =0 ;
    repeat (1) @(negedge clk);
    c =1 ; // start 'c' transition in the next tick
    repeat (2) @(negedge clk);
    c = 0; // set 'c' as false in order to make the assertion fail
    repeat (1) @(negedge clk);
    b =0 ; // 'b' has been true for 4 ticks, so toggle it
    repeat (10) @(negedge clk); // add some ticks before ending the stimulus
  endtask
  //dump waves
  initial begin
  	$dumpfile("dump.vcd");
  	$dumpvars(1);
  end
endmodule
