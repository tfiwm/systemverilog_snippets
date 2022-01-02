// Code your testbench here
// or browse Examples
module test();

  bit clk,a,b,c;
  
  always #5 clk = ~clk; 
  
  
  property a2_myprop;
    @(posedge clk) a |=> b[=3] ##1 c ;
  endproperty 
  a2:assert property (a2_myprop);
    
  initial begin 
    $display("STARTING SIMULATION");
    $display("starting pass stimulus");
    a2_pass();    
    $display("starting fail stimulus");
    a2_fail();
    $display("ENDING SIMULATION");
    $finish();
  end 
  task a2_fail();
    repeat (1) @(negedge clk);
    //set a to one
    a = 1;
    b = 0;
    repeat (1) @(negedge clk);
    b =1 ;
    repeat (3) @(negedge clk);
    b =0 ;
    c =0 ;
    repeat (1) @(negedge clk);
    c =1 ;
    repeat (1) @(negedge clk);
  endtask 
  task a2_pass();
    repeat (1) @(negedge clk);
    //set a to one
    a = 1;
    b = 0;
    repeat (1) @(negedge clk);
    b =1 ;
    a =0 ;
    repeat (3) @(negedge clk);
    b =0 ;
    c =1 ;
    repeat (2) @(negedge clk);
  endtask 
  //dump waves
  initial begin
  	$dumpfile("dump.vcd");
  	$dumpvars(1);
  end
endmodule
