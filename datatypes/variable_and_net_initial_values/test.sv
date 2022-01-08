module test();
   typedef struct packed {
       bit [7:0] one;
       bit [7:0] two;
   } mytype;

   var logic v; // variables have default initial value of its data type
   wire logic w; // nets have default initial value of 'z

   initial begin 
       #1 $display("default value of variable 'v' is: %p",v);
       #1 $display("default value of net 'w' is: %p",w);
   end
endmodule
