module test();
   typedef struct packed {
       bit [7:0] one;
       bit [7:0] two;
   } mytype;

   mytype v;
   wire w;

    /*simultaneous continous assignment and procedural assignment 
    to a variable is possible, provided the assignments targets 
    an independent element of that variable */
   assign v.two = byte'(8); 

   initial begin 
       //multiple procedural assignment to a variable is okay
       //last assignment wins
       v.one = byte'(16);
       v.one = byte'(16);
       //this should be an error since there is already a continuous assignment on this element
       //v.two = byte'(16); 
       
       //this should be an error because it is a procedural assignment on a net
       //w = 1'b1;
   end
endmodule