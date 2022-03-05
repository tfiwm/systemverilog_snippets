// generate a sequence of opcodes (ADD,SUB,MUL,NOP) so that the next occurrence 
// of a given opcode is 'x' opcodes after the current occurrence, where 'x' is the number of cycles
// required to execute the current opcode

typedef enum { ADD, SUB, MUL, NOP} ins_t; // list of opcode 
  
class myclass ;
  
  parameter SIZE=20; // size of the sequence
  rand ins_t opcode[]; // dynamic array for opcode sequence
  bit [15:0] delays[ins_t]; //holds delay value for each opcode type
 
  function new();
   //set the delay values
    delays[ADD] = 2;
    delays[SUB] = 3;
    delays[MUL] = 4;
    delays[NOP] = 1;
  endfunction
  
  constraint k {
    opcode.size() == SIZE;
    
    foreach(opcode[i]) 
      foreach(opcode[j])
        // given an opcode, ensure that the opcodes within 
        // its duration of execution are different opcodes
        if(j>i && j<(i+delays[opcode[i]]))
          opcode[i] != opcode[j];
  }
  
  // for testing: verify that the array got randomized properly
  function void post_randomize();
    for(int i = 0 ; i < opcode.size() ; i++) begin 
      for(int j = i+1 ; j < ( i + delays[opcode[i]]) ; j++) begin 
        assert( opcode[i] != opcode[j]); 
      end 
    end 
  endfunction
endclass
  
module test();
    myclass h;

    initial begin 
      h = new();
      
      assert(h.randomize());
      $display("h.opcode is %p",h.opcode);
      
      $finish();
    end 
endmodule