module test();

    initial begin 
        $dumpfile("dump.vcd");
        $dumpvars(1);
    end
endmodule
