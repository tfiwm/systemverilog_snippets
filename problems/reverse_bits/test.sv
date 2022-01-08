module test();
    parameter DW =4;
    logic [DW-1:0] din,dout;
    always_comb begin 
        for(int i=0; i < DW; i++) begin 
            dout[i] = din[DW-1-i];
        end
    end
    initial $monitor("din %b, dout %b",din,dout);

    initial begin 
        din = 4'hd;
        #10 din = 4'h4;
    end
endmodule
