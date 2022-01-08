//models a simple DFF
primitive myprim (q,clk,d);
    output reg q;
    input clk;
    input d;
    table
        //CLK   D   Q   Q+
        r       1  : ? :   1 ;
        r       0  : ? :   0 ;
        f       ?  : ? :   - ;
    endtable
endprimitive
//models a non-reset-able DFF in RTL
module dff(input clk,d,output logic q);
    always_ff @(posedge clk) begin 
        q <= d;
    end
endmodule

module test();

    logic d,dq,pq;
    bit clk;

    dff d1(.q(dq),.*);
    myprim p1(pq,clk,d);

    always clk = #5 ~clk;
    
    always @(posedge clk) begin 
        //check if the primitive and RTl DFF output matches 1 unit after clock edge
        #1 assert(dq === pq) else begin 
            $error("@%0t, d = %0b , dq = %0b , pq = %0b", $realtime, d, dq, pq);
        end
    end

    always @(posedge clk) begin 
        //just to see what is happening at each posedge clock
       #0 $strobe("@%0t, d = %0b , dq = %0b , pq = %0b", $realtime, d, dq, pq);
    end
    initial begin 
        //some random stimulus
        for(int i =0; i < 100; i++) begin 
            repeat (1) @(negedge clk);
            d = $urandom();
        end
        $finish();
    end
endmodule