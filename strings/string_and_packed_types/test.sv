module test();
    initial begin 
        string s="hello";
        bit [4:0] [7:0] vec = "hello";

        $display("Printing vec using foreach, one index at a time using string format specifier");
        foreach(vec[j]) begin  //foreach index ordering is based on how indices are specified in the declaration
            $display("%s at index %0d",vec[j],j);
        end

        $display("Printing string 's' using foreach, one index at a time using string format specifier");
        //foreach index ordering is based on how indices are specified in the declaration
        //left most packed dimension is the outer/slow-changing index
        foreach(s[j]) begin  
            $display("%s at index %0d",s[j],j); //one 8 bit chunk
        end
    end
endmodule
