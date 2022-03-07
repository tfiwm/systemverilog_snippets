/*
Credits: Koga 
N-Queens problem
    1. No queens in the same row
    2. No queens in the same col
    3. No queens in the same pos diagonal
    4. No queens in the same neg diagonal
*/
class n_queens #(N=8);
    //Variables
	//queen[1] denotes the position(column) of queen in row 1
    rand bit[$clog2(N)-1:0] queen [N];   
    
    //Constraints
    constraint no_queen_in_same_col_c { 
		// make sure that a row has only one queen
        unique {queen};
    }
    
	// Elements sharing same negative diagonal have same r-c values
	// negative diagonals are all the diagonals (not just the main/longest diagonals) with negative slope
    constraint no_queen_in_same_neg_diag_c {  
        foreach(queen[i]) {
            foreach(queen[j]) {
                if(i != j)
					// elements along all the negative diagonals must be different
                    (i - queen[i]) != (j - queen[j]);
            }
        }
    }
    // Elements sharing same positive diagonal have same r+c values
	// positive diagonals are all the diagonals with positive slope	
    constraint no_queen_in_same_pos_diag_c {  
        foreach(queen[i]) {
            foreach(queen[j]) {
                if(i != j)
                    (i + queen[i]) != (j + queen[j]);
            }
        }
    }
    
    function void display_board();
        string str;
        for (int r=0; r<N; r++) begin
        str = "";
            for (int c=0; c<N; c++) begin
                if (c==queen[r])
                    str = {str,"Q","|"};
                else
                    str = {str,"-","|"};
            end
        $display("%s",str);
        end
    endfunction
          
endclass

module tb;
    n_queens n1;
    initial begin
        n1 = new();
      repeat(50) begin
            if(n1.randomize()) begin
                $display("Solved board...");
                n1.display_board();
            end
            else
                $fatal("Rand failure");
        end
    end
endmodule