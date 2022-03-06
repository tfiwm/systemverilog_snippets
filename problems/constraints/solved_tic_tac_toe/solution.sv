// a solved tic-tac-toe game


typedef enum { CROSS,ZERO,EMPTY } cell_t;

class check;
  rand cell_t a[3][3];
  cell_t winner = CROSS; // which one should win?
  cell_t loser = ZERO; // which one should lose?
   
  constraint number_of_moves{
    // min number of moves to win is 3
    a.sum() with (item.sum(acell) with (int'(acell == winner))) >= 3;
    // for a min number of moves by the winner, the loser should have (min - 1) number of moves
    a.sum() with (item.sum(acell) with (int'(acell == loser))) == a.sum() with (item.sum(acell) with (int'(acell == winner))) - 1;
  }
  
  constraint for_winner {
    // at least one row should have number of winner symbols as 3
    (a[0].sum(acell) with ( int'( acell == winner)) == 3) | (a[1].sum(acell) with (int'( acell == winner)) == 3) | (a[2].sum(acell) with ( int'( acell == winner)) == 3 ) | 
    // or at least one column should have number of winner symbols as 3
    (a.sum(col) with (int'(a[col.index][0] == winner)) == 3) | (a.sum(col) with (int'(a[col.index][1] == winner)) == 3) | (a.sum(col) with (int'(a[col.index][2] == winner)) == 3) | 
    // or at leaset one of the diagonals should have number of winner symbols as 3
    (a.sum(acell) with (int'( a[acell.index][acell.index] == winner)) == 3) | (a.sum(acell) with (int'( a[acell.index][2 - acell.index] == winner)) == 3)  ;

  }
  
  // similar to for_winner, but ensures that the loser doesn't win
  constraint for_loser {
    (a[0].sum(acell) with ( int'( acell == loser )) != 3) & (a[1].sum(acell) with (int'( acell == loser )) != 3) & (a[2].sum(acell) with ( int'( acell == loser )) != 3 ) & 
    (a.sum(col) with (int'(a[col.index][0] == loser )) != 3) & (a.sum(col) with (int'(a[col.index][1] == loser )) != 3) & (a.sum(col) with (int'(a[col.index][2] == loser )) != 3) & 
    (a.sum(acell) with (int'( a[acell.index][acell.index] == loser )) != 3) & 
    (a.sum(acell) with (int'( a[acell.index][2 - acell.index] == loser )) != 3)  ;

  }
      
  function void show();
    foreach(a[i,]) begin 
      foreach(a[,j]) begin 
        if(a[i][j] == EMPTY) 
          $write("-\t");
        else if(a[i][j] == ZERO) 
          $write("O\t");
        else if(a[i][j] == CROSS) 
          $write("*\t");
      end
      $display("");
    end
  endfunction
  
endclass

module tb;
  initial begin
    check c = new;
    assert(c.randomize());
    c.show();
  end
endmodule