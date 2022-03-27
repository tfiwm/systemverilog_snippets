// Write constraints – to pick a ball out of 10 different colored balls and that color should not be repeated for in next 3 draws

// color should not repeat in the last N draws
class myclass #(parameter N=3); 
  
  typedef enum { RED, GREEN, BLUE, YELLOW, PINK, WHITE, BLACK, BROWN, PURPLE, CYAN } color_t;
  rand color_t ball; // the ball
  color_t last_n_balls[$:N]; // keeps track of last N outcomes
  
  // for verification 
  color_t counter[$:N];
  
  constraint b {
    // ball shouldn't be in the list that tracks 
    // last N draws
    foreach(last_n_balls[i]){
      last_n_balls[i] != ball;
    }
  } 
    
  function void post_randomize();
    // if the queue is full, remove the oldest draw result
    if(last_n_balls.size() >= N)
      last_n_balls.pop_front();
    // save the current draw to the end
    last_n_balls.push_back(ball);
    // verify that the randomization is happening as expected
    verify();
  endfunction 
  
  function void verify();
    bit fail;
    // counter independently keeps track of last N outcomes
    // the current ball shouldn't be in counter list
    foreach(counter[i]) begin
      if(ball == counter[i]) begin
        fail = 1;
        break;
      end
    end
    assert(!fail) else
      $error("%s has repeated in the last %0d draws- %p",ball.name,N,counter);
    
    // save the current draw for next check
    if(counter.size() >= N) 
      counter.pop_front();
    counter.push_back(ball);
  endfunction 
  
  function void show();
    $display("The ball is %s",ball.name);
  endfunction
    
endclass

module tb;
  initial begin
    automatic myclass c = new;
    repeat(100) begin 
      assert(c.randomize());
      c.show();
    end
    
  end
endmodule