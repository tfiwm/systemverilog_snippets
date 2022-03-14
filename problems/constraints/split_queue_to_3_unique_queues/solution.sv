// Write a constraint to divide values of 1 queue into 3 queues so that all 3 queues have unique elements
class myclass #(parameter WIDTH=5);
  
  bit [WIDTH-1:0] mainq[$]='{1,1,1,2,2,2,3,3,3,4,5,6,7,8};
  rand bit [WIDTH-1:0] a[$],b[$],c[$];
  
  constraint sizes {
    // The size shouldn't be greater than the
    // number of unique elements in mainq.
    // Given mainq[$]='{1,1,1,2,2,2,3,3,3,4,5,6,7,8};
    // constraint can fail if a.size() == 12
    // coz there are no 12 unique elements
    a.size() <= unique_size(mainq);
    b.size() <= unique_size(mainq);
    c.size() <= unique_size(mainq);
    
    // avoid zero sized queues
    a.size() > 0;
    b.size() > 0;
    c.size() > 0;
    
    // the sub-queue sizes should add up to the size of mainq
    a.size() + b.size() + c.size() == mainq.size();
  }
  
  // the sub-queue elements should be unqiue
  constraint uniqify{
    unique {a};
    unique {b};
    unique {c};
  }
  
  // the sub-queue elements should be from the mainq
  constraint inside_mainq { 
    foreach(a[i])
      a[i] inside {mainq};
    foreach(b[i]) 
      b[i] inside {mainq};
    foreach(c[i]) 
      c[i] inside {mainq};
  }
  
  // for a given element in mainq, the total number of 
  // occurrences of it across all the sub-queues should be
  // equal to its number of occurrences in the mainq
  constraint proper_count { 
    foreach(mainq[i]) {
      a.sum() with ( int'(item == mainq[i])) + 
      b.sum() with ( int'(item == mainq[i])) + 
      c.sum() with ( int'(item == mainq[i])) 
      ==  mainq.sum() with ( int'(item == mainq[i])) ; 
    }
  }
      
  // Used in constraints 
  // Returns the number of unique elements
  function int unique_size(const ref bit [WIDTH-1:0] myq[$]);
    bit [WIDTH-1:0] uniqueq[$];
    uniqueq = myq.unique();
    return uniqueq.size();
  endfunction 
    
  // verify that the randomization is correct
  function void post_randomize();
    bit [31:0] count[bit [WIDTH-1:0]];
    bit [31:0] total_count[bit [WIDTH-1:0]];
    bit [WIDTH-1:0] uniqueq[$];
    
    // CHECK:1
    // verify that the count of each element in mainq
    // equals the sum of count of that element in 
    // each sub-queue - a, b, c
    
    // count elements in the main queue
    foreach(mainq[i]) begin 
      count[mainq[i]]++; 
    end
    
    // accumulate the count of elements in the each queue
    foreach(a[i]) begin 
      total_count[a[i]]++;
    end
    foreach(b[i]) begin 
      total_count[b[i]]++;
    end
    foreach(c[i]) begin 
      total_count[c[i]]++;
    end
    // verify
    assert(count == total_count) else  begin
      $error("The sum of count of each unique element in each sub-queue doesn't match with count of that element in the main-queue");
      $display("count: %p",count);
      $display("total_count: %p",total_count);
    end
    
    // CHECK:2
    // verify if each element is unique or not
    uniqueq = a.unique();
    assert(uniqueq.size() == a.size()) else 
      $error("queue a is not unique, unique count:%0d, normal count:%0d",uniqueq.size(),a.size());
    
    uniqueq = b.unique();
    assert(uniqueq.size() == b.size()) else begin 
      $error("queue b is not unique, unique count:%0d, normal count:%0d",uniqueq.size(),b.size());
    end
    
    uniqueq = c.unique();
    assert(uniqueq.size() == c.size()) else
      $error("queue c is not unique, unique count:%0d, normal count:%0d",uniqueq.size(),c.size());
  endfunction 
    
  function void show();
    $display("The queues are:");
    $display("a is %p",a);
    $display("b is %p",b);
    $display("c is %p",c);
  endfunction 
    
endclass

module tb;
  initial begin
    myclass c = new;
    repeat(10) begin 
      assert(c.randomize());
      c.show();
    end
  end
endmodule