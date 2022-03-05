// Constraint for a number to be power of 4

class check;
  rand bit [31:0] a;

  // 4^x = (2^2)^x = 2^(2x) = all even powers of two
  constraint ca{
    // there shall be only one bit set 
    $countones(a) == 1;
    // make sure that odd bits are not set
    // coz we need only even powers of 2
    foreach(a[i]) 
      (i%2 != 0) -> (a[i] == 0);
  }
endclass

module tb;
  initial begin
    check c = new;
    c.randomize();
    $display("%0d %0b", c.a, c.a);
    // verify
    assert($clog2(c.a)/2 == int'($clog2(c.a))/2);
  end
endmodule