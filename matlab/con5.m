function [c,ceq] = con5(x)
m2_6=[
  0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ;
  1, -2, -1, 0, 0, 0, 0, -1, 0, -1, 1, 0, 1, -3, 0, 3 ;
  0, -1, 0, -1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0 ;
  0, 0, -1, 0, 1, 0, 1, -1, 0, -3, 0, 0, 0, -1, 0, 0 ;
  0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, -3, 0, 0, -1, 0 ;
  -1, 0, 1, 0, 0, 2, -1, 1, 0, 1, 0, 0, 0, 3, 0, 0 ;
  0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ;
  0, -1, 0, -1, 0, 1, 0, 0, 3, 2, 0, 1, 0, -2, 1, 0 ;
  0, 0, 1, 0, -1, 0, 0, 3, 0, 1, -3, 4, -1, 1, -4, -1 ;
  0, -1, 0, -3, 0, 1, 0, 2, 1, 6, 0, 3, 0, 2, 1, 0 ;
  0, 1, 0, 0, 0, 0, 0, 0, -3, 0, 0, -1, 2, 0, -1, -2 ;
  0, 0, 1, 0, -3, 0, 0, 1, 4, 3, -1, 6, -3, 1, 0, -1 ;
  0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 2, -3, 0, 0, -1, -2 ;
  0, -3, 0, -1, 0, 3, 0, -2, 1, 2, 0, 1, 0, 0, 3, 0 ;
  0, 0, 3, 0, -1, 0, 0, 1, -4, 1, -1, 0, -1, 3, -6, -3 ;
  0, 3, 0, 0, 0, 0, 0, 0, -1, 0, -2, -1, -2, 0, -3, -6 
 ];
m3_7=[
  0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ;
  0, 0, 0, -2, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0 ;
  1, 0, -2, 0, 1, 0, 0, -6, 0, -2, 0, 0, 0, -2, 0, 0 ;
  0, -2, 0, 0, 0, 1, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0 ;
  0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, -3, 0, 0, -1 ;
  0, 1, 0, 1, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ;
  -1, 0, 0, 0, 0, 0, 2, 3, 0, 1, 0, 0, 0, 1, 0, 0 ;
  0, 0, -6, 0, 0, 0, 3, 6, 0, 2, 1, 0, 3, 2, 0, 1 ;
  0, 1, 0, 3, 0, 0, 0, 0, -8, 0, 0, -2, 0, 0, -10, 0 ;
  0, 0, -2, 0, 0, 0, 1, 2, 0, 0, 3, 0, 1, -2, 0, 1 ;
  0, 0, 0, 0, -1, 0, 0, 1, 0, 3, 0, 0, 2, 1, 0, -2 ;
  0, 1, 0, 1, 0, 0, 0, 0, -2, 0, 0, -6, 0, 0, -2, 0 ;
  0, 0, 0, 0, -3, 0, 0, 3, 0, 1, 2, 0, 6, 1, 0, 2 ;
  0, 0, -2, 0, 0, 0, 1, 2, 0, -2, 1, 0, 1, 0, 0, 3 ;
  0, 3, 0, 1, 0, 0, 0, 0, -10, 0, 0, -2, 0, 0, -8, 0 ;
  0, 0, 0, 0, -1, 0, 0, 1, 0, 1, -2, 0, 2, 3, 0, 0 
 ];
m8_14=[ 
  0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0 ;
  0, 0, 0, 0, 0, 1, 0, -1, -1, -2, 0, 0, 0, -2, 1, 0 ;
  0, 0, 0, 0, 0, 0, -1, 2, 0, 2, 0, 0, -1, 1, 0, 1 ;
  0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -1, -1, 0 ;
  0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0 ;
  0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -3, 0, 0 ;
  0, 0, -1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0 ;
  -1, -1, 2, 1, -1, 0, 2, -4, -1, -1, 2, 0, 2, 0, 1, 1 ;
  0, -1, 0, 0, 0, 0, 0, -1, 4, -2, 0, -1, 2, 3, 2, -2 ;
  0, -2, 2, 0, 1, -2, 2, -1, -2, 0, 0, -3, 1, 1, 0, -1 ;
  0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, -2, -1, 0 ;
  0, 0, 0, 1, 0, 0, 0, 0, -1, -3, 1, 0, 0, -2, 1, -1 ;
  0, 0, -1, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 2, -2, 0 ;
  1, -2, 1, -1, 0, -3, 1, 0, 3, 1, -2, -2, 2, 4, -1, 0 ;
  0, 1, 0, -1, 0, 0, 0, 1, 2, 0, -1, 1, -2, -1, 2, -2 ;
  0, 0, 1, 0, 0, 0, 0, 1, -2, -1, 0, -1, 0, 0, -2, 0 
 ];
c = [];
ceq = [
    x*m2_6*transpose(x),
    x*m3_7*transpose(x),
    x*m8_14*transpose(x),
    ];
end

