function res = fun4(x)
%UNTITLED Summary of this function goes here
%   Detailed explanation goes here
num=[
 0, 6, 0, 0, 3, 0, 0, 0;
 6, -12, 6, 0, 0, 18, 6, 6;
 0, 6, 0, 6, 6, 0, 0, 0;
 0, 0, 6, 0, 0, 3, 3, 9;
 3, 0, 6, 0, -6, 0, 0, 0;
 0, 18, 0, 3, 0, -36, -6, -18;
 0, 6, 0, 3, 0, -6, 0, 6;
 0, 6, 0, 9, 0, -18, 6, -18
];
denum=[
 1, 0, 0, 0, 0, 0, 0, 0;
 0, 6, 0, 0, 0, 0, 0, 0;
 0, 0, 6, 0, 0, 0, 0, 0;
 0, 0, 0, 3, 0, 0, 0, 0;
 0, 0, 0, 0, 3, 0, 0, 0;
 0, 0, 0, 0, 0, 9, 3, 3;
 0, 0, 0, 0, 0, 3, 9, 3;
 0, 0, 0, 0, 0, 3, 3, 9
];
res=x*num*transpose(x)/(x*denum*transpose(x));
end

