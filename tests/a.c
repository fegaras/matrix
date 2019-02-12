var V: vector[int] = vector(1,2,3);
var M: matrix[int];

for i = 1,V.length do
    V[i] = V[i]+1;

for i = 1,M.rows do
   for j = 1,M.cols do
      M[i,j] = M[j,i]+5;

var n: int = 0;

foreach v in V do
   n = n+v;
