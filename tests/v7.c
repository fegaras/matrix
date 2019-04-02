var M: matrix[double];
var N: matrix[double];
var R: matrix[double];

for i = 1, 10 do
   for j = 1,20 do {
      R[i,j] = 0.0;
      for k = 1,5 do
         R[i,j] = R[i,j]+M[i,k]*N[k,j];
   };
