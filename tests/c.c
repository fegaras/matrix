var v: vector[int];
var n: int = 0;

foreach a in v do n = n+a;

/*
for i = 1, 10 do
  v[i] = v[i]+1;


var R: matrix[double];

for i = 1, 10 do
   for j = 1,20 do {
      R[i,j] = R[i,j]+1.0;
   };

var v: vector[int];
var w: vector[int];

for i = 1, 10  do v[w[i]] = v[w[i]]+1;
for j = 1, 10  do w[j] = w[j]+1;

var M: matrix[double];
var N: matrix[double];
var R: matrix[double];

for i = 1, 10 do
   for j = 1,20 do {
      R[i,j] = 0.0;
      for k = 1,5 do
         R[i,j] = R[i,j]+M[i,k]*N[k,j];
   };



var v: vector[int];
val n: int = v[2]+1;


for i = 1,10 do {
    var x: int = n+v[i];
    foreach a in v do x = x+a;
    n=n+i+x;
    v[i] = n*3;
};

val v: vector[int] = vector(1,2);
val n: int = v[2]+1;

foreach a in v do n=n+a;

var n: int = 4;
n = n+1;

var n: int = 4;
for i = 1,10 do {
    var x: int = n+1;
    var v: vector[int] = vector(1,2);
    foreach a in v do x = x+a;
    n=n+i+x;
};

var n: int = 4;
n = n+1;
var x: int = n+1;
x=x*3;
n=x*n;
var y: int = x+n;

var n: int = 0;
val v: vector[int] = vector(1,2);
var x: int = 4;
for i = 1,10 do n=n+i;
//val x: int = n*3;
foreach a in v do n=n+a;
n=x+n;
//n=n*5;
*/
