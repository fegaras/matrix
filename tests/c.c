
var n: int = 4;
for i = 1,10 do {
    var x: int = n+1;
    var v: vector[int] = vector(1,2);
    foreach a in v do x = x+a;
    n=n+i+x;
};



/*
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
