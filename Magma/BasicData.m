/*K:=
QuadraticField(2)
; n:=2;V:=KMatrixSpace(K,n,1);  L:=[IntegralBasis(K)[i]*V.j: i in 
[1..Degree(K)],j in [1..n]];*/
K:=QNF();
n:=3;
V:=KMatrixSpace(K,n,1);
L:=[V.j: j in [1..n]];
