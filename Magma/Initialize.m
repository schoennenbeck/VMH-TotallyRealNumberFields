import "BasicData.m" : K,L;
deg:=Degree(K);
n:=Dimension(Parent(L[1]));
dimsym:=deg*n*(n+1) div 2;
BBsym:=[SymmetricCoordinatesToMatrix([0: j in [1..i-1]] cat [1] cat [0: j in [1..dimsym-i]]): i in [1..dimsym]];
LReg:=[RegularCoordinates(x): x in L];
LReg:=LatticeWithBasis(Matrix(LReg));
BK:=Basis(K); assert BK[1] eq 1;
C:=[RegRepMat(MatrixRing(K,n)!BK[i]): i in [1..deg] ];
CE:=&cat[Eltseq(x): x in C];
l:=LCM([Denominator(x): x in CE]);
C:=[ChangeRing(x*l,Integers()): x in C];

BLidBS:=Matrix([&cat[Eltseq(x): x in Eltseq(l)]: l in L]);
BSidBL:=BLidBS^-1;

CBL:=[BLidBS*x*BSidBL: x in C];
CBLE:=&cat[Eltseq(x): x in CBL];
l:=LCM([Denominator(x): x in CBLE]);
CBL:=[ChangeRing(x*l,Integers()): x in CBL];





































