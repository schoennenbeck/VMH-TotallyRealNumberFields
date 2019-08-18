import "../../BasicData.m": K,L;
deg:=Degree(K);
n:=Dimension(Parent(L[1]));

SymEltSeq:=function(mat) //assuming mat is symmetric form the irredundant eltseq
 n:=Nrows(mat);
 res:=[];
 for i in [1..n] do
  res cat:= Eltseq(mat[i])[1..i];
 end for;
 return res;
end function;

intrinsic IsInGL(g::Mtrx)->BoolElt //THIS NEEDS TO BE CORRECTED.
 {}
 if Determinant(g) eq 0 then return false; end if;
 return g in MatrixRing(Integers(K),n) and g^-1 in MatrixRing(Integers(K),n);
end intrinsic;

intrinsic RealToString(r::FldReElt) -> MonStgElt
 {This converts a floating point real number into a string.}
 if Sign(r) eq -1 then
  str := "-";
 else
  str := "";
 end if;
 r:=Abs(r);
 p := Integers()! Floor(r) ;
 str := str cat IntegerToString(p) cat ".";
 for i := 1 to 15 do
  r:=10*(r-p);
  p := Integers()! Floor(r) ;
  str := str cat IntegerToString(p);
 end for;
 return str;
end intrinsic;

intrinsic SymmetricCoordinates(M::Mtrx)->SeqEnum
 {}
 Ses:=SymEltSeq(M);
 return &cat[Eltseq(K!x): x in Ses];
end intrinsic;

intrinsic SymmetricCoordinatesToMatrix(S::SeqEnum)->Mtrx
 {The inverse}
 SS:=[[S[(deg)*(i-1)+j]: j in [1..deg]]: i in [1..(#S div deg)]];
 SS:=[K!x: x in SS];
 return SymmetricMatrix(SS);
end intrinsic;

intrinsic RegularCoordinates(v::Any)->SeqEnum
 {}
 return &cat[Eltseq(K!x): x in Eltseq(v)];
end intrinsic;

intrinsic RegRep(x::FldNumElt)->Mtrx
 {The regular representation of the element x in K}
 x:=K!x;
 return MatrixRing(Rationals(),deg)!(Eltseq(x) cat &cat[Eltseq(x*Basis(K)[i]): i in [2..deg]]);
end intrinsic;

intrinsic RegRepMat(x::Mtrx)->Mtrx
 {The regular representation of the matrix x over K}
 Ex:=Eltseq(x);
 Ex:=[RegRep(K!y): y in Ex];
 return BlockMatrix(Nrows(x),Ncols(x),Ex); 
end intrinsic;

intrinsic RegRepInv(x::Mtrx)->FldNumElt
 {}
 return K!Eltseq(x[1]);
end intrinsic;

intrinsic RegRepMatInv(x::Mtrx)->Mtrx
 {}
 Bes:=[];
 for i in [1..Nrows(x) div deg] do
  for j in [1..Ncols(x) div deg] do
   Append(~Bes,ExtractBlock(x,deg*(i-1)+1,deg*(j-1)+1,deg,deg));
  end for;
 end for;
 Es:=[RegRepInv(x): x in Bes];
 return KMatrixSpace(K,Nrows(x) div deg, Ncols(x) div deg)!Es;
end intrinsic;

intrinsic InitializeData(K::FldNum,n::RngIntElt)
 {Initalizes the BasicData file to work with O_K^n}
 bd:="../../BasicData.m";
 V:=KMatrixSpace(K,n,1);
 PrintFile(bd,"K:=":Overwrite:=true);
 PrintFileMagma(bd,K);
 PrintFile(bd,"; n:=" cat Sprint(n) cat ";V:=KMatrixSpace(K,n,1);  L:=[IntegralBasis(K)[i]*V.j: i in [1..Degree(K)],j in [1..n]];");
 PrintFile("../../Initialize.m","");
 PrintFile("../../DivAlg/Voronoi/Voronoi.m","");

end intrinsic;
 
 

