import "../../BasicData.m": K,L;
import "../../Initialize.m": n,BBsym,LReg,dimsym,deg,C,CBL,BLidBS,BSidBL;



intrinsic Dagger(A::Any) -> AlgMatElt
 {The involution dagger.}
 return Transpose(A);
end intrinsic;

intrinsic MyInnerProduct(A::Mtrx,B::Mtrx) -> FldElt
 {Inner product of A and B.}
 return Rationals()!Trace(Trace(A*Dagger(B)));
end intrinsic;

/*intrinsic PreMyInnerProduct(A::Mtrx,B::Mtrx) -> FldElt
 {Inner product of A and B in K.}
 return Trace(A*Dagger(B));
end intrinsic;*/

intrinsic Evaluate(A::Mtrx,x::Mtrx) -> Any
 {Evaluates the vector x at the matrix A via the inner product.}
 return MyInnerProduct(A,x*Dagger(x));
end intrinsic;

/*intrinsic PreEvaluate(A::Mtrx,x::Mtrx) -> Any
 {Value of the evaluation of x at A in the number field K.}
 return PreMyInnerProduct(A,x*Dagger(x));
end intrinsic;*/

intrinsic RegularGramMatrix(A::DAForm)->Mtrx
 {The Gram matrix of A on L}
 Gram:=MatrixRing(Rationals(),#L)!0;
 for i in [1..#L] do
  for j in [i..#L] do
   Gram[i][j]:=MyInnerProduct(A`Matrix,L[i]*Dagger(L[j]));
   Gram[j][i]:=Gram[i][j];
  end for;
 end for;
 return Gram;
end intrinsic;

intrinsic FormMinimum(A::DAForm) -> FldRatElt
 {The minimum of the form A on the maximal order.}
 if assigned A`Minimum then return A`Minimum; end if;
 Gram:=MatrixRing(Rationals(),#L)!0;
 for i in [1..#L] do
  for j in [i..#L] do
   Gram[i][j]:=MyInnerProduct(A`Matrix,L[i]*Dagger(L[j]));
   Gram[j][i]:=Gram[i][j];
  end for;
 end for;
 LL:=LatticeWithGram(Gram);
 A`Minimum:=Minimum(LL);
 return A`Minimum;
end intrinsic;


intrinsic MinimalVectors(A::DAForm) -> SeqEnum
 {Returns the shortest vectors of the form A in M.}
 if assigned A`MinimalVectors then return A`MinimalVectors; end if;
 Gram:=MatrixRing(Rationals(),#L)!0;
 for i in [1..#L] do
  for j in [i..#L] do
   Gram[i][j]:=MyInnerProduct(A`Matrix,L[i]*Dagger(L[j]));
   Gram[j][i]:=Gram[i][j];
  end for;
 end for;
 LL:=LatticeWithGram(Gram);
 S:=ChangeRing(ShortestVectorsMatrix(LL),Integers());
 A`MinimalVectors:=[&+[S[i][j]*L[j]: j in [1..#L]]: i in [1..Nrows(S)]];
 A`Minimum:=Evaluate(A`Matrix,A`MinimalVectors[1]);
 return A`MinimalVectors;
end intrinsic;

intrinsic FindPerp(S::SeqEnum) -> AlgMatElt
 {Find perpendicular vector to the projections in the input list S.}
 SS:=S;
 T:=KMatrixSpace(K,dimsym,#SS)!0;
 for i in [1..#BBsym] do
  for j in [1..#SS] do
   T[i][j]:=MyInnerProduct(BBsym[i],SS[j]);
  end for;
 end for;
 KM:=KernelMatrix(T);
 if Nrows(KM) eq 0 then return false; end if;
 return SymmetricCoordinatesToMatrix(Eltseq(KM[1]));

end intrinsic;

intrinsic FindAllPerp(S::SeqEnum) -> AlgMatElt
 {Find all perpendicular vectorS to the projections in the input list S.}
 SS:=S;
 T:=KMatrixSpace(K,dimsym,#SS)!0;
 for i in [1..#BBsym] do
  for j in [1..#SS] do
   T[i][j]:=MyInnerProduct(BBsym[i],SS[j]);
  end for;
 end for;
 KM:=KernelMatrix(T);
 if Nrows(KM) eq 0 then return false; end if;
 return [SymmetricCoordinatesToMatrix(Eltseq(KM[i])): i in [1..Nrows(KM)]];
end intrinsic;

intrinsic PerfectionRank(A::DAForm) -> RngIntElt
 {Returns the perfection rank of the input form A.}
 if assigned A`PerfectionRank then return A`PerfectionRank; end if;
 List:=[x*Dagger(x) : x in MinimalVectors(A)];
 List:=[SymmetricCoordinates(x) : x in List];
 MM:=Matrix(List);
 A`PerfectionRank:=Rank(MM);
 return A`PerfectionRank;
end intrinsic;

intrinsic PerfectionCorank(A::DAForm) -> RngIntElt
 {Returns the perfection rank of the input form A.}
 return dimsym-PerfectionRank(A);
end intrinsic;

intrinsic PerfectionRankDAList(S::SeqEnum) -> Any
 {Returns the perfection rank of the projections onto the vectors contained in the input list S.}
 List:=[x*Dagger(x) : x in S];
 List:=[SymmetricCoordinates(x): x in List];
 MM:=Matrix(List);
 return Rank(MM);
end intrinsic;

intrinsic IsPositiveForm(A::DAForm) -> Any
 {Checks whether the input form A is positive definite on the maximal order M.}
 if assigned A`IsPositive then return A`IsPositive; end if;
 Gram:=MatrixRing(Rationals(),#L)!0;
 for i in [1..#L] do
  for j in [i..#L] do
   Gram[i][j]:=MyInnerProduct(A`Matrix,L[i]*Dagger(L[j]));
   Gram[j][i]:=Gram[i][j];
  end for;
 end for;
 A`IsPositive:=IsPositiveDefinite(Gram);
 return A`IsPositive;
end intrinsic;

intrinsic IsIntegral(A::Mtrx) -> Any
 {Checks if an element of the rational algebra is contained in the order specified by L.}
 for x in L do
  if not Vector(RegularCoordinates(A*x)) in LReg then
   return false;
  end if;
 end for; 
 return true;
end intrinsic;

intrinsic IsIntegralUnit(A::Mtrx) -> Any
 {Checks if an element of the rational algebra is a unit in the maximal order specified via the basis BB.}
 return IsIntegral(A) and IsIntegral(A^-1);
end intrinsic;

intrinsic TestIsometry(A::DAForm,B::DAForm:SL:=false,CheckMembership:=0) -> Any
 {Tests whether the two forms A and B are isometric. If SL then only isometries with determinant 1 or -1 are considered. The resulting element g fullfills g^dagger A g = B}
 if CheckMembership cmpeq 0 then 
  if SL and Determinant(A`Matrix) ne Determinant(B`Matrix)
   then return false,_;
  end if;
   GramA:=MatrixRing(Rationals(),#L)!0;
   GramB:=MatrixRing(Rationals(),#L)!0;
  for i in [1..#L] do
   for j in [i..#L] do
    GramA[i][j]:=MyInnerProduct(A`Matrix,L[i]*Dagger(L[j]));
    GramA[j][i]:=GramA[i][j];
    GramB[i][j]:=MyInnerProduct(B`Matrix,L[i]*Dagger(L[j]));
    GramB[j][i]:=GramB[i][j];
   end for;
  end for;
  l:=LCM([Denominator(x): x in Eltseq(GramA)] cat [Denominator(x): x in Eltseq(GramB)]);
  GramA:=ChangeRing(l*GramA,Integers());
  GramB:=ChangeRing(l*GramB,Integers());
  b,g:=IsIsometric([GramA] cat [x*GramA: x in CBL],[GramB] cat [x*GramB: x in CBL]);
  if not b then
   return false,_;
  end if;
  return true,Transpose(RegRepMatInv(BSidBL*ChangeRing(g,Rationals())*BLidBS));
 else
  b,g:=TestIsometry(A,B);
  if not b then 
   return false,_;
  end if;
  for y in AutomorphismGroup(B) do
   if CheckMembership(g*y) then
    return true,g*y;
   end if;
  end for;
  return false,_;
 end if;
end intrinsic;



intrinsic IsFace(L::SeqEnum) -> Any
 {Checks the dimension of a ist of possible facet vectors.}
 return PerfectionRankDAList(L) eq dimsym-1;
end intrinsic;
