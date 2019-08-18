import "../../BasicData.m": K,L;
import "../../Initialize.m": n,BBsym,LReg,dimsym,deg,C,CBL,BLidBS,BSidBL;



intrinsic AutomorphismGroup(A::DAForm:CheckMembership:=0) -> Grp
 {Calculates the automorphism group of the form A.}
 if CheckMembership cmpeq 0 then 
  if assigned A`Aut then return A`Aut; end if;
  Gram:=MatrixRing(Rationals(),#L)!0;
  for i in [1..#L] do
   for j in [i..#L] do
    Gram[i][j]:=MyInnerProduct(A`Matrix,L[i]*Dagger(L[j]));
    Gram[j][i]:=Gram[i][j];
   end for;
  end for;
  l:=LCM([Denominator(x): x in Eltseq(Gram)]);
  Gram:=ChangeRing(l*Gram,Integers());
  GG:=AutomorphismGroup([Gram] cat [x*Gram: x in CBL]);
  A`Aut:=MatrixGroup<n,K|[Transpose(RegRepMatInv(BSidBL*ChangeRing(x,Rationals())*BLidBS)): x in Generators(GG)]>;
  return A`Aut;
 else
  G:=AutomorphismGroup(A);
  order:=#[x: x in G| CheckMembership(x)];
  GG:=sub<G|[x: x in Generators(G) | CheckMembership(x)]>;
  while not #GG eq order do
   g:=Random(G);
   if not g in GG and CheckMembership(g) then
    GG:=sub<G|Generators(GG) join {g}>;
   end if;
  end while;
  return GG;
 end if;
end intrinsic;
