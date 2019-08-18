intrinsic SLPresentation(K::FldNum,n::RngIntElt)->FPGrp,GrpHom,Any
 {Computes a presentation of SL_n(K) and a constructive membership algorithm}
 require IsTotallyReal(K): "This only works for totally real number fields.";
 InitializeData(K,n);
 GG:=GL(n,K);
 powertest:=func<x| IsPower(Determinant(x),n)>; //This gives a finite index subgroup of GL_n that coincides with SL_n except for the center.
 V:=VoronoiAlgorithm(:CheckMembership:=powertest);
 PowerGroup,tomatpow:=Presentation(V);

 UG,ug:=UnitGroup(Integers(K));
 CenterGens:=[GG!(MatrixRing(K,n)!ug(UG.i)):  i in [1..Ngens(UG)]];
 PowGens:=[tomatpow(x): x in Generators(PowerGroup)];
 SLGens:=[];
 for g in PowGens do
  dg:=Determinant(g);
  b,r:=IsPower(dg,n);
  assert b;
  rr:=r@@ug;
  e:=Eltseq(rr);
  Append(~SLGens,g*(&*[CenterGens[i]^-e[i]: i in [1..#e]]));
 end for;
 if IsEven(n) then 
  Append(~SLGens,GG!(MatrixRing(K,n)!-1));
 end if;

 S:=FreeGroup(#SLGens);
 SR:=[];
 for r in Relations(PowerGroup) do
  Append(~SR,S!Eltseq(LHS(r))=S!Eltseq(RHS(r)));
 end for;
 
 for x in CenterGens do
  wx:=SolveWordProblem(x,V);
  Append(~SR,S!1=S!Eltseq(wx));
 end for;

 if IsEven(n) then //We need to fix the mistake we made by making things projective
  negone:=S.Ngens(S); //The negative identity
  for i in [1..#SR] do
   lhs:=&*([GG!1] cat [SLGens[Abs(y)]^Sign(y): y in Eltseq(LHS(SR[i]))]);
   rhs:=&*([GG!1] cat [SLGens[Abs(y)]^Sign(y): y in Eltseq(RHS(SR[i]))]);
   if not lhs eq rhs then
    assert lhs*SLGens[#SLGens] eq rhs;
    SR[i]:=LHS(SR[i])*negone=RHS(SR[i]);
   end if;
  end for;
  Append(~SR,negone^2=S!1);
  SR cat:= [S.i*negone*S.i^-1*negone=S!1: i in [1..Ngens(S)-1]];
 end if;

 SS:=quo<S|SR>;
 tomat:=hom<SS->GG|SLGens>;

 solver:=function(x)//We now do constructive membership in the new generators
  wx:=SS!Eltseq(SolveWordProblem(x,V));
  if IsOdd(n) then
   return wx;
  else
   matx:=tomat(wx);
   if matx eq x then
    return wx;
   else
    assert matx*(GG!(MatrixRing(K,n)!-1)) eq x;
    return wx*SS.Ngens(SS);
   end if;
  end if;
 end function;

 return SS,tomat,solver;
end intrinsic;