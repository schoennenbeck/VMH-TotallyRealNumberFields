import "../../BasicData.m": K,L;
import "../../Initialize.m": n,BBsym,LReg,dimsym,deg,C;

intrinsic ComputeRelations(V::VData)
 {Compute the relations w.r.t. V.}
 if not assigned V`Stabilizers then ComputeStabilizers(V); end if;
 if not assigned V`Barycenters then ComputeBarycenters(V); end if;
 if not assigned V`Edges then ComputeEdges(V); end if;
 Barycenters:=V`Barycenters;
 Edges:=V`Edges;
 Stabs:=[AutomorphismGroup(x:CheckMembership:=V`CheckMembership): x in V`PerfectList];
 PL:=V`PerfectList;
 FL:=V`FacesList;
 temp:=[* *];
 for i in [1..#FL] do
  M:=MinimalVectors(PL[i]);
  Append(~temp,[* {M[n]*Dagger(M[n])/Trace(Trace(M[n]*Dagger(M[n]))) : n in N} : N in FL[i] *]);
 end for;
 Facegens:=temp;
 FTL:=V`FaceTrafoList;
 NL:=V`NeighbourList;
 OKGens:=V`MultFreeList;
 Words:=[];
 Relations:=[];
 for a in [1..#PL] do
  print "Now doing perfect form number ", a,". Its Voronoi domain has ",#Edges[a], " edges.";
  for E in Edges[a] do
   for f in [1..#FL[a]] do
    if E subset Facegens[a][f] then
     cur:=a;
     S:=MinimalVectors(PL[cur]);
     face:=f;
     groupelt:=FTL[cur][face];
     groupeltprevious:=GL(n,K)!1;
     if groupelt ne groupeltprevious then
      word:=[[cur,face]];
      p:=0; e:=0;
      if groupelt in OKGens then p:=Position(OKGens,groupelt); e:=1; end if;
      relation:=[*<p,e>*];
     else
      word:=[[cur,face]];
      relation:=[**];
     end if;
       
      Nb:=NL[cur][face];
      finished:=false;
      k:=1;
      count:=1;
      while not finished do
       count +:= 1;
       h1:=groupeltprevious^-1;
       F:={h1^-1*S[x]*Dagger(S[x])*Dagger(h1^-1) : x in FL[cur][face]};  //!!!
       F:={x/Trace(Trace(x)) : x in F};
       h:=groupelt^-1;
       SN:=MinimalVectors(PL[Nb]);
       X:=[{h^-1*SN[x]*Dagger(SN[x])*Dagger(h^-1) : x in f} : f in FL[Nb]];
       X:=[{m/Trace(Trace(m)) : m in x} : x in X];
       for i in [1..#X] do
        if E subset X[i] and X[i] ne F then
         cur:=Nb;
         face:=i;
         g:=FTL[cur][face];
         if g ne MatrixRing(K,n)!1 then
          Append(~word,[Nb,i]);
          p:=0; e:=0;
          if g in OKGens then p:=Position(OKGens,g); e:=1; end if;
          Append(~relation,<p,e>);
         end if;
         Nb:=NL[cur][face];
         groupeltprevious:=groupelt;
         groupelt:=groupelt*g;
         S:=MinimalVectors(PL[cur]);
         break;
        end if;
       end for;
       k+:=1;
       if GL(n,K)!groupelt in Stabs[a] then
        Append(~relation,<a,groupelt>);
        finished:=true;
       end if;
      end while;
      Append(~Words,word);
      Append(~Relations,relation);
    end if;
   end for;
  end for;
 end for;
 V`Words:=Words;
 V`Relations:=Relations;
end intrinsic;


intrinsic Presentation(V::VData : projective:=false,simplify:=true)-> GrpFP
 {Computes a presentation of the arithmetic group underlying V}
 if assigned V`Presentation and V`Presentation then
  if projective then
   if simplify then
    return V`GSimplified,V`GSimplifiedHom,V`GSimplifiedPro,V`GSimplifiedToProHom;
   else
    return V`GNonsimplified, V`GNonsimplifiedHom,V`GNonsimplifiedPro,V`GNonsimplifiedToProHom;
   end if;
  else
   if simplify then
    return V`GSimplified,V`GSimplifiedHom;
   else
    return V`GNonsimplified, V`GNonsimplifiedHom;
   end if;
  end if;
 end if;
 
 if not assigned V`Relations then
  ComputeRelations(V);
 end if;
 print "Edges relations computed";
 Words:=V`Words;
 Gen:=V`MultFreeList;
 Rel:=V`Relations;
 Stabs:=[AutomorphismGroup(x:CheckMembership:=V`CheckMembership): x in V`PerfectList];
 FPStabs:=[];
 FPStabsHom:=[];
 PL:=V`PerfectList;
 FTL:=V`FaceTrafoList;
 FL:=V`FacesList;
 PNL:=V`PerfectNeighbourList;
 NL:=V`NeighbourList;
 One:=Parent(Gen[1])!1;
 for S in Stabs do
  F,f:=FPGroup(S);
  Append(~FPStabs,F);
  Append(~FPStabsHom,f);
 end for;
 ng:=#Gen+&+[#Generators(x): x in FPStabs];
 F:=FreeGroup(ng);
 R:=[];
 

 //First compute the relations coming from the intersection of stabilizers
 for i in [1..#Stabs] do 
  for j in [i+1..#Stabs] do
   offseti:=i eq 1 select #Gen else #Gen+ &+[Ngens(FPStabs[k]): k in [1..i-1]];
   offsetj:=j eq 1 select #Gen else #Gen+ &+[Ngens(FPStabs[k]): k in [1..j-1]];
   for x in Stabs[i] meet Stabs[j] do
    if x ne Stabs[i]!1 then
     X:=x @@FPStabsHom[i];
     Y:=x @@ FPStabsHom[j];
     FX:=[k gt 0 select k+offseti else k-offseti : k in Eltseq(X)];
     FY:=[k gt 0 select k+offsetj else k-offsetj : k in Eltseq(Y)];
     Append(~R,F!FX=F!FY);
    end if;
   end for;
  end for;
 end for;
 print "Intersection relations done.";

 //Now compute the relations due to the edges
 for w in Rel do
  lhs:=F!1;
  lhsmat:=One;
  for i in [1..#w-1] do
   lhs:=lhs*(F.w[i][1])^(w[i][2]);
   lhsmat:=lhsmat*(Gen[w[i][1]])^(w[i][2]);
  end for;
  cur:=w[#w][1];
  rhsmat:=w[#w][2];
  if rhsmat eq -lhsmat then
   rhsmat:=-rhsmat;
  end if;
  rhs:=rhsmat @@ FPStabsHom[cur];
  rhs:=ElementToSequence(rhs);
  offset:=cur eq 1 select #Gen else #Gen+&+[#Generators(FPStabs[i]): i in [1..cur-1]];
  rhs:=[Sign(i) gt 0 select i+offset else i-offset: i in rhs];
  Append(~R,lhs=F!rhs);
 end for;
 print "Edge relations done.";
 //These are the relations coming from the finite stabilizers
 for cur in [1..#FPStabs] do 
  offset:=cur eq 1 select #Gen else #Gen+&+[#Generators(FPStabs[i]): i in [1..cur-1]];
  SRel:=Relations(FPStabs[cur]);
  for r in SRel do
   lhs:=ElementToSequence(LHS(r));
   rhs:=ElementToSequence(RHS(r));
   rhs:=[Sign(i) gt 0 select i+offset else i-offset: i in rhs];
   lhs:=[Sign(i) gt 0 select i+offset else i-offset: i in lhs];
   Append(~R,F!rhs=F!lhs);
  end for;
 end for;
 print "Stabilizer relations done.";
 //These are the Poincare relations due to facets which lie in the same orbit.
 for p in [1..#PL] do
  for f in [1..#FL[p]] do
   if FTL[p][f] ne 1 then
    nb:=NL[p][f];
    NB:=PL[nb];
    x:=FTL[p][f];
    X:=Position(Gen,FTL[p][f]);
    face:={MinimalVectors(PL[p])[i]*Dagger(MinimalVectors(PL[p])[i]): i in FL[p][f]};
    //face:={y/Trace(Trace(y)) : y in face};
    Xinvface:={x^-1*v*Dagger(x^-1): v in face};
    Xinvface:={y/Trace(Trace(y)) : y in Xinvface};
    NBfaces:=[{MinimalVectors(NB)[i]*Dagger(MinimalVectors(NB)[i]) : i in y}: y in FL[nb]];
    NBfaces:=[{m/Trace(Trace(m)) : m in M} : M in NBfaces];
    cor:=Position(NBfaces,Xinvface);
    y:=FTL[nb][cor];
    Y:=Position(Gen,y);
    //The relations are y^-1x^-1 in Stab(p) 
    lhs1:=[-Y,-X];
    rhs1:=ElementToSequence((y^-1*x^-1) @@ FPStabsHom[p]);
    offset1:=p eq 1 select #Gen else #Gen+&+[#Generators(FPStabs[i]): i in [1..p-1]];
    rhs1:=[Sign(i) gt 0 select i+offset1 else i-offset1: i in rhs1];
    Append(~R,F!lhs1=F!rhs1);
   end if;
  end for;
 end for;
 print "Poincare relations done.";
 //Relations corresponding to the orbits of the stabilizers on the facets
 for p in [1..#PL] do
  for f in [1..#FL[p]] do
   for f1 in [f+1..#FL[p]] do
    if NL[p][f] eq NL[p][f1] then
     x:=FTL[p][f];
     X:=Position(Gen,x);
     y:=FTL[p][f1];
     Y:=Position(Gen,y);
     for g in Stabs[p] do
      s:=GL(n,K)!(x*(Parent(x)!g)*y^-1);
      if s in Stabs[p] then
       offset:=p eq 1 select #Gen else #Gen+&+[#Generators(FPStabs[i]): i in [1..p-1]];
       lhs:=[X] cat [t gt 0 select t+offset else t-offset: t in Eltseq(g @@ FPStabsHom[p])] cat [-Y];
       rhs:=[t gt 0 select t+offset else t-offset: t in Eltseq(s @@ FPStabsHom[p])];
       Append(~R,F!lhs=F!rhs);
       break g;
      end if;
     end for;
    end if;
   end for;
  end for;
 end for; 
 print "Stabilizer orbit relations done."; 
 Img:=Gen;
 for i in [1..#PL] do
  Img cat:=[FPStabsHom[i](FPStabs[i].j): j in [1..#Generators(FPStabs[i])]];
 end for;

 GL:=sub<GeneralLinearGroup(n,K)|Img>;
 require IsSatisfied(R,[GL!x: x in Img]): "Some of the computed relations are not satisfied. This should not have happened";
 G:=quo<F|R>;
 V`GNonsimplified:=G; 

 g:=hom<G->GL|Img>;
 V`GNonsimplifiedHom:=g;
 
 H,h:=Simplify(G);
 hnew:=hom<H->GL|[g(h(H.i)): i in [1..#Generators(H)]]>;
 V`GSimplified:=H;
 V`GSimplifiedHom:=hnew; 
 V`GNonsimplifiedToSimplifiedHom:=h; 

 
 offset:=#Gen;
 NegOne:=(Parent(Gen[1])!-1) @@ FPStabsHom[1];
 NegOne:=Eltseq(NegOne);
 NegOne:=[t gt 0 select t + offset else t-offset: t in NegOne];
 RP:=R cat [F!NegOne=F!1];
 Gmod:=quo<F|RP>;
 pi:=hom<G->Gmod|[Gmod.i: i in [1..#Generators(Gmod)]]>;
 V`GNonsimplifiedPro:=Gmod;
 V`GNonsimplifiedToProHom:=pi;
 Hmod,hmod:=Simplify(Gmod);
 pinew:=hom<H->Hmod|[pi(h(H.i)) @@ hmod: i in [1..#Generators(H)]]>;
 V`GSimplifiedPro:=Hmod;
 V`GNonsimplifiedProToSimplifiedProHom:=hmod;
 V`GSimplifiedToProHom:=pinew;

 //We now compute for each element in one of the finite stabilizers a preimage in the FPgrp
 StabsToG:=[**];
 for cur in [1..#FPStabs] do 
  offset:=cur eq 1 select #Gen else #Gen+&+[#Generators(FPStabs[i]): i in [1..cur-1]];
  for x in Stabs[cur] do
   w:=x @@FPStabsHom[cur];
   w:=Eltseq(w);
   w:=[t gt 0 select t + offset else t-offset: t in w];
   //g(G!w) eq x;
   Append(~StabsToG,<x,G!w>);
  end for;
 end for;

 V`StabilizerPreimages:=StabsToG;
 V`Presentation:=true;
 return Presentation(V:projective:=projective,simplify:=simplify);

end intrinsic;
 
