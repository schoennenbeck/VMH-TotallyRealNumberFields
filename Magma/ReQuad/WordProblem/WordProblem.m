import "../../BasicData.m": K,L;
import "../../Initialize.m": n,BBsym,LReg,dimsym,deg,C;

ERank:=dimsym-2;
FRank:=dimsym-1;

intrinsic ComputeBarycenters(V::VData)
 {Compute and save the attribute Barycenters in V.}
 BZ:=[];
 PL:=V`PerfectList;
 for i in [1..#PL] do
  M:=MinimalVectors(PL[i]);
  b:=1/#M * &+[(x*Dagger(x))/Trace(Trace(x*Dagger(x))) : x in M];
  Append(~BZ,b);
 end for;
 V`Barycenters:=BZ;
end intrinsic;

intrinsic ComputeEdges(V::VData)
 {Compute and save the attribute Edges in V.}
 if not assigned V`Barycenters then ComputeBarycenters(V); end if;
 Edges:=[* *];
 FL:=V`FacesList;
 PL:=V`PerfectList;
 for i in [1..#FL] do
  edges:=[* *];
  F:=FL[i];
  for j in [1..#F] do
   for k in [j+1..#F] do
    s:=SetToSequence(F[j] meet F[k]);
    M:=MinimalVectors(PL[i]);
    s:=[M[x] : x in s];
    sproj:=[x*Dagger(x): x in s];
    sproj:=[x/Trace(Trace(x)): x in sproj];
    
    if #sproj ne 0 and PerfectionRankDAList(s) eq ERank then
     Append(~edges,sproj);
    end if;
   end for;
  end for;
  Append(~Edges,edges);
 end for;
 V`Edges:=Edges;
end intrinsic;

intrinsic ComputeStabilizers(V::VData)
 {Compute and assign the attribute Stabilizers to V.}
 temp:=[ [x : x in AutomorphismGroup(P:CheckMembership:=V`CheckMembership)] : P in V`PerfectList ];
 V`Stabilizers:=&cat temp;
end intrinsic;

intrinsic ComputePolytopeVectors(V::VData)
 {Computes a list of vectors in the symmetric space such that for each facet of the Voronoi domain of each perfect form in PerfectList the facet is given by a system of inequalities involving the scalar products on these vectors. Consider this an internal procedure.}
 if not assigned V`Edges then ComputeEdges(V); end if;
 if not assigned V`Stabilizers then ComputeStabilizers(V); end if;
 PV:=[];
 PL:=V`PerfectList;
 FL:=V`FacesList;
 EL:=V`Edges;
 for i in [1..#PL] do
  PV[i]:=[];
  Mi:=MinimalVectors(PL[i]);
  for j in [1..#FL[i]] do
   temp:=[];
   SFace:={(Mi[x]*Dagger(Mi[x]))/Trace(Trace(Mi[x]*Dagger(Mi[x]))) : x in FL[i][j]};
   FB:=1/#SFace*&+SFace; //Barycenter of the face
   edgestemp:=[e : e in EL[i] | SequenceToSet(e) subset SFace];
   faceperp:=FindPerp(Setseq(SFace));
   edgestemp:=[e cat [faceperp] : e in edgestemp];
   temp:=[FindPerp(e) : e in edgestemp];
   for x in [1..#temp] do
    vz:=Sign(MyInnerProduct(temp[x],FB));
    temp[x]:=vz*temp[x];
   end for;
   Append(~PV[i],temp);
  end for;
 end for;
 V`PolytopeVectors:=PV;
end intrinsic;

intrinsic GeodesicIntersection(M1::Mtrx,M2::Mtrx,Face::Any,V::VData : ReturnSolution:=false,careful:=false) -> BoolElt
 {Checks if the geodesic from M1 to M2 intersects the face "Face" given as a pair [i,j] corresponding to the j-th face of the i-th perfect form. This function returns 0 if the geodesic does not intersect the face, 1 if it intersects the relative interior of the face and 2 if it intersects the boundary of the face (this is only checked if the optional parameter careful is true).}
 M1:=M1/Trace(Trace(M1));
 M2:=M2/Trace(Trace(M2));
 i:=Face[1];
 j:=Face[2];
 M:=MinimalVectors(V`PerfectList[i]);
 F:=[M[k]*Dagger(M[k]): k in V`FacesList[i][j]];
 F:=[x/Trace(Trace(x)): x in F];
 GeodesicGens:=[SymmetricCoordinates(M1),SymmetricCoordinates(M2)];
 FaceGens:=[SymmetricCoordinates(x): x in F];
 GG:=Polytope(GeodesicGens);
 FF:=Polytope(FaceGens);
 if #Vertices(GG meet FF) eq 0 then
  return 0,0;
 end if;

 Vert:=Vertices(GG meet FF)[1];
 if careful then
  for fac in Facets(FF) do
   if Vert in fac then
    return 2,SymmetricCoordinatesToMatrix(Eltseq(Vert));
   end if;
  end for;
 end if;
 
 return 1,SymmetricCoordinatesToMatrix(Eltseq(Vert));
end intrinsic;

intrinsic ConstructWord(x::Mtrx,V::VData) -> SeqEnum
 {Other method.}
 if not assigned V`Barycenters then ComputeBarycenters(V); end if;
 if not assigned V`Stabilizers then ComputeStabilizers(V); end if;
 if not assigned V`PolytopeVectors then ComputePolytopeVectors(V); end if;
 Barycenters:=V`Barycenters;
 Stabs:=V`Stabilizers;
 FL:=V`FacesList;
 FacVec:=V`FacetVectors;
 FTL:=V`FaceTrafoList;
 NL:=V`NeighbourList;
 OKGens:=V`MultFreeList;
 One:=Parent(x)!1;
 B1:=Barycenters[1];
 B:=B1;
 B2:=x^-1*B1*Transpose(x^-1);
 cur:=1; //current index
 Word:=[];
 found:=true;
 count:=0;
 while not x in Stabs and found do
  found:=false;
  for j in [1..#FL[cur]] do
   a,b:=GeodesicIntersection(B1,B2,[cur,j],V : ReturnSolution:=true, careful:=true); 
   if a eq 0 then continue; end if;
   if a eq 2 then
    //this is the case in which the geodesic intersects an edge of the fundamental domain
    if count ne 0 then //We try starting from the barycenter instead of from the point we entered through.
     B1:=V`Barycenters[cur];
     found:=true;
     count:=0;
     break j;
    else
     B1/:=Trace(Trace(B1));
     B1:=(1/2)*(B1+b);
     B1pert:=B1;
     interior:=false;
     N:=1;
     while not interior do
      N*:=1/10;
      randoms:=[1/Random([N,2*N] cat [-2*N,N]) : i in [1..dimsym]];
      B1pert+:=&+[randoms[i]*BBsym[i]: i in [1..dimsym]];
      B1pert/:=Trace(Trace(B1pert));
      interior:=&and [MyInnerProduct(B1pert,FacVec[cur][j]) gt 0 : j in [1..#FL[cur]]];
      if not interior then
       B1pert:=B1;
      else
       B1:=B1pert;
      end if;
     end while; 
     found:=true; break j; //check all faces again
    end if;
   end if;
   if a eq 1 and b ne B1/Trace(Trace(B1)) then
    found:=true;
    g:=FTL[cur][j];
    cur:=NL[cur][j];
    x:=x*g;
    if g ne One then 
     p:=0; e:=0;
     if g in OKGens then p:=Position(OKGens,g); e:=1; end if;
     Append(~Word,[p,e]);
    end if;
    B1:=g^-1*b*Transpose(g^-1);
    B2:=g^-1*B2*Transpose(g^-1);
    break;
   end if;
  end for;
  count:=count+1;
 end while;
 Append(~Word,[0,Position(Stabs,x)]);
 //At this point the output is to be read as follows:
 //x*w[1]^exp[1]*w[2]^exp[2]*....*w[r]^exp[r] = Stabs[l]
 //The stabilizer element is found in the last entry of the list "Word".

 //For convenience, we change this, so that now we have x=s*w[2]^exp[2]*...*w[r]^exp[r] and s is the stabilizer element, which is now found in the first entry
 temp:=[ Word[#Word] ];
 for i in [1..#Word-1] do
  Word[#Word-i][2]*:=-1;
  Append(~temp,Word[#Word-i]);
 end for;
 Word:=temp;
 return found,Word,x;
end intrinsic;




intrinsic SolveWordProblem(x::Mtrx,V::VData)->GrpFpElt
 {}
 found,Word,xx:=ConstructWord(x,V);
 if not found then
  error "This element does not belong to the computed group";
 end if;
 
 G,mathom:=Presentation(V);
 simpl:=V`GNonsimplifiedToSimplifiedHom;
 Gnon:=V`GNonsimplified;
 res:=G!1;
 for i in [2..#Word] do
  res:=res*simpl(Gnon.Word[i][1]^Word[i][2]);
 end for;

 s:=V`Stabilizers[Word[1][2]];
 pos:=Position([P[1]: P in V`StabilizerPreimages],s);
 res:=simpl(V`StabilizerPreimages[pos][2])*res;
 assert V`GSimplifiedHom(res) eq x;
 
 return res;
end intrinsic;
