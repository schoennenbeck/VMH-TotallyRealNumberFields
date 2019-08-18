import "../../BasicData.m": K,L,V;
import "../../Initialize.m": n,BBsym,LReg,dimsym,deg,C;


limit:=3;

/**********************************************************/

OrbitReps:=function(G,L);
a:=#L;
OO:=[**];
O:=[];
S:=[];

b:=0;
for i in [1..#L] do 
  neu:=true;
  elt:=L[i];
  for oo in OO do if elt in oo then neu:=false; break; end if; end for;
  if neu then 
  Append(~O,i);
  o:=Orbit(G,L[i]);
  s:=Stabiliser(G,L[i]);
   // t = OrbitRepresentatives von s auf L 
     		OOs:=[**];
		Os:=[];
		bs:=0;
		for ts in [1..#L] do
  		neus:=true;
  		elts:=L[ts];
  		for oos in OOs do 
                   if elts in oos then neus:=false; break; end if; 
                end for;
  		if neus then
  		Append(~Os,ts);
  		os:=Orbit(s,L[ts]);
  		Append(~OOs,os); 
  		bs +:= #os;
  		if bs eq a then break; end if;
  		end if;
                end for; // ts
  Append(~S,Os);
  Append(~OO,o); 
  b +:= #o;
  if b eq a then return O,S; end if;
  end if;
end for;
print [a,b];
return O,S;
end function;


/**********************************************************/

intrinsic CanonicalFormOfMinimalClass(A::DAForm) -> DAForm
 {}
 if assigned A`CanonicalFormMinimalClass then return A`CanonicalFormMinimalClass; end if;
 S:=MinimalVectors(A);
 A`CanonicalFormMinimalClass:=NewDAForm(&+[s*Dagger(s) : s in S]);
 return A`CanonicalFormMinimalClass;
end intrinsic;

intrinsic AreEquivalentMinimalClasses(A::DAForm,B::DAForm) -> Any
 {}
 AA:=CanonicalFormOfMinimalClass(A);
 BB:=CanonicalFormOfMinimalClass(B);
 return TestIsometry(NewDAForm(AA`Matrix^-1),NewDAForm(BB`Matrix^-1));
end intrinsic;

intrinsic IsWellRounded(A::DAForm) -> Any
 {}
 S:=MinimalVectors(A);
 //V:=KMatrixSpace(K,1,n);
 U:=sub<V|[V!x : x in S]>;
 return Dimension(U) eq n;
end intrinsic;

intrinsic StabilizerOfMinimalClass(A::DAForm) -> DAForm
 {}
 return AutomorphismGroup(NewDAForm((CanonicalFormOfMinimalClass(A)`Matrix)^-1));
end intrinsic;

intrinsic MinimalClasses(V::VData) 
 {Computes a system of representatives of the minimal classes in the Voronoi-tesselation corresponding to V.}

 //faceneu:=V`faceneu;


perfectlist:=V`PerfectList;
facelist:=V`FacesList;
facevectList:=V`FacetVectors;
CriticalValueList:=V`CriticalValueList;


FaceTupleList:=[**];                           //This will contain the tuples of faces of codim>1
Representatives:=[* [p : p in perfectlist] *];            //Representatives of all minimal classes
FaceTupleListOfRepresentatives:=[* [] *];      //We need this to check the dimension of the intersection

print "Starting the computation of minimal classes. Please be patient.";

//n=2



 //Generate the tuples
 for i in [1..#perfectlist] do
  FaceTuples:=[**];
  S:=MinimalVectors(perfectlist[i]);
  for j in [1..#facelist[i]] do
   for k in [j+1..#facelist[i]] do
    Intersection:=facelist[i][j] meet facelist[i][k];
    if #Intersection gt 1 then
     if #FindAllPerp([S[l]*Dagger(S[l]) : l in Intersection]) eq 2 then
      Append(~FaceTuples,[j,k]);
      if k gt #facelist[i] then print "Error."; end if;
     end if;
    end if;
   end for;
  end for;
  Append(~FaceTupleList,FaceTuples);
 end for;
 FaceTupleList:= [* FaceTupleList *];       //This is a bit clumsy; now FTL[1] is the data for codim 2

 
 codim:=3;
 while dimsym-codim ge 1 do
  print "Now doing it for Codim " cat IntegerToString(codim);
  FaceTuplesInCodim:=[**];
  for i in [1..#perfectlist] do
   FaceTuples:=[**];
   S:=MinimalVectors(perfectlist[i]);
   for j in [1..#FaceTupleList[codim-2][i]] do
    Intersection:=facelist[i][FaceTupleList[codim-2][i][j][1]];
    for l in FaceTupleList[codim-2][i][j] do
     Intersection:=facelist[i][l] meet Intersection;
    end for;
    for k in [1..#facelist[i]] do
     IntersectionTemp:=facelist[i][k] meet Intersection;
     if #IntersectionTemp gt 1 then
      if #FindAllPerp([S[l]*Dagger(S[l]) : l in IntersectionTemp]) eq codim then
       LL:=FaceTupleList[codim-2][i][j];
       Append(~LL,k);
       Append(~FaceTuples, LL  );
      end if;
     end if;
    end for;
   end for;
   Append(~FaceTuplesInCodim,FaceTuples);
  end for;
  Append(~FaceTupleList,FaceTuplesInCodim);
  codim:=codim+1;
 end while; 

//Compute corank 1 classes:

 TempList:=[**];
 for i in [1..#perfectlist] do
  for j in [1..#CriticalValueList[i]] do
   Append(~TempList , NewDAForm(perfectlist[i]`Matrix+(CriticalValueList[i][j]/2)*facevectList[i][j]) );
  end for;
 end for;

 MinClassReps:=[TempList[1]];
 for x in TempList do
  isi:=false;
  for y in MinClassReps do
   if AreEquivalentMinimalClasses(x,y) then
    isi:=true;
   end if;
  end for;
  if not isi then
   Append(~MinClassReps,x);
  end if;
 end for;
  //Test: append herm forms
 Append(~Representatives,MinClassReps);
 print "Corank 1 done.";

 //Compute classes of corank >= 2

 codim:=2;

 while dimsym-codim ge 0 do
  TempList:=[**];
  for i in [1..#perfectlist] do
   for j in [1..#FaceTupleList[codim-1][i]] do
    T:=MatrixRing(K,n)!perfectlist[i]`Matrix;
    for k in FaceTupleList[codim-1][i][j] do
     T:=T+(CriticalValueList[i][k]/(2*codim))*facevectList[i][k];
    end for;
    T:=NewDAForm(T);
    if IsWellRounded(T) then 
     Append(~TempList,T);
    end if;
   end for;
  end for;
  if #TempList eq 0 then
   break;
  end if;
  MinClassReps:=[TempList[1]];
  for x in TempList do
   isi:=false;
   for y in MinClassReps do
    if AreEquivalentMinimalClasses(x,y) then
     isi:=true;
     break y;
    end if;
   end for;
   if not isi then
    Append(~MinClassReps,x);
   end if;
  end for;
  //Test: Apppend herm forms
  Append(~Representatives,MinClassReps);
  codim:=codim+1;
 end while;





 print "Data assembled.";
 V`FaceTupleList:=FaceTupleList;
 V`MinimalClasses:=Representatives;
end intrinsic;
