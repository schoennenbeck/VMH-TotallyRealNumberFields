import "../../BasicData.m": K,L;
import "../../Initialize.m": n,BBsym,LReg,dimsym,deg,C;


filestring:=IntegerToString(Floor(Realtime()));

intrinsic VoronoiAlgorithm(:quiet:=false,SL:=false,CheckMembership:=0) -> SeqEnum
 {This runs the Voronoi algorithm.}
 //Find a first perfect form
 Pini:=NewDAForm(MatrixRing(K,n)!1);
 
 Sini:=MinimalVectors(Pini);
 Rini:=PerfectionRank(Pini);
 min:=FormMinimum(Pini);

 count:=1;

 while Rini lt dimsym and count lt 100 do
  count:=count+1;
  dir:=FindPerp([x*Dagger(x): x in Sini]);
  tsup:=10000;
  tinf:=0;
  t:=(tsup+tinf)/2;
  bool:=false;
  count2:=1;

  while not bool and count2 lt 400 do
   count2:=count2+1;
   M:=min;
   Pt:=NewDAForm(Pini`Matrix+t*dir);
   while M eq min do
    if IsPositiveForm(Pt) then
     M:=FormMinimum(Pt);
     if M eq min then
      tinf:=t;
      t:=(tinf+tsup)/2;
      Pt:=NewDAForm(Pini`Matrix+t*dir);
     end if;
    else
     tsup:=t;
     t:=(tinf+tsup)/2;
     Pt:=NewDAForm(Pini`Matrix+t*dir);
    end if;
   end while;
   St:=MinimalVectors(Pt);
   St:=[v : v in St | not (v in Sini or -v in Sini)];

   ll:=[(min-Evaluate(Pini`Matrix,v))/Evaluate(dir,v) : v in St];
   ttr:=Min(ll);
   pos:=Position(ll,Min(ll));
   tt:=( (min-Evaluate(Pini`Matrix,St[pos]))/Evaluate(dir,St[pos]) );

   bool:=false;
   if tt lt t and tt gt 0 then
    Pc:=NewDAForm(Pini`Matrix+tt*dir);
    M:=FormMinimum(Pc);
    if M eq min then
     bool:=true;
    else
     tsup:=tt;
     t:=(tinf+tsup)/2;
     Pt:=NewDAForm(Pini`Matrix+t*dir);
    end if;
   else
    tsup:=t;
    t:=(tsup+tinf)/2;
    Pt:=NewDAForm(Pini`Matrix+t*dir);
   end if;
  end while;
  Pini:=Pc;
  Sini:=MinimalVectors(Pini);
  Rini:=PerfectionRank(Pini);
 end while;

 //Enumerate perfect neighbours in order to obtain a set of representatives
 //of perfect forms

 perfectlist:=[Pini];         //List of representatives of perfect forms
 vectlist:=[**];              //List of shortest vectors of perfect forms
 facelist:=[**];              //List of facets of V-domains of p. forms; given by shortest vectors
 faceneu:=[**];               //1 at [i][j] if neighbor(facelist[i][j]) >= i
                              //0 else
 facevectList:=[**];          //Perpendicular form to shortest vectors defining the respective facet
 FaceFormList:=[**];          //List of forms defined by those shortest vectors, which define the respective facet
 AutList:=[**];               //List of Aut-Groups of the inverse FaceForms

 numberoffaces:=[];           //List of number of faces of V-domains of p. forms
 E:={**};                     //multiset encoding the Voronoi graph of perfect forms
 Todo:=[Pini];                //List of perfect forms to be treated with Voronoi algorithm
 PerfectNeighbourList:=[**];  //List of perfect neighbours of all (mod GL) perfect forms

 CriticalValueList:=[**];     //List of critical rho values (from Voronoi's algorithm)
 FacetVectorList:=[**];       //List of facet vectors (from Voronoi's algorithm)

 FaceTrafoList:=[**];
 NeighbourList:=[**];

 minvecss:=[MinimalVectors(Pini)];

 while(#Todo gt 0) do
  P:=Todo[1];
  m:=FormMinimum(P);
  Sk:=MinimalVectors(P);
  Sproj:=[v*Dagger(v) : v in Sk];
  
  Co:=[SymmetricCoordinates(x/Trace(Trace(x))) : x in Sproj];
  Append(~vectlist,Sk);

  Exclude(~Todo,Todo[1]);
  if not quiet then
   print "Still " cat IntegerToString(#Todo+1) cat " forms to treat. I have found " cat IntegerToString(#perfectlist) cat " perfect forms.";
  end if;

  GeneratorsOfPolytope:=[[Rationals()!0 : i in [1..dimsym]]] cat Co;
  //return GeneratorsOfPolytope;
  //print "Generators of Polytope constructed. Number of generators: " cat IntegerToString(#GeneratorsOfPolytope);
  Poly:=Polytope(GeneratorsOfPolytope);
  //print "Polytope constructed.";
  Faces:=FacetIndices(Poly);
  //print "Faces calculated.";
  Faces:=[Exclude(x,1) : x in Faces | 1 in x];
  Vert:=Vertices(Poly);
  Faces:=[[Position(GeneratorsOfPolytope,Eltseq(Vert[i])): i in F ]: F in Faces];
  
  Faces:=[[x-1: x in y]: y in Faces];
  Append(~facelist,[Seqset(x): x in Faces]);  
  
  count:=0;
 
  PerfectNeighbours:=[**];    //List of perfect neighbours of P being treated
  CriticalValues:=[**];       //List of critical rho-values of P
  fneu:=[];		      //List of "new faces" (for optimization of min.cl.calculation)
  if not quiet then print "I am now treating a Voronoi domain which has " cat IntegerToString(#Faces) cat " faces."; end if;
  FaceTrafos:=[**];
  NList:=[**];
  facetvectors:=[**];
  nof:=0;                     //Number of faces for this form
  while(#Faces gt 0) do
   isface:=IsFace([Sk[n] : n in Faces[1]]);
   //print isface;
   if isface then
    F1:=ChangeRing(FindPerp([Sproj[n] : n in Faces[1]]),K); 
    sgns:=[Evaluate(F1,x) : x in Sk];
    for x in sgns do 
     if x gt 0 then sgn := 1; break; end if; 
     if x lt 0 then sgn := -1; break; end if; 
    end for;
    for i in [1..#sgns] do
     if sgn*sgns[i] lt 0 or (sgn*sgns[i] lt 0 and not i in Faces[1]) then
      isface:=false;
      break;
     end if;
    end for; 
    F1:=sgn*F1;
   end if;
   count:=count+1;
   if isface then Append(~facetvectors,F1); end if;
   Exclude(~Faces,Faces[1]);
   //sgn:=Sign(&+ [Evaluate(F1,x) : x in Sk]);
   //F1:=sgn*F1;  

   if isface then
    nof+:=1;
    tsup:=1000000;
    tinf:=0;
    t:=(tinf+tsup)/2;
    minimcont:=0;
    while minimcont ne min do
     coherent:=false;
     while not coherent do
      Pt:=NewDAForm(P`Matrix+t*F1);
      M:=min;
      while M eq min do
       if IsPositiveForm(Pt) then
        M:=FormMinimum(Pt);
        if M eq min then
         tinf:=t;
         t:=(tinf+tsup)/2;
         Pt:=NewDAForm(P`Matrix+t*F1); 
        end if;
       else
        tsup:=t;
        t:=(tinf+tsup)/2;
        Pt:=NewDAForm(P`Matrix+t*F1);
       end if;
      end while;
      St:=MinimalVectors(Pt);
      SFace:=[ s : s in Sk | Evaluate(F1,s) eq 0];
      SS:=SFace cat St;
      Cond:=KMatrixSpace(Rationals(),#BBsym,#SS) ! 0;
      for i in [1..#BBsym] do
       for j in [1..#SS] do
        Cond[i][j]:=Evaluate(BBsym[i],SS[j]);
       end for;
      end for;
      Uns:=&cat [[min] : i in [1..#SS]];
      Uns:=Vector(Uns);
    
  
      coherent:=IsConsistent(Cond,Uns);
      if not coherent then
       tsup:=t;
       t:=(tinf+tsup)/2;
       Pt:=NewDAForm(P`Matrix+t*F1);
      end if;
     end while; 

     Pcont:=NewDAForm(SymmetricCoordinatesToMatrix(Eltseq(Solution(Cond,Uns))));  

     Scontk:=MinimalVectors(Pcont);
 
     minimcont:=FormMinimum(Pcont);
 
     tsup:=t;
     t:=(tinf+tsup)/2;
     Pt:=NewDAForm(P`Matrix+t*F1);
    end while;
 
    Append(~PerfectNeighbours,Pcont);
    critF1:=Pcont`Matrix-P`Matrix;
    for pos in [1..#Eltseq(critF1)] do
     if Eltseq(critF1)[pos] ne 0 then
      crit:=Eltseq(critF1)[pos]/Eltseq(F1)[pos];
      break pos;
     end if;
    end for;
    Append(~CriticalValues,crit);

    iso:=false;
    jjj := Position(perfectlist,P);
    for i in [1..#perfectlist] do
     bool,trans:=TestIsometry(Pcont,perfectlist[i]:SL:=SL,CheckMembership:=CheckMembership);     
     if bool then
      Include(~E,<jjj,i>);
      if jjj  le i then Append(~fneu,1); else Append(~fneu,0); end if;
      Append(~NList,i);
      break i;
     end if;
    end for;
    if not bool then
     Append(~perfectlist,Pcont);
     Append(~minvecss,MinimalVectors(Pcont));
     Append(~fneu,1);
     Append(~Todo,Pcont);
     Include(~E,<Position(perfectlist,P),Position(perfectlist,Pcont)>);
     Append(~FaceTrafos,MatrixRing(K,n)!1);
     Append(~NList,#perfectlist);
    else
     Append(~FaceTrafos,trans);
    end if;
   end if;
  end while;
  Append(~numberoffaces,nof);
  Append(~faceneu,fneu);
  Append(~PerfectNeighbourList,PerfectNeighbours);
  Append(~CriticalValueList,CriticalValues);
  Append(~FaceTrafoList,FaceTrafos);
  Append(~NeighbourList,NList);
  Append(~FacetVectorList,facetvectors);
 end while;
 
 V:=New(VData);
 V`Context:="DivAlg";
 V`PerfectList:=perfectlist;
 V`PerfectNeighbourList:=PerfectNeighbourList;
 V`FacesList:=facelist;
 V`FaceTrafoList:=FaceTrafoList;
 V`NeighbourList:=NeighbourList;
 V`PerfectNeighbourList:=PerfectNeighbourList;
 OKGens:=[];
 MultFreeList:=[];
 for i in [1..#perfectlist] do
  OKGens:=OKGens cat [MatrixRing(K,n)!x : x in AutomorphismGroup(P:CheckMembership:=CheckMembership)];
  OKGens:=OKGens cat [MatrixRing(K,n)!x : x in FaceTrafoList[i]];
  MultFreeList cat:= [MatrixRing(K,n)!x : x in FaceTrafoList[i]];
 end for;
 MultFreeList:=SetToSequence(SequenceToSet(MultFreeList));
 Exclude(~MultFreeList,MatrixRing(K,n)!1);
 V`MultFreeList:=MultFreeList;
 V`OKGens:=OKGens;
 V`FacetVectors:=FacetVectorList;
 V`CriticalValueList:=CriticalValueList;
 V`CheckMembership:=CheckMembership;

 if not quiet then print "Voronoi data assembled."; end if;
 return V;
end intrinsic;

















