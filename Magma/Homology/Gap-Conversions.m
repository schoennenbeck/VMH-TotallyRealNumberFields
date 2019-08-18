import "Functions.m": matbas2;

intrinsic WriteMatrixToGapFormat(File::MonStgElt,M::Mtrx)
 {Writes the Matrix M in gap-readable format to the file specified by the string "File"}
 Write(File,"[");
 for i in [1..NumberOfRows(M)] do
  if i ne 1 then
   Write(File,",");
  end if;
  Write(File,"[");
  for j in [1..NumberOfColumns(M)] do
   if j eq 1 then	
    Write(File,M[i][j]);
   else 
    Write(File,",");
    Write(File,M[i][j]);
   end if;
  end for;
  Write(File,"]");
 end for;
 Write(File,"]");
end intrinsic;

intrinsic MatrixToGapString(M::Mtrx)->MonStgElt
 {...}
 M:=ChangeRing(M,Rationals());
 str:="";
 str cat:= "[";
 for i in [1..NumberOfRows(M)] do
  if i ne 1 then
   str cat:= ",";
  end if;
  str cat:="[";
  for j in [1..NumberOfColumns(M)] do
   if j eq 1 then	
    str cat:= Sprint(M[i][j]);
   else 
    str cat:= "," ;
    str cat:= Sprint(M[i][j]);
   end if;
  end for;
  str cat:= "]";
 end for;
 str cat:= "]";
 return str;
end intrinsic;

intrinsic WriteBoundaryComponentsToGapFormat(File::MonStgElt,B::List,Elts::List)
 {Writes the boundary components from the list "B" to the file "File" in the format expected by HAP and corresponding to the list of elements "Elts"}
 B:=[*[*[*[B[i][j][k][1],Position(Elts,RegRepMat([B[i][j][k][2]])[1])]:k in [1..#B[i][j]]*]:j in [1..#B[i]]*]:i in [1..#B]*]; 
 Write(File,"BoundaryComponent:=[");
 for i in [1..#B] do
  if i ne 1 then
   Write(File,",");
  end if;
  Write(File,"[");
  for j in [1..#B[i]] do
   if j ne 1 then
    Write(File,",");
   end if;
   Write(File,"[");
   for k in [1..#B[i][j]] do
    if k ne 1 then
     Write(File,",");
    end if;
    Write(File,"[");
    Write(File,B[i][j][k][1]);
    Write(File,",");
    Write(File,B[i][j][k][2]);
    Write(File,"]");
   end for;
   Write(File,"]");
  end for;
  Write(File,"]");
 end for;
 Write(File,"];");
end intrinsic;

intrinsic BoundaryComponentsToGapString(B::List,Elts::List) -> MonStgElt
 {}
 str:="";
 B:=[*[*[*[B[i][j][k][1],Position(Elts,RegRepMat(B[i][j][k][2]))]:k in [1..#B[i][j]]*]:j in [1..#B[i]]*]:i in [1..#B]*]; 
 str cat:= "BoundaryComponent:=[";
 for i in [1..#B] do
  if i ne 1 then
   str cat:= ",";
  end if;
  str cat:= "[";
  for j in [1..#B[i]] do
   if j ne 1 then
    str cat:= ",";
   end if;
   str cat:= "[";
   for k in [1..#B[i][j]] do
    if k ne 1 then
     str cat:= ",";
    end if;
    str cat:= "[";
    str cat:= Sprint(B[i][j][k][1]);
    str cat:= ",";
    str cat:= Sprint(B[i][j][k][2]);
    str cat:= "]";
   end for;
   str cat:= "]";
  end for;
  str cat:= "]";
 end for;
 str cat:= "];";
 return str;
end intrinsic;

intrinsic WriteElementsToGapFormat(File::MonStgElt,Elts::Any)
 {Writes the element list in Gap-readable format}
 Write(File,"elts:=[");
 for i in [1..#Elts] do
  if i ne 1 then
  Write(File,",");
  end if;
  WriteMatrixToGapFormat(File,Elts[i]);
 end for;
 Write(File,"];");
end intrinsic;

intrinsic ElementsToGapString(Elts::Any)-> MonStgElt
 {...}
 str:="";
 str cat:= "elts:=[";
 for i in [1..#Elts] do
  if i ne 1 then
  str cat:= ",";
  end if;
  str cat:= MatrixToGapString(Elts[i]);
 end for;
 str cat:= "];";
 return str;
end intrinsic;

intrinsic WriteStabilizersToGapFormat(File::MonStgElt,Stabs::List,booleven::BoolElt)
 {booleven specifies whether the full stabilizer or only the orientation preserving stabilizer will be printed}
 if booleven then
  Write(File,"evenstabilizers:=[");
 else
  Write(File,"stabilizers:=[");
 end if;
 for i in [1..#Stabs] do
  if i ne 1 then
   Write(File,",");
  end if;
  Write(File,"[");
  for j in [1..#Stabs[i]] do
   if j ne 1 then
    Write(File,",");
   end if;
   Write(File,"[");
   z:=true;
   for x in Stabs[i][j] do
    if not z then
     Write(File,",");
    end if;
    WriteMatrixToGapFormat(File,x);
    z:=false;
   end for;
   Write(File,"]");
  end for;
  Write(File,"]");
 end for;
 Write(File,"];");
end intrinsic;

intrinsic StabilizersToGapString(Stabs::Any,booleven::BoolElt)-> MonStgElt
 {...}
 str:="";
 if booleven then
  str cat:= "evenstabilizers:=[";
 else
  str cat:= "stabilizers:=[";
 end if;
 for i in [1..#Stabs] do
  if i ne 1 then
   str cat:= ",";
  end if;
  str cat:= "[";
  for j in [1..#Stabs[i]] do
   if j ne 1 then
    str cat:= ",";
   end if;
   str cat:= "[";
   z:=true;
   for x in Stabs[i][j] do
    if not z then
     str cat:= ",";
    end if;
    str cat:= MatrixToGapString(x);
    z:=false;
   end for;
   str cat:= "]";
  end for;
  str cat:= "]";
 end for;
 str cat:= "];";
 return str;
end intrinsic;

intrinsic WriteDimensionsToGapFormat(File::MonStgElt,Dims::SeqEnum)
 {...}
 Write(File,"DIMS:=[");
  for i in [1..#Dims] do
   if i ne 1 then 
    Write(File,",");
   end if;
   Write(File,Dims[i]);
  end for;
 Write(File,"];");
end intrinsic;

intrinsic DimensionsToGapString(Dims::SeqEnum)-> MonStgElt
 {...}
 str:="";
 str cat:= "DIMS:=[";
  for i in [1..#Dims] do
   if i ne 1 then 
    str cat:= ",";
   end if;
   str cat:= Sprint(Dims[i]);
  end for;
 str cat:= "];";
 return str;
end intrinsic;

intrinsic WriteGeneratorsToGapFormat(File::MonStgElt,Gens::SeqEnum)
 {...}
 Write(File,"Gens:=[");
 for i in [1..#Gens] do
  if i ne 1 then
   Write(File,",");
  end if;
  WriteMatrixToGapFormat(File,Gens[i]);
 end for;
 Write(File,"];");
end intrinsic;

intrinsic GeneratorsToGapString(Gens::SeqEnum) -> MonStgElt
 {...}
 str:="";
 str cat:= "Gens:=[";
 for i in [1..#Gens] do
  if i ne 1 then
   str cat:= ",";
  end if;
  str cat:= MatrixToGapString(Gens[i]);
 end for;
 str cat:= "];";
 return str;
end intrinsic;


