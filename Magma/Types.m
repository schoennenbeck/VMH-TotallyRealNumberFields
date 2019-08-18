declare type VData;
declare attributes VData: Context,PerfectList,FacesList,MinimalClasses,FaceTupleList,faceneu, FaceTrafoList,ZGens,OKGens,CheckMembership,CriticalValueList,NeighbourList,Edges,Barycenters,Stabilizers, n,d , Relations , PerfectNeighbourList , Words , PolytopeVectors, MultFreeList , FacetVectors , Presentation , GSimplified , GSimplifiedHom , GSimplifiedPro , GSimplifiedToProHom , GNonsimplified , GNonsimplifiedHom , GNonsimplifiedPro , GNonsimplifiedToProHom , GNonsimplifiedToSimplifiedHom , GNonsimplifiedProToSimplifiedProHom , StabilizerPreimages;

declare type DAForm;
declare attributes DAForm: Matrix, MinimalVectors, Minimum, PerfectionRank, IsPositive, Aut,CanonicalFormMinimalClass;

intrinsic Print(X::VData)
 {Print procedure for VData.}
 printf "Voronoi Data with " cat IntegerToString(#X`PerfectList) cat " perfect form(s).";
end intrinsic;

intrinsic Print(F::DAForm)
 {Print procedure for DAForm.}
 print F`Matrix;
end intrinsic;

intrinsic NewDAForm(A::Mtrx) -> DAForm
 {Create a new DAForm with input matrix A.}
 require A eq Dagger(A): "The input matrix must be dagger-invariant.";
 F:=New(DAForm);
 F`Matrix:=A;
 return F;
end intrinsic;

intrinsic 'eq'(A::DAForm,B::DAForm) -> BoolElt
 {}
 return A`Matrix eq B`Matrix;
end intrinsic;
