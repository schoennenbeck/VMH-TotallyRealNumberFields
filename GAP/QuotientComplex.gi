QuotientComplex:=
function(C,S)
local
        Elts,G,Stabilizer,Action,D;

SetInfoLevel(InfoWarning,0);
D:=List(Elements(S),x->x);
Elts:=List(C!.elts, x->QuotientGroup(x,D));
G:=Group(Elts);
#Action:=function(a,b,c) return 1; end;

#####################
Action:=function(n,k,g)
local gg;
gg:=Position(C!.elts,Elts[g]!.element[1]);
	if gg=fail then
		Add(C!.elts,Elts[g]!.element[1]);
		gg:=Length(C!.elts);
	fi;
return C!.action(n,k,gg);
end;
#####################

#####################
Stabilizer:=function(n,i);
return 
Group(List(Elements(C!.stabilizer(n,i)),x->QuotientGroup(x,D)));
end;
#####################

SetInfoLevel(InfoWarning,1);

return Objectify(HapNonFreeResolution,
            rec(
            dimension:=C!.dimension,
            boundary:=C!.boundary,
            homotopy:=fail,
            elts:=Elts,
            group:=G,
            stabilizer:=Stabilizer,
            action:=Action,
            properties:=
            [["length",EvaluateProperty(C,"length")],
             ["characteristic",0],
             ["type","resolution"],
             ["reduced",C!.dimension(0)=1]]  ));

end;
