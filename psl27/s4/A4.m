(* ::Package:: *)

(* CGC of A4 group *)
LoadPackage[file_]:= Get[FileNameJoin[{DirectoryName[$InputFileName],file}]];
LoadPackage["../../cgframework.m"];

ClearAll[A4Group]
A4Group[KeyIrr]:={{"1_0",1},{"1_1",1},{"1_2",1},{"3",3}};
A4Kronecker[x_,y_]:=DefaultKronecker[A4Group,x,y];
A4Kronecker["1_1","1_1"]:={"1_2"};
A4Kronecker["1_1","1_2"]:={"1_0"};
A4Kronecker["1_1","3"]:={"3"};
A4Kronecker["3","3"]:={"1_0","1_1","1_2", "3:+","3:-"};
A4Group[KeyKronecker]:=A4Kronecker;
A4Group[KeyConjugateIrr]:={{"1_1","1_2"}};

(* Generators of A4: s^2=t^3=(st)^3=e *)
omega=Exp[I*2Pi/3];
GA4T["1_0"]={{1}};
GA4S["1_0"]={{1}};

GA4T["1_1"]={{omega}};
GA4S["1_1"]={{1}};

GA4T["1_2"]={{omega^2}};
GA4S["1_2"]={{1}};

GA4T["3"]=DiagonalMatrix[{1,omega, omega^2}];
GA4S["3"]=1/3*{{-1,2,2},{2,-1,2},{2,2,-1}};
GammaA4={{1,0,0},{0,0,1},{0,1,0}};

VerifyA4Generators[]:=Module[{i, reps, s, t,st},
	reps={"1_0","1_1","1_2","3"};
	For[i=1,i<= Length[reps],i++,
		s=GA4S[reps[[i]]];
		t=GA4T[reps[[i]]];
		st=s.t;

		(*Print[s.s, ", ", t.t.t, ", ", st.st.st];*)
		Assert[Simplify[s.s]==IdentityMatrix[Length[s]]];
		Assert[Simplify[t.t.t]==IdentityMatrix[Length[s]]];
		Assert[Simplify[st.st.st]==IdentityMatrix[Length[s]]];
	];
];

On[Assert];
VerifyA4Generators[]
Assert[Simplify[GammaA4.Conjugate[GA4T["3"]].GammaA4-GA4T["3"]]==ConstantArray[0,{3,3}]]
Assert[Simplify[GammaA4.Conjugate[GA4S["3"]].GammaA4-GA4S["3"]]==ConstantArray[0,{3,3}]]




(* Clebsch-Gordan Coefficients for A4. *)
ClearAll[CGA4];
CGA4[x_, y_,z_]:={};

CGA4["3","3","1_0"]:={
	1/Sqrt[3]{{1,0,0},{0,0,1},{0,1,0}}
};

CGA4["3","3","1_1"]:={
	1/Sqrt[3]{{0,1,0},{1,0,0},{0,0,1}}
};

CGA4["3","3","1_2"]:={
	1/Sqrt[3]{{0,0,1},{0,1,0},{1,0,0}}
};

CGA4["3","3","3:+"]:={
	1/Sqrt[6]{{2,0,0},{0,0,-1},{0,-1,0}},
	1/Sqrt[6]{{0,-1,0},{-1,0,0},{0,0,2}},
	1/Sqrt[6]{{0,0,-1},{0,2,0},{-1,0,0}}
};

CGA4["3","3","3:-"]:={
	1/Sqrt[2]{{0,0,0},{0,0,1},{0,-1,0}},
	1/Sqrt[2]{{0,1,0},{-1,0,0},{0,0,0}},
	1/Sqrt[2]{{0,0,-1},{0,0,0},{1,0,0}}
};

CGA4["1_1","3","3"]:={
	{{0,0,1}},
	{{1,0,0}},
	{{0,1,0}}
};

CGA4["1_2","3","3"]:={
	{{0,1,0}},
	{{0,0,1}},
	{{1,0,0}}
};

CGA4["1_1","1_2","1_0"]:={
	{{1}}
};

CGA4["1_1","1_1","1_2"]:={
	{{1}}
};

CGA4["1_2","1_2","1_1"]:={
	{{1}}
};

ClearAll[DotA4];
DotA4::NoCGFound="Clebsh Gordan Coefficients not found.";
DotA4[a_,b_,ra_,rb_,rc_]:=Module[{cg,res},
	res=DefaultDotFunction[A4Group, a,b,ra,rb,rc];
	If[Length[res]>0, Return[res]];

	(* find CG. *)
	cg = CGA4[ra,rb,rc];
	If[Length[cg]==0 && ra!=rb,
		(*Print[ra, " ", rb, " ", rc];*)
		cg = CGA4[rb,ra,rc];
		Do[cg[[i]]=Transpose[cg[[i]]],{i,1,Length[cg]}];
	];

	If[Length[cg]==0, Message[DefaultDotFunction::NoCGFound, ra,rb,rc]; Return[$Failed]];
	Return[Table[a.cg[[i]].b, {i,1,Length[cg]}]];
];

ClearAll[VerifyA4CG];
VerifyA4CG[r1_,r2_,r3_]:=Module[{ops,op,d1,d2,d3,rr3,i,v1,v2,v3,v4,x1,y1,z1,x2,y2,z2},
	ops={GA4S,GA4T};
	d1=GetDimensionByRep[A4Group,r1];
	d2=GetDimensionByRep[A4Group,r2];
	d3=GetDimensionByRep[A4Group,r3];
	rr3=GetRepName[r3];
	v1={x1,y1,z1}[[1;;d1]];
	v2={x2,y2,z2}[[1;;d2]];
	v3=DotA4[v1,v2,r1,r2,r3];
	(*Print["v1=",v1, ", v2=", v2, ", v3=",v3, ", rr3=",rr3];*)
	For[i=1,i<= Length[ops],i++,
		op=ops[[i]];
		v4=DotA4[op[r1].v1,op[r2].v2, r1,r2,r3];
		(*Print["v4-v3=",Simplify[v4-op[rr3].v3]];*)
		Assert[Simplify[v4-op[rr3].v3]==ConstantArray[0,d3]];
	];
];

On[Assert];
VerifyA4CG["3","3","3:+"]
VerifyA4CG["3","3","3:-"]
VerifyA4CG["3","3","1_0"]
VerifyA4CG["3","3","1_1"]
VerifyA4CG["3","3","1_2"]
VerifyA4CG["3","1_1","3"]
VerifyA4CG["1_1","3","3"]
VerifyA4CG["3","1_2","3"]
VerifyA4CG["1_1","1_2","1_0"]
VerifyA4CG["1_1","1_1","1_2"]
VerifyA4CG["1_2","1_2","1_1"]

A4Group[KeyDotFunction]:=DotA4;
Assert[VerifyGroupInfo[A4Group,VerifyDotFunction->True]]
ClearAll[tmp1,tmp2,rtmp1,s3,t3,s11,t11];

