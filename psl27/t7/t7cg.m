(* ::Package:: *)

<<"/users/gaolichen/gitroot/psl27cg/mpackage/cgframework.m";

ClearAll[T7Group];
T7Group[KeyIrr]={{"1",1},{"1p",1,"1^{\\prime}"},{"1pb",1,"\\bar{1}^{\\prime}"},{"3",3},{"3b",3,"\\bar{3}"}};
T7Kronecker[x_,y_]:=DefaultKronecker[T7Group,x,y];
T7Kronecker["1p","1p"]:={"1pb:+"};
T7Kronecker["1p","1pb"]:={"1"};
T7Kronecker["1p","3"]:={"3"};
T7Kronecker["1p","3b"]:={"3b"};
T7Kronecker["3","3"]:={"3:+","3b:+","3b:-"};
T7Kronecker["3","3b"]:={"3","3b","1","1p","1pb"};
T7Group[KeyKronecker]:=T7Kronecker;
T7Group[KeyConjugateIrr]:={{"1p","1pb"},{"3","3b"}};

omg=(-1+I*Sqrt[3])/2;

ClearAll[CGT7];
CGT7[x_,y_,z_]:={};

CGT7["1p","1pb","1"]:={
	{{1}}
};

CGT7["1p","1p","1pb:+"]:={
	{{1}}
};

CGT7["3","1p","3"]:={
	{{1},{0},{0}},
	{{0},{omg},{0}},
	{{0},{0},{omg^2}}
};

CGT7["3","1pb","3"]:={{{1},{0},{0}},{{0},{omg^2},{0}},{{0},{0},{omg}}};

CGT7["3","3","3:+"]:={{{0,0,0},{0,0,0},{0,0,1}},{{1,0,0},{0,0,0},{0,0,0}},{{0,0,0},{0,1,0},{0,0,0}}};

CGT7["3","3","3b:+"]:={1/Sqrt[2]{{0,0,0},{0,0,1},{0,1,0}},1/Sqrt[2]{{0,0,1},{0,0,0},{1,0,0}},1/Sqrt[2]{{0,1,0},{1,0,0},{0,0,0}}};

CGT7["3","3","3b:-"]:={1/Sqrt[2]{{0,0,0},{0,0,-1},{0,1,0}},1/Sqrt[2]{{0,0,1},{0,0,0},{-1,0,0}},1/Sqrt[2]{{0,-1,0},{1,0,0},{0,0,0}}};

CGT7["3","3b","1"]:={1/Sqrt[3]{{1,0,0},{0,1,0},{0,0,1}}};

CGT7["3","3b","1p"]:={1/Sqrt[3]{{1,0,0},{0,omg^2,0},{0,0,omg}}};

CGT7["3","3b","3"]:={{{0,0,0},{1,0,0},{0,0,0}},{{0,0,0},{0,0,0},{0,1,0}},{{0,0,1},{0,0,0},{0,0,0}}};

DotT7[a_,b_,ra_,rb_,rc_]:=DotByTable[T7Group,CGT7,a,b,ra,rb,rc];

T7Group[KeyDotFunction]:=DotT7;

ClearAll[T7GenA,T7GenB];
T7GenA["1"]:={{1}};
T7GenA["1p"]:={{1}};
T7GenA["1pb"]:={{1}};
T7GenA["3"]:=DiagonalMatrix[{Exp[I*2Pi/7],Exp[I*4Pi/7],Exp[I*8Pi/7]}];
T7GenA["3b"]:=DiagonalMatrix[{Exp[I*12Pi/7],Exp[I*10Pi/7],Exp[I*6Pi/7]}];
T7GenB["1"]:={{1}};
T7GenB["1p"]:={{Exp[I*2Pi/3]}};
T7GenB["1pb"]:={{Exp[I*4Pi/3]}};
T7GenB["3"]:={{0,1,0},{0,0,1},{1,0,0}};
T7GenB["3b"]:={{0,1,0},{0,0,1},{1,0,0}};

VerifyT7Generators[]:=Module[{i, reps, a,b},
	reps={"1","1p","1pb","3","3b"};
	For[i=1,i<= Length[reps],i++,
		a=T7GenA[reps[[i]]];
		b=T7GenB[reps[[i]]];

		If[Simplify[b.b.b]!= IdentityMatrix[Length[b]],Return[False]];
		If[Simplify[MatrixPower[a,7]]!= IdentityMatrix[Length[a]],Return[False]];
		If[Simplify[Inverse[b].a.b]!= Simplify[MatrixPower[a,4]],Return[False]];
	];

	Return[True]
];

ClearAll[VerifyT7CG];
VerifyT7CG[r1_,r2_,r3_]:=Module[{ops,op,d1,d2,d3,rr3,i,v1,v2,v3,v4,x1,y1,z1,x2,y2,z2},
	ops={T7GenA,T7GenB};
	d1=GetDimensionByRep[T7Group,r1];
	d2=GetDimensionByRep[T7Group,r2];
	d3=GetDimensionByRep[T7Group,r3];
	rr3=GetRepName[r3];
	v1={x1,y1,z1}[[1;;d1]];
	v2={x2,y2,z2}[[1;;d2]];
	v3=DotT7[v1,v2,r1,r2,r3];
	(*Print["v1=",v1, ", v2=", v2, ", v3=",v3, ", rr3=",rr3];*)
	For[i=1,i<= Length[ops],i++,
		op=ops[[i]];
		(*Print[op[r1]," ",op[r2], " ",op[rr3]];*)
		v4=DotT7[op[r1].v1,op[r2].v2, r1,r2,r3];
		(*Print["v4-v3=",Simplify[v4-op[rr3].v3]];*)
		If[Simplify[v4-op[rr3].v3]!= ConstantArray[0,d3],
			Return[False]
		];
	];

	Return[True]
];

VerifyT7CG[]:=Module[{irr,i,j,k,gi,res},
	gi=T7Group;
	irr={"1","1p","1pb","3","3b"};
	For[i=1,i<= Length[irr],i++,
		For[j=1,j<= Length[irr],j++,
			res=Kronecker[gi, irr[[i]], irr[[j]]];
			For[k=1,k<=Length[res],k++,
				If[VerifyT7CG[irr[[i]],irr[[j]],res[[k]]]==False,
					Print[irr[[i]],"*",irr[[j]],"->",res[[k]]," failed."];
					Return[False]
				];
			];
		];
	];

	Return[True]
];

Print["VerifyGroupInfo: ", VerifyGroupInfo[T7Group,VerifyDotFunction->True]];
Print["VerifyGroupInfo:", VerifyT7Generators[]];
Print["VerifyT7CG:", VerifyT7CG[]];

