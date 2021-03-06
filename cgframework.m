(* ::Package:: *)

(* This package file implements the framework for Subgroup-basis Clebsch-Gordan coeffcients calculation. *)

LoadPackage[file_]:= Get[FileNameJoin[{DirectoryName[$InputFileName],file}]];
LoadPackage["cyclicnumber.m"];
LoadPackage["numerical.m"];


(* This cell implements the data structures used in the framework. *)

KeyIrr="Irr";
KeyConjugateIrr="ConjugateIrr";
KeyKronecker="MyKroneckerProduct";
KeyDotFunction="DotFunction";
KeyLargeGroup="LargeGroup";
KeySubGroup="SubGroup";
KeyTransformMatrix="TransformMatrix";
KeyCGImplicitSymmetric="SubCGImplicitSymmetric";
KeyCGTerms="CGTerms";
KeyCGCoefficient="CGCoefficient";

(* 
Gets the name of representation from given string. 
If the string contains ":", split the string by ":" and return the first part. Otherwise, return the string. 
*)
ClearAll[GetRepName];
SetAttributes[GetRepName,Listable];
GetRepName[r_String]:=If[StringContainsQ[r,":"],First[StringSplit[r,":"]],r];

ClearAll[AllIrrs];
AllIrrs[gi_Symbol]:=gi[KeyIrr][[All,1]];

ClearAll[GetRepWithSym];
SetAttributes[GetRepWithSym,Listable];
GetRepWithSym[r_String]:=Module[{parts},
	If[StringContainsQ[r,":"]==False,Return[r]];

	parts=StringSplit[r,":"];
	If[StringContainsQ[Last[parts], "+"], Return[ToFullRep[First[parts], "+"]]];
	If[StringContainsQ[Last[parts], "-"], Return[ToFullRep[First[parts], "-"]]];
	Return[First[parts]];
];

ClearAll[GetSymmetryByRep];
GetSymmetryByRep[r_String]:=Module[{parts},
	If[StringContainsQ[r,":"]==False,Return[""]];

	parts=StringSplit[r,":"];
	If[StringContainsQ[Last[parts], "+"], Return["+"],
		If[StringContainsQ[Last[parts], "-"], Return["-"],Return[""]];
	];
]

ClearAll[GetRepDecorate];
GetRepDecorate[r_String]:=If[StringContainsQ[r,":"],Last[StringSplit[r,":"]],""];

ClearAll[ToFullRep];
ToFullRep[name_String,decorate_String]:=If[decorate=="", name, name<>":"<>decorate];

ClearAll[GetDimensionByRep];
GetDimensionByRep[gi_,r_String]:=Module[{v},
	v=SelectFirst[gi[KeyIrr], First[#]==GetRepName[r] &];
	Assert[Length[v]>= 2];
	Return[v[[2]]]
];

ClearAll[GetRepMultiplicity];
GetRepMultiplicity[r_String]:=
	If[StringContainsQ[r,":"]&&DigitQ[StringTake[r,-1]], 
		Return[ToExpression[StringTake[r,-1]]],
		Return[0]
	];

ClearAll[SetRepMultiplicity];
SetRepMultiplicity[r_String,m_]:=Module[{part},
	part=GetRepWithSym[r];
	If[StringContainsQ[part,":"], 
		Return[part<>ToString[m]],
		Return[part<>":"<>ToString[m]]
	];
];

(* By convention, the first representation should be the trivial singlet. *)
ClearAll[SingletRepresentation];
SingletRepresentation[gi_]:=gi[KeyIrr][[1,1]];

(* Return conjugate representation for a given representation. *)
ClearAll[ToConjugateRep];
SetAttributes[ToConjugateRep,Listable];
ToConjugateRep[gi_,r_String]:=Module[{conj,rn, rd},
	rn=GetRepName[r];
	(*Print["rn=",rn,", all conjs=",gi[KeyConjugateIrr]];*)
	conj=SelectFirst[gi[KeyConjugateIrr], #[[1]]==rn || #[[2]]==rn &];
	If[conj==Missing["NotFound"], Return[r]];
	rd=GetRepDecorate[r];
	If[conj[[1]]==rn, 
		Return[ToFullRep[conj[[2]], rd]], 
		Return[ToFullRep[conj[[1]],rd]]
	];
];

(* Return true if the given representation is real, otherwise false.*)
IsRealRep[gi_,r_String]:=Return[r==ToConjugateRep[gi,r]];

ClearAll[DefaultKronecker];
DefaultKronecker[gi_,r1_String,r2_String]:=Module[{},
	If[r1== SingletRepresentation[gi] && r2==r1, 
		Return[{ToFullRep[SingletRepresentation[gi], "+"]}]
	];

	If[r1== SingletRepresentation[gi],Return[{r2}]];
	If[r2== SingletRepresentation[gi],Return[{r1}]];
	Return[{}]
];

ClearAll[Kronecker];
Kronecker[gi_,r1_String,r2_String]:=Module[{kfun,ret},
	If[r1== SingletRepresentation[gi] && r1==r2, 
		Return[{ToFullRep[SingletRepresentation[gi], "+"]}]
	];

	If[r1== SingletRepresentation[gi], Return[{r2}]];
	If[r2== SingletRepresentation[gi], Return[{r1}]];

	kfun= gi[KeyKronecker];
	ret = kfun[r1,r2];
	If[Length[ret]>0, Return[ret]];

	ret=kfun[r2,r1];
	If[Length[ret]>0, Return[ret]];

	ret = kfun[ToConjugateRep[gi,r1],ToConjugateRep[gi,r2]];
	If[Length[ret]>0, Return[ToConjugateRep[gi,ret]]];

	ret = kfun[ToConjugateRep[gi,r2],ToConjugateRep[gi,r1]];
	If[Length[ret]>0, Return[ToConjugateRep[gi,ret]]];

	Return[{}];
];

ClearAll[GetCGMultiplicity];
GetCGMultiplicity[gi_,r1_String,r2_String,r3_String]:=
	Module[{list,rr3,i,ret=0},
	rr3=GetRepWithSym[r3];
	list=Kronecker[gi,r1,r2];
	For[i=1,i<= Length[list],i++,
		If[GetRepWithSym[list[[i]]]== rr3, ret++]
	];

	Return[ret]
];

ClearAll[DefaultEmbed];
DefaultEmbed[r_String,largeG_,subG_]:=
If[r== SingletRepresentation[largeG], {SingletRepresentation[subG]}, 
	If[r== KeyCGImplicitSymmetric, Return[False],Return[{}]]
];

ClearAll[DefaultDotFunction]
DefaultDotFunction::NoCGFound="Clebsh Gordan Coefficients `1` * `2` -> `3` not found.";
DefaultDotFunction[gi_,v1_List,v2_List,r1_String,r2_String,r3_String]:=Module[{},
	If[r1==SingletRepresentation[gi] && r1==r2, 
		Assert[Length[v1]==1];
		Assert[Length[v2]==1];
		Assert[r3== ToFullRep[SingletRepresentation[gi], "+"]];
		Return[{v1[[1]]*v2[[1]]}]
	];

	If[r1==SingletRepresentation[gi],
		Assert[r3==r2];
		Assert[Length[v1]==1];
		Return[v2*v1[[1]]]
	];

	If[r2==SingletRepresentation[gi],
		Assert[r3==r1];
		Assert[Length[v2]==1];
		Return[v1*v2[[1]]]
	];

	If[MemberQ[Kronecker[gi, r1,r2], r3]==False, 
		Message[DefaultDotFunction::NoCGFound, r1,r2,r3];
		Throw[$Failed]
	];

	Return[{}]
];

ClearAll[DotByTable];
DotByTable[gi_,tab_,a_,b_,ra_,rb_,rc_]:=Module[{cg,res,rab,rbb,rcb},
	res=DefaultDotFunction[gi, a,b,ra,rb,rc];
	If[Length[res]>0, Return[res]];

	(* find CG. *)
	cg = tab[ra,rb,rc];
	If[Length[cg]==0 && ra!=rb,
		(*Print[ra, " ", rb, " ", rc];*)
		cg = tab[rb,ra,rc];
		Do[cg[[i]]=Transpose[cg[[i]]],{i,1,Length[cg]}];
	];

	If[Length[cg]==0,
		rab=ToConjugateRep[gi,ra];
		rbb=ToConjugateRep[gi,rb];
		rcb=ToConjugateRep[gi,rc];
		cg = tab[rab,rbb,rcb];

		If[Length[cg]==0, 
			cg=tab[rbb,rab,rcb];
			Do[cg[[i]]=Transpose[cg[[i]]],{i,1,Length[cg]}];
		];

		If[Length[cg]!= 0,cg=Conjugate[cg]];
	];

	If[Length[cg]==0, Message[DefaultDotFunction::NoCGFound, ra,rb,rc]; Return[$Failed]];
	(*Print["cg=",cg];*)
	Return[Table[a.cg[[i]].b, {i,1,Length[cg]}]];
];

ClearAll[ToSubRep];
ToSubRep[v_List,r_String,subr_String,embed_]:=Module[
	{tmat,res, allsubr,i,subg,index=1},

	allsubr = embed[r];
	subg=embed[KeySubGroup];
	For[i=1,i<= Length[allsubr],i++,
		If[allsubr[[i]]==subr, Break[]];
		index += GetDimensionByRep[subg, allsubr[[i]]];
	];

	If[i>Length[allsubr],
		Print[r, " does not contains ", subr];Return[$Failed]
	];

	res=v[[index;;index+GetDimensionByRep[subg,subr]-1]];

	tmat = SelectFirst[embed[KeyTransformMatrix],#[[1]]== GetRepName[r] && #[[2]]== subr &];
	If[SameQ[tmat, Missing["NotFound"]]== False,
		res = tmat[[3]].res;
		(*Print["ToSubRep: tmat=",tmat[[3]]];*)
	];

	Return[res];
];

ClearAll[CGGeneralError];
CGGeneralError::ArgumentError="Argument error in function  `1`";

ClearAll[ToLargeRep]
ToLargeRep[r_String,vlist_List,embed_]:=Module[{allsubr,i,ret={},tmat},
	allsubr = embed[GetRepName[r]];
	If[Length[allsubr]!= Length[vlist],
		Message[CGGeneralError::ArgumentError, "ToLargeRep"];
		Throw[$Failed];
	];

	For[i=1,i<= Length[allsubr],i++,
		tmat = SelectFirst[embed[KeyTransformMatrix],#[[1]]== GetRepName[r] && #[[2]]== allsubr[[i]] &];
		If[SameQ[tmat, Missing["NotFound"]],
			ret=Join[ret, vlist[[i]]],
			ret=Join[ret,tmat[[3]].vlist[[i]]];
			(*Print["ToLargeRep: tmat=",tmat[[3]]];*)
		];
	];

	Return[ret]
];


ClearAll[GetCG];
GetCG[r1_String,r2_String,r3_String,embed_]:=embed[r1,r2,r3,KeyCGCoefficient];

ClearAll[SetCG];
SetCG[r1_String,r2_String,r3_String,embed_, coefs_]:=Module[{lg,klist},
	lg = embed[KeyLargeGroup];
	klist = Kronecker[lg, r1,r2];
	If[MemberQ[klist, r3]!= True, 
		Print["SetCG failed: cannot find the Kronecker product ", r1, "*",r2,"->",r3];
		Return[]
	];

	embed[r1,r2,r3,KeyCGCoefficient]=coefs;
];

ClearAll[ResetCG];
ResetCG[r1_String,r2_String,r3_String, embed_]:=Module[{cgterms},
	cgterms=embed[r1,r2,GetRepWithSym[r3],KeyCGTerms];
	embed[r1,r2,r3,KeyCGCoefficient]=Table[Unique["CG"],{h,1,Length[cgterms]}];
];


(* functions to test data structures. *)

ClearAll[VerifyGroupInfo];
Options[VerifyGroupInfo]={VerifyDotFunction->False};
VerifyGroupInfo[gi_, opt:OptionsPattern[]]:=Module[{irr,i,j,k, tot,res,res2,fun,tmp1,tmp2},
	irr=AllIrrs[gi];
	For[i=1,i<= Length[irr],i++,
		For[j=i,j<= Length[irr],j++,
			res=Kronecker[gi, irr[[i]], irr[[j]]];
			res2=Kronecker[gi, ToConjugateRep[gi,irr[[i]]], ToConjugateRep[gi,irr[[j]]]];
			res2=ToConjugateRep[gi,res2];
			res=Sort[res];
			res2=Sort[res2];
			If[res!= res2,
				Print["res=",res, ", res2=",res2];Return[False]
			];

			tot = Sum[GetDimensionByRep[gi, res[[k]]],{k,1,Length[res]}];
			If[tot!=GetDimensionByRep[gi, irr[[i]]] * GetDimensionByRep[gi,irr[[j]]],
				Print["tot=",tot, ", r1=",  GetDimensionByRep[gi, irr[[i]]] , ", r2=",  GetDimensionByRep[gi, irr[[j]]] ];
				Return[False]
			];
		];
	];

	If[OptionValue[VerifyDotFunction]==False, Return[True]];
	fun=gi[KeyDotFunction];
	For[i=1,i<= Length[irr],i++,
		tmp1=Table[RandomInteger[],{k,1,GetDimensionByRep[gi, irr[[i]]]}];
		For[j=i,j<= Length[irr],j++,
			tmp2=Table[RandomInteger[],{k,1,GetDimensionByRep[gi, irr[[j]]]}];
			res=Kronecker[gi, irr[[i]], irr[[j]]];
			(*Print["res=",res];*)
			For[k=1,k<= Length[res],k++,
				res2=fun[tmp1,tmp2,irr[[i]],irr[[j]],res[[k]]];
				If[SameQ[Length[res2],GetDimensionByRep[gi, res[[k]]]]==False,
					Print["ri=",irr[[i]],", rj=",irr[[j]],", rk=",res[[k]],", expect size=", GetDimensionByRep[gi, res[[k]]], ", returned=",Length[res2]];
					Return[False]
				];
			];
		];
	];

	Return[True]
];

ClearAll[VerifyEmbed];
VerifyEmbed[embed_]:=Module[{g,subg,irrs,list,i,j, conj,list2},
	g=embed[KeyLargeGroup];
	subg=embed[KeySubGroup];
	irrs=AllIrrs[g];

	For[i=2,i<= Length[irrs],i++,
		list=embed[irrs[[i]]];
		Assert[GetDimensionByRep[g,irrs[[i]]]== Sum[GetDimensionByRep[subg,list[[j]]],{j,1,Length[list]}]];
		conj=ToConjugateRep[g, irrs[[i]]];
		If[conj == irrs[[i]], Continue[]];

		list2=embed[conj];
		list2=ToConjugateRep[subg, list2];
		list2=Sort[list2];
		list = Sort[list];
		Assert[list==list2];
	];
];



(* functions to build CG coefficients and setup equations with respect to CG coefficients. *)

ClearAll[BuildCGTermsSub];
BuildCGTermsSub[r1_String,r2_String,subr_String,embed_]:=Module[
	{subg,subr1,subr2,i,j,k,list,res,dec,rn},
	subg=embed[KeySubGroup];
	subr1=embed[r1];
	subr2=embed[r2];
	dec=GetRepDecorate[subr];
	rn=GetRepName[subr];

	res={};
	For[i=1,i<= Length[subr1],i++,
		For[j=1,j<= Length[subr2],j++,
			list=Kronecker[subg, subr1[[i]],subr2[[j]]];
			For[k=1,k<= Length[list],k++,
				If[GetRepName[list[[k]]]!= rn,Continue[]];
				If[dec=="" || GetSymmetryByRep[list[[k]]]== dec || 
					(* if the subr1 and subr2 has the same dimension, it's possible that subr1*subr2\[Rule]list[[k]] is 
					already symmetrized or antisymmetrized even subr1 and subr2 are different. So we simply add both 
					subr1*subr2\[Rule]list[[k]] and subr2*subr1\[Rule]list[[k]] in this case. *)
					(SameQ[embed[KeyCGImplicitSymmetric],True] && GetDimensionByRep[subg,subr1[[i]]]==GetDimensionByRep[subg,subr2[[j]]]),
					AppendTo[res,{list[[k]], subr1[[i]], subr2[[j]]}],
					If[GetSymmetryByRep[list[[k]]]== "" && Order[GetRepName[subr1[[i]]],GetRepName[subr2[[j]]]]>0,
						AppendTo[res,{list[[k]], subr1[[i]], subr2[[j]], ToExpression[dec<>"1"]}];
					]
				];
			];
		];
	];

	Return[res];
];

ClearAll[BuildCGTerms];
BuildCGTerms[r1_String,r2_String,r3_String,embed_]:=Module[
	{subg,subr,i,dec,rn,res={}},
	subg=embed[KeySubGroup];
	dec = GetRepDecorate[r3];
	rn=GetRepName[r3];
	subr=embed[rn];
	(*Print["subr=",subr];*)

	For[i=1,i<= Length[subr],i++,
		res=Join[res, BuildCGTermsSub[r1,r2, ToFullRep[subr[[i]], dec], embed]]
	];

	Return[res]
];

ClearAll[BuildCGTermsAll];
BuildCGTermsAll[embed_]:=Module[
	{lg, rlist,i,j,k,klist,terms},

	lg = embed[KeyLargeGroup];
	rlist = AllIrrs[lg];
	(* start from 2nd rep because the first one is trivial singlet representation*)
	For[i=2,i<= Length[rlist],i++,
		For[j=i,j<= Length[rlist],j++,
			klist = DeleteDuplicates[GetRepWithSym[Kronecker[lg,rlist[[i]],rlist[[j]]]]];
			For[k=1,k<= Length[klist],k++,
				terms=BuildCGTerms[rlist[[i]],rlist[[j]],klist[[k]],embed];
				embed[rlist[[i]],rlist[[j]],klist[[k]],KeyCGTerms]=terms;
				(*Print[rlist[[i]]," ",rlist[[j]]," ",klist[[k]],"=",terms];*)
			];

			klist = Kronecker[lg,rlist[[i]],rlist[[j]]];
			For[k=1,k<= Length[klist],k++,
				(*ResetCG[rlist[[i]],rlist[[j]],klist[[k]],embed];*)
				terms=embed[rlist[[i]],rlist[[j]],GetRepWithSym[klist[[k]]],KeyCGTerms];
				embed[rlist[[i]],rlist[[j]],klist[[k]],KeyCGCoefficient]=Table[Unique["CG"],{h,1,Length[terms]}];
			];
		];
	];
];

ClearAll[DotRep]
DotRep[v1_List,v2_List,r1_String,r2_String,r3_String,embed_]:=Module[
	{terms,cgc,lg,subg,i,j,subr,subv1,subv2,subv3,subv4,vlist={},res,subdot,tmp},
	lg = embed[KeyLargeGroup];
	res=DefaultDotFunction[lg, v1,v2,r1,r2,r3];
	If[Length[res]>0, Return[res]];

	subg=embed[KeySubGroup];
	subdot = subg[KeyDotFunction];
	terms = embed[r1,r2,GetRepWithSym[r3], KeyCGTerms];
	cgc = embed[r1,r2,r3, KeyCGCoefficient];
	subr=embed[GetRepName[r3]];

	For[i=1,i<= Length[subr],i++,
		(*Print[subr[[i]], ":", GetDimensionByRep[subg, subr[[i]]]];
		Print[vlist];*)
		AppendTo[vlist, ConstantArray[0, GetDimensionByRep[subg, subr[[i]]]]];
		(*Print[vlist];*)
		For[j=1,j<=Length[terms],j++,
			If[GetRepName[terms[[j,1]]]!= subr[[i]], Continue[]];
			subv1=ToSubRep[v1, r1,terms[[j,2]], embed];
			subv2=ToSubRep[v2, r2,terms[[j,3]], embed];
			(* the fourth element of terms[j] is the symmetry type. *)
			If[Length[terms[[j]]]==3,
				tmp=subdot[subv1,subv2, terms[[j,2]], terms[[j,3]], terms[[j,1]]];
				(*Print["tmp=",tmp];
				If[Length[tmp]\[Equal]0,Print["v1=",subv1,",v2=",subv2, "term=",terms[[j]]]];*)
				vlist[[i]]+= cgc[[j]]*tmp;
			];

			If[Length[terms[[j]]]==4,
				subv3=ToSubRep[v1, r1,terms[[j,3]], embed];
				subv4=ToSubRep[v2, r2,terms[[j,2]], embed];
				tmp=subdot[subv3,subv4, terms[[j,3]], terms[[j,2]], terms[[j,1]]];
				(*Print["tmp=",tmp];
				If[Length[tmp]\[Equal]0,Print["v1=",subv3,",v2=",subv3, "term=",terms[[j]]]];*)
				vlist[[i]]+= cgc[[j]]/Sqrt[2]*subdot[subv1,subv2, terms[[j,2]], terms[[j,3]], terms[[j,1]]];
				vlist[[i]]+= cgc[[j]]/Sqrt[2]*terms[[j,4]]*tmp;
			];
		];
	];

	Return[ToLargeRep[r3,vlist,embed]]
];

ClearAll[DotDifference];
DotDifference[v1_List,v2_List,r1_String,r2_String,r3_String,embed_Symbol,op_Symbol]:=Module[{res1,res2,res3,v3,v4},
	res1=op[GetRepName[r3]].DotRep[v1,v2,r1,r2,r3,embed];
	v3=op[r1].v1;
	v4=op[r2].v2;
	res2=DotRep[v3,v4,r1,r2,r3,embed];
	Return[res1-res2]
];

ClearAll[VerifyCG];
VerifyCG[r1_String,r2_String,r3_String,embed_Symbol,op_Symbol,rep_:{}]:=Module[
	{v1,v2,lg,res,i,j,coef,d3,expect},

	lg=embed[KeyLargeGroup];
	v1=Table[Unique["x"],{i,1,GetDimensionByRep[lg, r1]}];
	v2=Table[Unique["y"],{i,1,GetDimensionByRep[lg, r2]}];
	d3=GetDimensionByRep[lg, r3];
	expect=ConstantArray[0,d3];
	If[Length[rep]>0,
		res=N[DotDifference[v1,v2,r1,r2,r3,embed,op]/.rep],
		res=N[DotDifference[v1,v2,r1,r2,r3,embed,op]];
	];
	
	For[i=1,i<= Length[v1],i++,
		For[j=1,j<= Length[v2],j++,
			If[Chop[Coefficient[res,v1[[i]]*v2[[j]]]]!= expect, 
				Print["diff=",Chop[Coefficient[res,v1[[i]]*v2[[j]]]]];
				Return[False]
			]
		]
	];

	Return[True]
];

ClearAll[SetupCgcEquations]
SetupCgcEquations[input_List,r1_String,r2_String,r3_String,embed_Symbol,opList_List]:=Module[{mat,vars,res,diff={},i,j},
	vars =embed[r1,r2,r3,KeyCGCoefficient];
	For[i=1,i<= Length[opList],i++,
		For[j=1,j<= Length[input],j++,
			diff=Join[diff,DotDifference[input[[j,1]],input[[j,2]],r1,r2,r3,embed,opList[[i]]]];
		];
	];

	mat=Table[Coefficient[diff, vars[[i]]], {i,1,Length[vars]}];
	Return[Transpose[mat]]
];



(* function to solve equations built by SetupCgcEquations *)

ClearAll[SolveLinearEquation];
Options[SolveLinearEquation]={FreeCoefficients->{},Numeric->False};
SolveLinearEquation[cMat_List, opts:OptionsPattern[]]:=Module[
	{n,vars,freevars,i,eqs,root,freecoef,tosolve,allzero,ans,res={},zeroArray},

	If[Length[cMat]==0,Return[{}]];
	n=Length[cMat[[1]]];
	vars=Table[Unique["Var"],{i,1,n}];
	If[OptionValue[Numeric],
		eqs = N[cMat].vars,
		eqs = cMat.vars
	];

	freecoef=OptionValue[FreeCoefficients];
	If[Length[freecoef]>0,
		freevars = vars[[freecoef]];
		tosolve = Join[freevars,Select[vars,MemberQ[freevars,#]==False &]],
		tosolve = vars;
	];

	(*Print["vars=",vars, ", tosolve=", tosolve, ", freecoef=", freecoef];*)
	Quiet[root = Solve[eqs==0,tosolve], {Solve::svars}];
	If[Length[root]!=1,
		Print["SolveLinearEquation: Failed to solve equations, root=",root];
		Throw[$Failed],
		root=First[root];
	];

	(*Print["cMat.vars=",Collect[N[cMat].vars/.root,vars]];
	Print["eqs=",Collect[eqs/.root,vars]];*)
	(*Print["root=",root];*)
	allzero=Table[vars[[i]]->0,{i,1,Length[vars]}];
	root = vars/.root;
	zeroArray=ConstantArray[0,Length[vars]];
	For[i=1,i<= Length[vars],i++,
		ans=root/.{vars[[i]]->1};
		ans=ans/.allzero;
		If[ans!= zeroArray, 
			(*Print["ans=",ans];*)
			AppendTo[res,ans]
		];
	];

	If[OptionValue[Numeric],
		Return[Chop[res]],
		Return[res]
	];
];

(* find the index of free parameter. The fp argument has the form: r1*r2\[Rule]r3 *)
ClearAll[FreeParameterToIndex]
SetAttributes[FreeParameterToIndex,Listable]
FreeParameterToIndex[r1_String,r2_String, r3_String, fp_String, embed_]:=Module[{term,tmp,tlist,ret,i},
	term = StringSplit[fp, {"*","->","\[Rule]"," "}];
	If[Length[term]!= 3, Print["Invalid free parameter input: ", fp]; Throw[$Failed]];

	tmp=term[[3]];
	term[[3]]=term[[2]];
	term[[2]]=term[[1]];
	term[[1]]=tmp;
	
	tlist = embed[r1,r2,r3,KeyCGTerms];
	ret = -1;
	For[i = 1, i <= Length[tlist], i++,
		If[Length[tlist[[i]]]==3 && tlist[[i]] == term, ret=i; Break[]]
		If[Length[tlist[[i]]]==4 && tlist[[i,1]]==term[[1]], 
			If[(tlist[[i,2]]==term[[2]] && tlist[[i,3]]==term[[3]])
				|| tlist[[i,3]]==term[[2]] && tlist[[i,2]]==term[[3]], ret=i; Break[]];
		];
	];
	
	If[ret == -1, 
		Print["Failed to find free parameter ", fp, " for ", r1, "*", r2, "->", r3];
		Throw[$Failed];
	];

	Return[ret]
];

TestCG[r1_,r2_,r3_,embed_,op_,cgList_]:=Module[{i,rr3,ret=True},
	For[i=1,i<= Length[cgList],i++,
		If[Length[cgList]==1,
			rr3=r3, rr3=SetRepMultiplicity[r3, i]
		];
		(*rr3=SetRepMultiplicity[r3, i];*)
		SetCG[r1,r2,rr3,embed,N[cgList[[i]]]];
		If[VerifyCG[r1,r2,rr3,embed,op]==False,
			Print["TestCG: failed for CG " <> r1 <> "*" <> r2 <>"->"<>rr3];
			ret = False
			(*,Print["VerifyCG succeed:", cgList[[i]]]*)
		];
		ResetCG[r1,r2,rr3,embed];
	];

	Return[ret]
];



(* function to solve CP constraints and orthonormalize CG coefficients. *)

ClearAll[CGConjugateMat];
CGConjugateMat[r1_,r2_,r3_,embed_]:=Module[{cgterms,subG,conj,conj2,i,j,ret,index},
	cgterms=embed[r1,r2,r3,KeyCGTerms];
	subG=embed[KeySubGroup];
	ret=ConstantArray[0,{Length[cgterms],Length[cgterms]}];
	For[i=1,i<= Length[cgterms],i++,
		conj=Table[ToConjugateRep[subG, cgterms[[i,j]]],{j,1,3}];
		If[Length[cgterms[[i]]]==4,AppendTo[conj,cgterms[[i,4]]]];
		conj2=conj;
		conj2[[2]]=conj[[3]];
		conj2[[3]]=conj[[2]];
		For[j=1,j<= Length[cgterms],j++,
			If[cgterms[[j]]== conj, 
				ret[[i,j]]=1; Break[],
				If[Length[conj]==4 &&cgterms[[j]]==conj2,
					ret[[i,j]]=conj[[4]];Break[];
				];
			];
		];
	];

	Return[ret];
];


(* find orghogonal basis *)
ClearAll[GramSchmid2];
GramSchmid2[vList_List]:=Module[{ret={},i,j,vvl,inv,dot},
	If[Length[vList]==1,Return[vList]];
	vvl=vList;
	For[i=1,i<= Length[vvl],i++,
		If[vvl[[i]]=== ConstantArray[0,Length[vvl[[i]]]], Continue[]];
		AppendTo[ret,vvl[[i]]];
		inv=SimplifyNum2[1/(Conjugate[vvl[[i]]].vvl[[i]])];
		For[j=i+1,j<= Length[vvl],j++,
			vvl[[j]] = SimplifyNum2[vvl[[j]]-Conjugate[vvl[[i]]].vvl[[j]]*inv*vvl[[i]]];
		];
	];

	Return[ret]
];

ClearAll[NormalizeVectors];
NormalizeVectors[vList_List,factor_]:=Module[{i,ret={},norm},
	For[i=1,i<=Length[vList],i++,
		norm=SimplifyNum2[Sqrt[Conjugate[vList[[i]]].vList[[i]]]];
		AppendTo[ret, SimplifyNum2[vList[[i]]/norm*factor]]
	];

	Return[ret]
];

ClearAll[SolveConjugateConstraints];
SolveConjugateConstraints[cgc_,gamma_]:=Module[
	{reVarList,imVarList, i, cg1, cg2, cg1parts, cg2parts, root, allzero, ret={}, v},

	reVarList=Table[Unique["cgRe"],{i,1,Length[cgc]}];
	imVarList=Table[Unique["cgIm"],{i,1,Length[cgc]}];
	cg1 = Sum[(reVarList[[i]]+imVarList[[i]]*I)*cgc[[i]],{i,1,Length[cgc]}];
	cg2 = gamma.ComplexExpand[Conjugate[cg1]];
	cg1parts = ComplexExpand[Join[Re[cg1],Im[cg1]]];
	cg2parts = ComplexExpand[Join[Re[cg2],Im[cg2]]];

	Quiet[root=Solve[cg1parts==cg2parts, Join[reVarList, imVarList]],{Solve::svars}];
	If[Length[root]==0, 
		Print["SolveConjugateConstraints: No solution found."];
		Throw[$Failed];
	];

	root = First[root];
	cg1=Simplify[cg1/.root];
	(*Print["root=",root, ", cg1=",cg1];*)
	
	allzero=Join[Table[reVarList[[i]]->0,{i,1,Length[reVarList]}],
		Table[imVarList[[i]]->0,{i,1,Length[reVarList]}]];

	For[i=1, i <= Length[reVarList], i++,
		v=Simplify[cg1/.{reVarList[[i]]->1}];
		v= Simplify[v/.allzero];
		If[SameQ[v,ConstantArray[0,Length[cg1]]]==False, AppendTo[ret,v]];

		v=Simplify[cg1/.{imVarList[[i]]->1}];
		v=Simplify[v/.allzero];
		If[SameQ[v,ConstantArray[0,Length[cg1]]]==False, AppendTo[ret,v]];
	];

	Return[ret]
];

NormalizeCG[r1_,r2_,r3_,cgList_,embed_]:=Module[{vv,ncg,eigen,tmp,Dmhalf,ret,lg,matM,gamma,svd,matO,Pmhalf,i},
	ncg = cgList/.b7ToNum/.et2Num;

	lg = embed[KeyLargeGroup];
	(* If any of r1, r2, r3 are complex, we simply use GramSchmid algorithm to find orthogonal basis.*)
	If[IsRealRep[lg, r1]==False || IsRealRep[lg, r2]==False || IsRealRep[lg, r3]==False,
		ret=GramSchmid2[ncg];
		Return[NormalizeVectors[ret,Sqrt[Length[embed[GetRepName[r3]]]]]]
	];

	(* If r1, r2, r3 are real reps, we need to solve the CP constraints to make each set of CG real*)
	gamma = CGConjugateMat[r1,r2,r3,embed];
	ncg=SolveConjugateConstraints[cgList, gamma];

	(*Print["ncg=",ncg];*)
	ret=GramSchmid2[ncg];
	Return[NormalizeVectors[ret,Sqrt[Length[embed[GetRepName[r3]]]]]];
];



(* main function to calculate CG coefficients. *)

Options[FinalizeCG]={FreeParameters->{},EquationSolver->Null};
FinalizeCG[r1_,r2_,r3_,cgEqs_,embed_,opts:OptionsPattern[]]:=Module[
{coefsList,i,j,mat,nmat,mat2,evlist,cgmat,res,u,w,v,diag,fplist,solver=OptionValue[EquationSolver]},
	If[solver === Null,
		Print["FinalizeCG: EquationSolver is null."];
		Throw[$Failed];
	];

	fplist = OptionValue[FreeParameters];
	If[Length[fplist]>0, 
		coefsList=solver[cgEqs,FreeParameterToIndex[r1,r2,r3,fplist,embed]],
		coefsList=solver[cgEqs]
	];

	(* If there is only one cg term, then we manually set the CG coefficients to 1. *)
	If[Length[coefsList]==0 && Length[embed[r1,r2,r3,KeyCGTerms]]==1,
		coefsList={{1}};
	];
	(*Print["coefsList=",coefsList];*)

	If[TestCG[r1,r2,r3,embed,PslGenB,coefsList/.b7ToNum]==False, 
		Return[{}]
	];

	coefsList=NormalizeCG[r1,r2,r3,coefsList,embed];
	Return[ToRadicals[coefsList]];
];

ClearAll[CalculateCG];
Options[CalculateCG]=Join[{},Options[FinalizeCG]];
CalculateCG[r1_String,r2_String,r3_String,embed_, input_,opList_,opts:OptionsPattern[]]:=
Module[{eqs,res,i,rr3,repName,repDec,m,largeG},
	largeG=embed[KeyLargeGroup];
	m=GetCGMultiplicity[largeG,r1,r2,r3];
	If[m>1,rr3=SetRepMultiplicity[r3,1],rr3=r3];
	ResetCG[r1,r2,rr3,embed];
	(*Print["GetCG=",GetCG[r1,r2,rr3,embed]];*)
	eqs=SetupCgcEquations[input, r1,r2,rr3,embed, opList];
	(*Print["eqs=",eqs];*)
	res=FinalizeCG[r1,r2,GetRepWithSym[r3],eqs, embed, FilterRules[{opts},Options[FinalizeCG]]];
	(*Print["res=",res];*)
	For[i=1,i<= Length[res],i++,
		If[Length[res]==1,
			rr3=r3, rr3=SetRepMultiplicity[r3, i]
		];
		SetCG[r1,r2,rr3,embed,res[[i]]];
	];

	Return[ToExp[res]]
];


(* utility functions *)

ClearAll[PrintCG];
PrintCG[r1_,r2_,r3_, embed_]:=Module[{cg,cgterms,term,row,i,isFirst=True,c},
	cg=GetCG[r1,r2,r3,embed];
	cgterms=embed[r1,r2,GetRepWithSym[r3],KeyCGTerms];
	row={};

	For[i=1,i<= Length[cg],i++,
		If[SameQ[cg[[i]],0]==True, Continue[]];
		c = ToExp[cg[[i]]];
		If[isFirst== False && StringTake[ToString[c,InputForm],1]!= "-",
			AppendTo[row,"+"];
		];
		AppendTo[row,c];
		term=cgterms[[i]];
		AppendTo[row, "("<>term[[2]]<>"*"<>term[[3]]<>"->"<>term[[1]]<>")"];
		If[Length[term]==4,
			If[term[[4]]==1,
				AppendTo[row,"_s"],
				AppendTo[row,"_a"]]
		];
		isFirst=False;
	];

	Print[Row[row]];
];

ClearAll[SimpleList,TwoSimpleList];
SimpleList[n_Integer,m_Integer]:=Module[{ret},
	ret=ConstantArray[0,n];
	ret[[m]]=1;
	Return[ret]
];

TwoSimpleList[n1_Integer,n2_Integer,list_List]:=Table[{SimpleList[n1,list[[i,1]]],SimpleList[n2,list[[i,2]]]},{i,1,Length[list]}];

