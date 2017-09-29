(* ::Package:: *)

<<"/users/gaolichen/gitroot/psl27cg/mpackage/cyclicnumber.m";
<<"/users/gaolichen/gitroot/psl27cg/mpackage/numerical.m";

KeyIrr="Irr";
KeyConjugateIrr="ConjugateIrr";
KeyKronecker="MyKroneckerProduct";
KeyDotFunction="DotFunction";
KeyLargeGroup="LargeGroup";
KeySubGroup="SubGroup";
KeyTransformMatrix="TransformMatrix";
KeyCGImplicitSymmetric="SubCGImplicitSymmetric";

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

KeyCGTerms="CGTerms";
KeyCGCoefficient="CGCoefficient";

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

ClearAll[SimpleList,TwoSimpleList];
SimpleList[n_Integer,m_Integer]:=Module[{ret},
	ret=ConstantArray[0,n];
	ret[[m]]=1;
	Return[ret]
];

TwoSimpleList[n1_Integer,n2_Integer,list_List]:=Table[{SimpleList[n1,list[[i,1]]],SimpleList[n2,list[[i,2]]]},{i,1,Length[list]}];

ClearAll[DotDifference];
DotDifference[v1_List,v2_List,r1_String,r2_String,r3_String,embed_Symbol,op_Symbol]:=Module[{res1,res2,res3,v3,v4},
	res1=op[GetRepName[r3]].DotRep[v1,v2,r1,r2,r3,embed];
	v3=op[r1].v1;
	v4=op[r2].v2;
	res2=DotRep[v3,v4,r1,r2,r3,embed];
	Return[res1-res2]
];

ClearAll[VerifyCG];
VerifyCG[r1_String,r2_String,r3_String,embed_Symbol,op_Symbol,rep_]:=Module[
	{v1,v2,lg,res,i,j,coef,d3,expect},

	lg=embed[KeyLargeGroup];
	v1=Table[Unique["x"],{i,1,GetDimensionByRep[lg, r1]}];
	v2=Table[Unique["y"],{i,1,GetDimensionByRep[lg, r2]}];
	d3=GetDimensionByRep[lg, r3];
	expect=ConstantArray[0,d3];
	res=N[DotDifference[v1,v2,r1,r2,r3,embed,op]/.rep];
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

ClearAll[CgcEquations]
CgcEquations[input_List,r1_String,r2_String,r3_String,embed_Symbol,opList_List]:=Module[{mat,vars,res,diff={},i,j},
	vars =embed[r1,r2,r3,KeyCGCoefficient];
	For[i=1,i<= Length[opList],i++,
		For[j=1,j<= Length[input],j++,
			diff=Join[diff,DotDifference[input[[j,1]],input[[j,2]],r1,r2,r3,embed,opList[[i]]]];
		];
	];

	mat=Table[Coefficient[diff, vars[[i]]], {i,1,Length[vars]}];
	Return[Transpose[mat]]
];

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

ClearAll[FixCGPhase];
FixCGPhase[coefs_,conjMat_]:=Module[
	{i,index,arg1,arg2},
	For[i=1,i<=Length[coefs],i++, 
		If[coefs[[i]]!= 0, Break[]]
	];

	If[i>Length[coefs], Print["FixCGPhase invalid input: coefs =", coefs]; Throw[$Failed]];

	For[index=1,index < Length[conjMat[[i]]],index++,
		If[conjMat[[i,index]]!=0, Break[]]
	];

	If[index>Length[coefs], Print["FixCGPhase invalid input: conjMat =", conjMat]; Throw[$Failed]];
	arg1=Arg[coefs[[i]]];
	arg2=Arg[coefs[[index]]];

	If[IntegerQ[(arg1+arg2)/(2*Pi)], Return[coefs]];
	Return[Simplify[coefs*Exp[-I*(arg1+arg2)/2]]]
];

(* orthogonalize CG coefficients. *)
ClearAll[OrthnormalizeCG];
OrthnormalizeCG[r1_,r2_,r3_,coefsList_,embed_]:=Module[
	{cgterms,pos={},i,j,subterm,subcoefs={},mat,ret,eigenV,norm},

	cgterms=embed[r1,r2,r3,KeyCGTerms];
	subterm = GetRepName[cgterms[[1,1]]];
	For[i=1,i<= Length[cgterms],i++,
		If[GetRepName[cgterms[[i,1]]]==subterm, AppendTo[pos, i]]
	];

	For[i=1,i<= Length[coefsList],i++,
		AppendTo[subcoefs,coefsList[[i]][[pos]]];
	];

	(*Print["subcoefs=",subcoefs];*)

	If[Length[coefsList]==1,
		(* If there is one set of CG coefficients, we do not need to do orthnormalization.*)
		ret=coefsList,

		(* If there are more than one set of CG coefficients, we need to do orthnormalization.*)
		Assert[Length[coefsList]>1];
		ret=GramSchmid[coefsList, et,7];
		(*Print["ret=",ret];*)
		(*mat=ConstantArray[0,{Length[subcoefs],Length[subcoefs]}];
		For[i=1,i\[LessEqual] Length[mat],i++,
		For[j=1,j\[LessEqual] Length[mat],j++,
		mat[[i,j]]= Conjugate[subcoefs[[i]]].subcoefs[[j]];
		]
		];
		(*Print["mat=",Simplify[mat]];*)

		(* orthogonalize. *)
		ret={};
		eigenV=Eigenvectors[mat];
		For[i=1,i\[LessEqual] Length[eigenV],i++,
		AppendTo[ret,Sum[eigenV[[i,j]]*coefsList[[j]],{j,1,Length[eigenV]}]]
		];*)
	];

	(* normalize. *)
	For[i=1,i<= Length[ret],i++,
		norm=Simplify[ToConjugateCN[ret[[i,pos]],et,7].ret[[i,pos]]];
		norm=SimplifyCN[norm,et,7];
		(*Print["norm=",norm];*)
		norm=Simplify[Sqrt[norm]];
		ret[[i]]/=norm;
		ret[[i]]=SimplifyCN[ret[[i]],et,7];
		(*Print["ret[[i]]=",ret];*)
	];

	Return[Simplify[ret]]
];


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

