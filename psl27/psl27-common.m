(* ::Package:: *)

<<"/users/gaolichen/gitroot/psl27cg/mpackage/cgframework.m";
<<"/users/gaolichen/gitroot/psl27cg/mpackage/numerical.m";

(* Returns a vector v such that Conjugate[v].v1 = Conjugate[v].v2 = 0. *)
ClearAll[CrossProduct];
Options[CrossProduct]={Phases->{}};
CrossProduct[v1_,v2_,opts:OptionsPattern[]]:=Module[{det,x,y,z,phases,rep},
	phases=OptionValue[Phases];
	rep = Table[phases[[i]]->1/phases[[i]],{i,Length[phases]}];
	det=Det[{{x,y,z},ComplexExpand[Conjugate[v1]],ComplexExpand[Conjugate[v2]]}]/.rep;
	Return[Simplify[{Coefficient[det,x],Coefficient[det,y],Coefficient[det,z]}]];
]

ClearAll[CountTerms]
CountTerms[expr_,var_]:=Module[{ret=0,e,i},
	e=Exponent[expr,var];
	For[i=e,i >= 1,i--,
		If[SameQ[Coefficient[expr,var^i],0]==False, ret++];
	];

	If[SameQ[Simplify[(expr/.{var->0})],0] == False, ret++];
	Return[ret]
];

ClearAll[ToEt6]
SetAttributes[ToEt6,Listable];
ToEt6[expr_,et_,n_:0]:=Module[
	{ret=expr,i,exp2,sum=1+et+et^2+et^3+et^4+et^5+et^6,cnt},
	cnt = CountTerms[expr,et];
	For[i=5,i>=2,i--,
		If[i!=n && SameQ[Coefficient[expr,et^i],0]==False,
			exp2=Expand[Simplify[expr/.{et^i->-Simplify[sum-et^i]}]];
			(*Print["i=",i, ", exp2=",exp2];*)
			If[CountTerms[exp2,et]<cnt, ret=exp2;Break[]]
		];
	];

	Return[Expand[ret]];
];

(* common functions for psl27-g4 CG coefficients calculation. *)
ClearAll[DecomposePoly];
Options[DecomposePoly]={Vars->{},Phases->{}};
DecomposePoly[poly_,basis_,opts:OptionsPattern[]]:=
	Module[{ret,i,j,vars,terms,rep,pp,coef,term,phases,invertedPhases, phases2One},
	ret = ConstantArray[0,Length[basis]];
	pp=Expand[poly];
	(*Print["pp=",pp];*)
	vars = OptionValue[Vars];
	phases=OptionValue[Phases];
	invertedPhases=Table[phases[[i]]->1/phases[[i]],{i,1,Length[phases]}];
	If[Length[vars]==0,vars=Variables[poly]];
	rep=Table[vars[[i]]->1,{i,1,Length[vars]}];
	phases2One=Table[phases[[i]]->1,{i,1,Length[phases]}];
	(*Print["phases2One=",phases2One];*)
	For[i=1,i<= Length[basis],i++,
		terms=MonomialList[basis[[i]]/.phases2One];
		(*Print["terms=",terms];*)
		For[j=1,j<= Length[terms],j++,
		coef =terms[[j]]/.rep;
		term = Simplify[terms[[j]]/coef];
		coef = Coefficient[basis[[i]],term];
		(*Print["coef=",Coefficient[pp,term], "*",coef];*)
		ret[[i]] += Coefficient[pp,term] * ComplexExpand[Conjugate[coef/.invertedPhases]];
	];
	ret[[i]]=Simplify[ret[[i]]];
	(*Print["ret=",ret[[i]]];*)
	];

	Return[Simplify[ret]]
];

 
ClearAll[DecomposePolyMat];
Options[DecomposePolyMat]=Join[{},Options[DecomposePoly]];
DecomposePolyMat[mat_,basis_,opts:OptionsPattern[]]:=Table[
	DecomposePoly[mat[[i]], basis,FilterRules[{opts},Options[DecomposePoly]]],
	{i,1,Length[mat]}
];

TestConjugateTransform[op_,mat_]:=Module[{opc},
	opc=Simplify[mat.Conjugate[op].Inverse[mat]];
	Return[Simplify[opc-op]]
];
 
(* Verify Psl27 Generators.*)
VerifyPsl27Generator[A_,B_]:=Module[{AB,n,zero,ABc},
	n=Length[A];
	If[n!= Length[B],Return[False]];
	zero = ConstantArray[0,{n,n}];

	AB=N[A.B];
	ABc=N[A.B.A.B.B];
	If[SameQ[Chop[Expand[N[A.A]]-IdentityMatrix[n]],zero]==False,
		Return[False]
	];

	If[SameQ[Chop[Expand[N[MatrixPower[B,3]]]-IdentityMatrix[n]],zero]==False,
		Print["VerifyPsl27Generator failed: B^3 != I."];
		Return[False]
	];

	If[SameQ[Chop[Expand[N[MatrixPower[AB,7]]]-IdentityMatrix[n]],zero]==False,
		Print["VerifyPsl27Generator failed: (AB)^7 != I."];
		Return[False]
	];

	If[SameQ[Chop[Expand[N[MatrixPower[ABc,4]]]-IdentityMatrix[n]],zero]==False,
		Print["VerifyPsl27Generator failed: [A,B]^4 != I."];
		Return[False]
	];

	Return[True];
];

(* Transpose[LeftDiag[Y]].Y.RightDiag[Y] = diagonal matrix *)
LeftDiag[Y_]:=Module[{mat,res,ret},
	mat = Y.ConjugateTranspose[Y];
	res = Eigensystem[mat];
	ret = ConjugateTranspose[res[[2]]];
	Return[ret];
];

RightDiag[Y_]:=Module[{mat,res,ret},
	mat = ConjugateTranspose[Y].Y;
	res = Eigensystem[mat];
	ret = Transpose[res[[2]]];

	Return[ret];
];

ClearAll[ExtractOverallPhase];
ExtractOverallPhase/:ExtractOverallPhase[expr_, phases_]:=Module[
	{i, e, ret = 1, expr2, rep1, rep2, diff},
	If[expr === 0, Return[{0, ret}]];

	expr2 = Factor[expr];

	For[i=1,i <= Length[phases],i++,
		e = Exponent[expr2, phases[[i]]];
		ret *= phases[[i]]^e;
	];

	(* verify it is reall an overall phase *)
	rep1 = Table[phases[[i]]->1, {i,Length[phases]}];
	rep2 = Table[phases[[i]]->2, {i,Length[phases]}];
	diff = Simplify[(expr/.rep1) * (ret/.rep2) - (expr/.rep2)];
	If[SameQ[diff, 0] == False, 
		Print["ret=", ret, ", diff=", diff];
		Print["ExtractOverallPhase: not overall phase, expr = ", expr];
		Throw[$Failed];
	];

	Return[{expr/.rep1, ret}];
]

ExtractOverallPhase/:ExtractOverallPhase[list_,phases_]:=Module[{i, ret={}, ph={}, res},
	For[i=1,i <= Length[list],i++,
		res = ExtractOverallPhase[list[[i]], phases];
		AppendTo[ret, res[[1]]];
		AppendTo[ph, res[[2]]];
	];
	
	Return[{ret, ph}];
]/;Head[list]==List

ClearAll[CalcGenerator];
CalcGenerator[dotFun_, phases_, rep1_, rep2_]:=Module[{n1, n2, i, v1, v2, res1, res2, gen, ph, ret},
	n1 = Length[rep1];
	n2 = Length[rep2];
	v1 = Table[Unique["x"], {i,n1}];
	v2 = Table[Unique["y"],{i,n2}];
	res1 = dotFun[v1,v2];
	res2 = dotFun[rep1.v1, rep2.v2];
	gen = DecomposePolyMat[res2, res1, Vars->Join[v1,v2], Phases->phases];
	(*Print["gen=",gen];*)
	{gen, ph} = ExtractOverallPhase[gen, phases];
	(*Print["gen=", gen, ", ph=", ph];*)
	ret = SimplifyCN[gen, et, 7];
	ret = ToEt6[ret, et];
	ret = Table[ret[[i,j]]*ph[[i,j]], {i, 1, Length[ret]}, {j, 1, Length[ret[[1]]]}];
	Return[ret];
];

ClearAll[ChargeDiff];
Options[ChargeDiff]={Numeric->False};
ChargeDiff[gen_, chargeOp_, phases_, opts:OptionsPattern[]]:=Module[{op2, gen1, gen2, rep, diff, ndiff},
	op2 = ConjugateTranspose[chargeOp];
	rep = Table[phases[[i]]->1/phases[[i]],{i, Length[phases]}];
	gen1 = chargeOp.gen.op2;
	gen2 = ToConjugateCN[gen, et, 7]/.rep;
	
	diff = gen2 - gen1;
	ndiff = Chop[Expand[N[diff/.et2Num]]];
	(*Print["ndiff=",ndiff];*)
	If[ndiff == ConstantArray[0, {Length[gen], Length[gen]}], Return[ndiff]];
	If[OptionValue[Numeric],
		Return[ndiff],
		Return[diff]
	];
];

SolveDiff[diff_, phases_, pos_]:=Module[{i,eqs={},root, ret, ph, ndiff},
	eqs = Table[diff[[pos[[i,1]],pos[[i,2]]]],{i,Length[pos]}];
	Quiet[root=Solve[eqs==0 && phases!=0, phases], {Solve::svars}];

	If[Length[root]!=1, 
		Print["SolveDiff: solve failed, root=", root];
		Throw[$Failed]
	];

	root = First[root];
	ret = phases/.root;
	{ret,ph}=ExtractOverallPhase[ret, phases];
	ret = SimplifyCN[ret, et, 7];
	ret = Table[phases[[i]] -> ret[[i]]*ph[[i]], {i,Length[ret]}];

	(* verify diff is zero with the solution*)
	ndiff=Chop[Expand[N[diff/.ret/.et2Num]]];
	If[SameQ[ndiff, ConstantArray[0,{Length[diff],Length[diff]}]]==False,
		Print["ndiff=", ndiff]
	];

	Return[ret]
];

SimplifyCnWithPhase[expr_,phases_]:=Module[{n,ph},
	{n,ph}=ExtractOverallPhase[expr,phases];
	n=SimplifyCN[n, et, 7];
	Return[n*ph]
];



TestCG[r1_,r2_,r3_,embed_,op_,cgList_]:=Module[{i,rr3,ret=True},
	For[i=1,i<= Length[cgList],i++,
		If[Length[cgList]==1,
			rr3=r3, rr3=SetRepMultiplicity[r3, i]
		];
		(*rr3=SetRepMultiplicity[r3, i];*)
		SetCG[r1,r2,rr3,embed,N[cgList[[i]]/.{et->Exp[I*2Pi/7]}]];
		If[VerifyCG[r1,r2,rr3,embed,op,b7ToNum]==False,
			Print["TestCG: failed for CG " <> r1 <> "*" <> r2 <>"->"<>rr3];
			ret = False
			(*,Print["VerifyCG succeed:", cgList[[i]]]*)
		];
		ResetCG[r1,r2,rr3,embed];
	];

	Return[ret]
];

ClearAll[SolveCGEquations];
SolveCGEquations[eqs_,freecoef_:{}]:=Module[{neqs,mat,root,i},
	(*Print["rank=",MatrixRank[eqs/.{et\[Rule]Exp[I*2*Pi/7]}]];*)
	neqs = IndependentRows[eqs,Var2N->{et->Exp[I*2*Pi/7]}];
	mat=SimplifyCN[neqs[[1]],et,7];
	(*root=SolveLinearEquation[mat,FreeCoefficients\[Rule]neqs[[2]],Numeric\[Rule]False];
	root=SimplifyCN[root,et,7];
	root=Simplify[root/.et4ToB7];*)

	mat=N[mat/.et2Num/.b7ToNum];
	(*Print["mat=",mat];
	Print["freeparameter=",neqs[[2]]];*)
	root=SolveLinearEquation[mat,FreeCoefficients->freecoef,Numeric->True];
	root=N2Exact[root]/.b7ToNum;
	root = SimplifyNum2[root];
	(*Print["root=",root];*)
	Return[root]
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

	(* If r1, r2, r3 are real reps, we need to make the *)
	gamma = CGConjugateMat[r1,r2,r3,embed];
	If[gamma == IdentityMatrix[Length[ncg[[1]]]],
		Do[ncg[[i]]=FixCGPhase[ncg[[i]], gamma], {i,1,Length[ncg]}],
		ncg=SolveConjugateConstraints[cgList, gamma]
	];

	(*Print["ncg=",ncg];*)
	ret=GramSchmid2[ncg];
	Return[NormalizeVectors[ret,Sqrt[Length[embed[GetRepName[r3]]]]]];

(*	vv=SimplifyNum2[ncg.ConjugateTranspose[ncg]];

	(*Print["vv=",MatrixForm[vv]];*)
	eigen=Eigensystem[vv];
	eigen[[1]]=SimplifyNum2[eigen[[1]]];
	eigen[[2]]=SimplifyNum2[eigen[[2]]];
	eigen[[2]]=Table[eigen[[2,i]]/Norm[eigen[[2,i]]],{i,1,Length[eigen[[2]]]}];
	eigen[[2]]=Simplify[eigen[[2]]];
	Dmhalf=DiagonalMatrix[ToRadicals[SqrtComplex[Reciprocal[eigen[[1]]]]]];
	(*Print["NormalizeCG eigen=", eigen, ", dmhalf=", Dmhalf];*)
	ret = Dmhalf.Conjugate[eigen[[2]]];
	(*Print["NormalizeCG ret1=", ret];*)
		
	matM = SimplifyNum2[ret.ncg];	
	matM = SimplifyNum2[matM.gamma.Transpose[matM]];
	eigen=Eigensystem[matM];
	(*Print["eigen=",eigen];*)
	eigen[[1]]=SimplifyNum2[eigen[[1]]];
	eigen[[2]]=SimplifyNum2[eigen[[2]]];
	(*Print["eigen2=",eigen];*)
	eigen[[2]]=Table[eigen[[2,i]]/Norm[eigen[[2,i]]],{i,1,Length[eigen[[2]]]}];
	matO=Transpose[eigen[[2]]];
		
	Pmhalf=DiagonalMatrix[SqrtComplex[Reciprocal[eigen[[1]]]]];
	(*Print["matM=", matM, ", eigen=", eigen, ", Pmhalf=",Pmhalf];*)
	(*tmp = SimplifyNum2[Pmhalf.ConjugateTranspose[matO]];*)
	ret = SimplifyNum2[Pmhalf.ConjugateTranspose[matO].ret];
	(*Print["NormalizeCG ret2=", ret];*)

	(*Print["ret.ncg=",Simplify[ret.ncg]];*)
	ret = SimplifyNum2[ret.ncg];
	(*Print["NormalizeCG ret3=", ret];*)
	
	Return[ret*Sqrt[Length[embed[GetRepName[r3]]]]];*)
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

Options[FinalizeCG]={FreeParameters->{}};
FinalizeCG[r1_,r2_,r3_,cgEqs_,embed_,opts:OptionsPattern[]]:=Module[
{coefsList,i,j,mat,nmat,mat2,evlist,cgmat,res,u,w,v,diag,fplist},
	fplist = OptionValue[FreeParameters];
	If[Length[fplist]>0, 
		coefsList=SolveCGEquations[cgEqs,FreeParameterToIndex[r1,r2,r3,fplist,embed]],
		coefsList=SolveCGEquations[cgEqs]
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
	eqs=CgcEquations[input, r1,r2,rr3,embed, opList];
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

(* PSL27 Group Info*)
ClearAll[Psl27]
Psl27[KeyIrr]:={{"1",1},{"3",3},{"3b",3,"\\bar{3}"},{"6",6},{"7",7},{"8",8}};

ClearAll[Psl27Kronecker];
Psl27Kronecker[x_,y_]:=DefaultKronecker[Psl27,x,y];
Psl27Kronecker["3","3"]={"3b:-","6:+"};
Psl27Kronecker["3","3b"]={"1","8"};
Psl27Kronecker["3","6"]={"3b","7","8"};
Psl27Kronecker["3","7"]={"6","7","8"};
Psl27Kronecker["3","8"]={"3","6","7","8"};
Psl27Kronecker["6","6"]={"1:+","6:+1","6:+2","8:+","7:-","8:-"};
Psl27Kronecker["6","7"]={"3","3b","6","7:1","7:2","8:1","8:2"};
Psl27Kronecker["6","8"]={"3","3b","6:1","6:2","7:1","7:2","8:1","8:2"};
Psl27Kronecker["7","7"]={"1:+","6:+1","6:+2","7:+","8:+","3:-","3b:-","7:-","8:-"};
Psl27Kronecker["7","8"]={"3","3b","6:1","6:2","7:1","7:2","8:1","8:2","8:3"};
Psl27Kronecker["8","8"]={"1:+","6:+1","6:+2","7:+","8:+1","8:+2","3:-","3b:-","7:-1","7:-2","8:-"};
Psl27[KeyKronecker]:=Psl27Kronecker;
Psl27[KeyConjugateIrr]:={{"3","3b"}};


b7ToNum={b7->(-1+I*Sqrt[7])/(2Sqrt[2]),d7->(-1-I*Sqrt[7])/(2Sqrt[2])};
b7ToEt={b7->(et+et^2+et^4)/Sqrt[2],d7->(et^6+et^5+et^3)/Sqrt[2]};
et4ToB7={et^4-> Sqrt[2]*b7-et-et^2};
sq7Tob7={Sqrt[7]->-2I*Sqrt[2]b7-I};
(*latexTob7={Subscript[b,7]->b7,Subscript[Overscript[b, _], 7]->d7};*)
et2Num={et->Exp[2Pi*I/7]};
