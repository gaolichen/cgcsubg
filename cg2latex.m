(* ::Package:: *)

<<"/users/gaolichen/gitroot/psl27cg/mpackage/cgframework.m";
<<"/users/gaolichen/gitroot/psl27cg/mpackage/numerical.m";

MyWriteLine[os_, x___]:=WriteString[os,x, "\n"];

ClearAll[RepTexName];
Options[RepTexName]={WithSymmetry->True};
RepTexName[gi_,r_,opts:OptionsPattern[]]:= Module[{v,name,sub="",sym,ret},
	v=SelectFirst[gi[KeyIrr], First[#]==GetRepName[r] &];
	If[Length[v]>=3, name=v[[3]],name=GetRepName[r]];
	If[StringContainsQ[name, "_"],
		v=StringSplit[name,"_"];
		name=v[[1]];sub=v[[2]];
	];

	If[OptionValue[WithSymmetry],
		sym = GetRepWithSym[r];
		If[StringTake[sym,-1]== "+", 
			sub = sub <> "s", 
			If[StringTake[sym,-1]== "-",sub = sub <> "a"]
		];
	];

	ret=name;
	If[sub!= "", ret=ret<>"_{"<>sub<> "}"];

	Return[ret]
];

ClearAll[Rep2TeX];
Options[Rep2TeX]={Primed->False,WithSymmetry->True,VarName->""};
Rep2TeX[gi_,r_,opts:OptionsPattern[]]:=Module[
	{v,name,ret, sub="", sup="",sym, m,rep},
	v=SelectFirst[gi[KeyIrr], First[#]==GetRepName[r] &];
	If[Length[v]>=3, name=v[[3]],name=GetRepName[r]];
	If[StringContainsQ[name, "_"],
		v=StringSplit[name,"_"];
		name=v[[1]];sub=v[[2]];
	];

	m=GetRepMultiplicity[r];
	If[m>0,sup="("<>ToString[m]<>")"];

	If[OptionValue[WithSymmetry],
		sym = GetRepWithSym[r];
		If[StringTake[sym,-1]== "+", 
			sub = sub <> "s", 
			If[StringTake[sym,-1]== "-",sub = sub <> "a"]
		];
	];

	If[OptionValue[Primed],sup=sup<>"\\prime"];

	If[OptionValue[VarName] == "",
		ret="\\rep{"<>name<>"}",
		ret = "\\repx{"<>name<>"}{"<>OptionValue[VarName]<>"}"
	];

	If[sub!= "",
		ret=ret<>"_{"<>sub<> "}"
	];

	If[sup!= "",
		ret=ret<>"^{"<>sup<> "}"
	];

	Return[ret]
];

ClearAll[RepSum2TeX];
(*Options[RepSum2TeX]=Join[{},Options[Rep2TeX]];*)
RepSum2TeX[gi_,r1_, r2_, reps_(*,opts:OptionsPattern[]*)]:=Module[
	{i, res=""},
	
	For[i=1,i<= Length[reps],i++,
		If[i>1, res= res<>"+"];
		res = res <> Rep2TeX[gi,reps[[i]], WithSymmetry->False(*FilterRules[{opts},Options[Rep2TeX]]*)];
	];

	Return[res]
];

ClearAll[KroneckerEquation2TeX];
KroneckerEquation2TeX[ gi_,r1_,r2_]:=Module[
	{kronecker,i, symReps={}, antiSymReps={}, res=""},
	
	kronecker=Kronecker[gi,r1,r2];
	If[r1==r2,
		(* need to handle symmetric and antisymmetric *)
		For[i=1,i<=Length[kronecker],i++,
			If[StringTake[GetRepWithSym[kronecker[[i]]],-1]=="+",
				AppendTo[symReps, kronecker[[i]]],
				AppendTo[antiSymReps, kronecker[[i]]]
			]
		];

		If[Length[symReps]>1,
			res = res <> "\\left(" <>RepSum2TeX[gi,r1,r2, symReps]<> "\\right)_s",
			res = res <> RepSum2TeX[gi,r1,r2, symReps]<>"_s";
		];

		If[Length[antiSymReps]>1,
			res = res <> "+\\left(" <>RepSum2TeX[gi,r1,r2, antiSymReps]<> "\\right)_a",
			res = res <> "+"<> RepSum2TeX[gi,r1,r2, antiSymReps]<>"_a";
		],
		(* No symmetry or antisymmetry *)
		res = RepSum2TeX[gi,r1,r2, kronecker];
	];

	Return["\\paragraph*{\\Large $"<> Rep2TeX[gi,r1]<> "\\otimes"<> Rep2TeX[gi,r2]<> "\\to"<> res<>"$}"];
];

EqsToTeX[gi_,r1_, r2_, r3_]:=Module[{primed = False},
	If[r1==r2,primed=True];
	Return[Rep2TeX[gi,r1,VarName->"x"]<>"\\otimes"<>Rep2TeX[gi,r2, (*Primed->primed,*)VarName->"y"]<>"\\to"<>Rep2TeX[gi,r3]];
];

ClearAll[SubRep2TeX];
SubRep2TeX[embed_,subr_, r_,primed_:False]:=Module[{subG, largeG},
	subG=embed[KeySubGroup];
	largeG=embed[KeyLargeGroup];
	(*Print["subr=",subr,", r=",r];
	Print["dim subr=",GetDimensionByRep[subG,subr], ", dim r=",GetDimensionByRep[largeG,r]];*)
	If[GetDimensionByRep[subG,subr] != GetDimensionByRep[largeG,r],
		Return[Rep2TeX[subG,subr]<> "_{" <> Rep2TeX[largeG,r,Primed->primed] <> "}"],
		Return[Rep2TeX[subG,subr,Primed->primed]]
	]
];

(* return tex for subr1*subr2 \[Rule] to *)
Dot2TeX[embed_,subr1_,subr2_,r1_,r2_, to_]:=Module[{primed, sym, to2, withSym = True, subG,v},
	subG=embed[KeySubGroup];
	If[r1==r2, primed = True, primed = False];
	sym = GetSymmetryByRep[to];
	If[sym != "", 
		If[sym == "+", 
			to2 = ToFullRep[GetRepName[to],"-"],
			to2 = ToFullRep[GetRepName[to],"+"]
		];

		v=Select[Kronecker[subG,subr1, subr2], GetRepWithSym[#]==to2 &];
		If[Length[v]==0, withSym = False];
	];

	(*Print["embed=",embed,", subr1=",subr1,", r1=",r1];
	Print["embed=",embed,",subr2=",subr2,", r2=",r2];
	Print["SubRep2Tex=",SubRep2TeX[embed,subr1,r1]];
	Print["SubRep2Tex=",SubRep2TeX[embed,subr2,r2,primed]];*)
	(*Return["\\subcg{" <> SubRep2TeX[embed,subr1,r1] <> "}{" <> SubRep2TeX[embed,subr2,r2, primed] <>  "}{" <> Rep2TeX[subG,to, WithSymmetry->withSym] <> "}" ];*)
	Return["\\subcg{" <> RepTexName[subG,subr1] <> "}{" <> RepTexName[subG,subr2] <>  "}{" <> RepTexName[subG,to, WithSymmetry->withSym] <> "}" ];
];

ClearAll[CGTerm2TeX];
CGTerm2TeX[embed_,ana_, r1_, r2_]:=Module[{sign, exp},
	If[Length[ana]< 4,
		Return[Dot2TeX[embed,ana[[2]],ana[[3]],r1,r2, ana[[1]]]],
		If[ana[[4]]==1,
			(* Symmetric case.*)
			sign="+",
			(*AntiSymmetric case.*)
			sign="-"
		]
	];

	exp = Dot2TeX[embed,ana[[2]],ana[[3]],r1,r2, ana[[1]]] <> sign <> Dot2TeX[embed,ana[[3]],ana[[2]],r1,r2, ana[[1]]];
	exp = "\\left(" <> exp <> "\\right)";
	Return[exp];
];

Clear[IsNegative];
IsNegative[val_]:=Module[{str},
	(*str=ToString[val,OutputForm];*)
	str=ToString[val,TeXForm];
	If[StringLength[str]>0 && StringMatchQ[StringTake[str,1],"-"],Return[True],Return[False]]
];

b7Tolatex={b7-> Subscript[b,7],d7-> Subscript[



\!\(\*OverscriptBox[\(b\), \(_\)]\), 7]};

ClearAll[CGTermList2TeX];
CGTermList2TeX[embed_,coefs_,cgterms_,r1_,r2_, align_]:=Module[
	{to, exp="", i, val, isFirst = True, terms=0, terminc,largeG,subG},

	largeG=embed[KeyLargeGroup];
	subG=embed[KeySubGroup];
	to=GetRepName[cgterms[[1,1]]];
	(*Print["r1=",r1,", r2=",r2,",to=",to];*)

	For[i=1,i<= Length[coefs],i++,
		If[coefs[[i]]==0,Continue[]];
		(*val=Simplify[coefs[[i]]/.b7Tolatex];
		val = Together[val];*)
		val = Together[ZToExp[Simplify[coefs[[i]]]]];

		If[Length[cgterms[[i]]]>=4, val = val /Sqrt[2];terminc = 2, terminc = 1];
		If[terms + terminc > 3, 
			(* new line if more than 4 terms. *)
			exp=exp<> " \\\\ \n & & "; terms = terminc, 
			terms = terms + terminc
		];

		If[isFirst == False && IsNegative[val]==False,exp=exp<> "+"];

		If[SameQ[val,-1], 
			exp = exp<> "-",
			If[SameQ[val,1]==False,
				exp=exp<>ToString[TeXForm[val]]
			]
		];

		exp=exp<> CGTerm2TeX[embed,cgterms[[i]],r1,r2];
		isFirst=False;
	];

	If[align,
		Return[Rep2TeX[subG,to]<>" &=& "<>exp],
		Return[Rep2TeX[subG,to]<>"="<>exp]
	];
];

(* Save the for r1*r2\[Rule]r3 *)
SaveCG[os_, embed_,r1_, r2_,r3_]:=Module[{i,j, align = True,subreps,terms, coefs,pos},
	(*If[Length[cg]>1,MyWriteLine[os, "\\begin{eqnarray*}"]; align = True, MyWriteLine[os, "\\["]];*)
	MyWriteLine[os, "\\begin{eqnarray*}"];
	(*Print["r1=",r1,",r2=",r2,",r3=",r3];*)
	terms=embed[r1,r2,GetRepWithSym[r3],KeyCGTerms];
	coefs=embed[r1,r2,r3,KeyCGCoefficient];
	subreps=embed[GetRepName[r3]];
	For[i=1,i<= Length[subreps],i++,
		pos={};
		For[j=1,j<= Length[terms],j++,
			If[GetRepName[terms[[j,1]]]==subreps[[i]],AppendTo[pos,j]];
		];

		MyWriteLine[os,CGTermList2TeX[embed,coefs[[pos]],terms[[pos]],r1,r2, align]];
		If[align && i < Length[subreps], MyWriteLine[os, "\\\\"]]
	];
	MyWriteLine[os, "\\end{eqnarray*}"];
	(*If[Length[cg]>1,MyWriteLine[os, "\\end{eqnarray*}"], MyWriteLine[os, "\\]"]];*)
];

(* Save all CG for r1 times r2 to the stream os. *)
ClearAll[SaveAllCG];
Options[SaveAllCG]={Skips->{}};
SaveAllCG[os_, r1_,r2_,embed_,opts:OptionsPattern[]]:=Module[
	{largeG, i,kronecker,r3,m, ch, cg, rep, eq, j, angle1, angle2,rr3,skips},
	largeG=embed[KeyLargeGroup];
	MyWriteLine[os,KroneckerEquation2TeX[largeG,r1,r2]];
	MyWriteLine[os, "\\begin{itemize}"];

	kronecker=Kronecker[largeG,r1,r2];
	If[Length[kronecker]==0,Return[]];

	skips=OptionValue[Skips];
	For[i=1,i<=Length[kronecker],i++,
		r3 = kronecker[[i]];
		If[MemberQ[skips,{r1,r2,r3}],
			Print[r1,"*",r2,"->",r3, " is skipped."];
			Continue[]
		];
		eq = EqsToTeX[largeG,r1, r2, r3];
		MyWriteLine[os, "\\item $", eq, "$:"];
		SaveCG[os, embed,r1,r2,r3];
	];

	MyWriteLine[os, "\\end{itemize}"];
];

WriteHeader[os_]:=Module[{},
	MyWriteLine[os, "\\documentclass[english]{article}"];
	MyWriteLine[os, "\\usepackage[T1]{fontenc}"];
	MyWriteLine[os, "\\usepackage[latin9]{inputenc}"];
	MyWriteLine[os];

	MyWriteLine[os, "\\makeatletter"];
	MyWriteLine[os, "\\newcommand{\\rep}[1]{\\mathbf{#1}}"];
	MyWriteLine[os, "\\newcommand{\\repx}[2]{{}_{#2}\\mathbf{#1}}"];
	(*MyWriteLine[os, "\\newcommand{\\subcg}[3]{\\big\\{ {#1}\\otimes{#2}\\big\\}^{}_{#3}}"];*)
	MyWriteLine[os, "\\newcommand{\\subcg}[3]{\\big\\{ \\repx{#1}{x}\\otimes\\repx{#2}{y}\\big\\}^{}_{#3}}"];
	
	MyWriteLine[os, "\\makeatother"];
	MyWriteLine[os, "\\usepackage{babel}"];
	MyWriteLine[os, "\\begin{document}"];
];

WriteTail[os_]:=MyWriteLine[os, "\\end{document}"];

ClearAll[WriteBody]
Options[WriteBody]=Join[{},Options[SaveAllCG]];
WriteBody[os_, prodList_, embed_,opts:OptionsPattern[]]:=Module[{i},
	For[i=1,i <= Length[prodList],i++,
		SaveAllCG[os, prodList[[i,1]], prodList[[i,2]], embed, FilterRules[{opts},Options[SaveAllCG]]];
	];
];

ClearAll[SaveToTexFile];
Options[SaveToTexFile]=Join[{},Options[WriteBody]];
SaveToTexFile[file_, prodList_, embed_,opts:OptionsPattern[]]:=Module[{os},
	os = OpenWrite[file];
	Print["Writing header"];
	WriteHeader[os];
	Print["Writing body"];
	WriteBody[os, prodList, embed, FilterRules[{opts},Options[WriteBody]]];
	Print["Writing tail"];
	WriteTail[os];
	Close[os];
];

