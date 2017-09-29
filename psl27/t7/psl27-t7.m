(* ::Package:: *)

<<"/users/gaolichen/gitroot/psl27cg/mpackage/cgframework.m";
<<"/users/gaolichen/gitroot/psl27cg/psl27-t7/t7cg.m";
<<"/users/gaolichen/gitroot/psl27cg/mpackage/psl27-generators-t7.m";
<<"/users/gaolichen/gitroot/psl27cg/mpackage/cyclicnumber.m";
<<"/users/gaolichen/gitroot/psl27cg/mpackage/psl27-common.m";

VerifyGroupInfo[Psl27]

(* embedding of T7 in Psl27*)
ClearAll[Psl27ToT7];
Psl27ToT7[KeyLargeGroup]:=Psl27;
Psl27ToT7[KeySubGroup]:=T7Group;

Psl27ToT7[r_]:=DefaultEmbed[r, Psl27, T7Group]
Psl27ToT7["3"]:={"3"};
Psl27ToT7["3b"]:={"3b"};
Psl27ToT7["6"]:={"3","3b"};
Psl27ToT7["7"]:={"1","3","3b"};
Psl27ToT7["8"]:={"1p","1pb","3","3b"};
Psl27ToT7[KeyTransformMatrix]:={};
Psl27ToT7[KeyCGImplicitSymmetric]:=False;
PslGenA["1"]:={{1}};
PslGenA["3"]:=pslA3;
PslGenA["3b"]:=pslA3b;
PslGenA["6"]:=pslA6;
PslGenA["7"]:=pslA7;
PslGenA["8"]:=pslA8;

PslGenB["1"]:={{1}};
PslGenB["3"]:=pslB3;
PslGenB["3b"]:=pslB3b;
PslGenB["6"]:=pslB6;
PslGenB["7"]:=pslB7;
PslGenB["8"]:=pslB8;

On[Assert]
VerifyEmbed[Psl27ToT7]
BuildCGTermsAll[Psl27ToT7]

ClearAll[ClaculateAndPrintPslT7CG];
Options[ClaculateAndPrintPslT7CG]=Join[{},Options[CalculateCG]];
ClaculateAndPrintPslT7CG[r1_,r2_,r3_, input_,opts:OptionsPattern[]]:=Module[{m,i,rr3},
	CalculateCG[r1,r2,r3,Psl27ToT7,input,{PslGenA},FilterRules[{opts}, Options[CalculateCG]]];
	m=GetCGMultiplicity[Psl27,r1,r2,r3];
	If[m==1,
		PrintCG[r1,r2,r3,Psl27ToT7],
		For[i=1,i<= m,i++,
			rr3=SetRepMultiplicity[r3, i];
			PrintCG[r1,r2,rr3,Psl27ToT7]
		];
	];
];

