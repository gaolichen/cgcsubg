(* ::Package:: *)

LoadPackage[file_]:=Get[FileNameJoin[{DirectoryName[$InputFileName],file}]];

LoadPackage["../psl27-common.m"];
LoadPackage["S4.m"];
LoadPackage["psl27-generators.m"];


On[Assert]
Assert[VerifyGroupInfo[Psl27]]

(* embedding of S4 in Psl27*)
ClearAll[Psl27ToS4];
Psl27ToS4[KeyLargeGroup]:=Psl27;
Psl27ToS4[KeySubGroup]:=S4Group;

Psl27ToS4[r_]:=DefaultEmbed[r, Psl27, S4Group]
Psl27ToS4["3"]:={"3_2"};
Psl27ToS4["3b"]:={"3_2"};
Psl27ToS4["6"]:={"1_0","2","3_1"};
Psl27ToS4["7"]:={"1_1","3_1","3_2"};
Psl27ToS4["8"]:={"2","3_1","3_2"};
Psl27ToS4[KeyTransformMatrix]:={
	{"3b","3_2",{{1,0,0},{0,0,1},{0,1,0}}}
};
Psl27ToS4[KeyCGImplicitSymmetric]:=True;

PslGenA["1"]:={{1}};
PslGenA["3"]:=pslA3/.b7ToEt;
PslGenA["3b"]:=pslA3b/.b7ToEt;
PslGenA["6"]:=pslA6/.b7ToEt;
PslGenA["7"]:=pslA7/.b7ToEt;
PslGenA["8"]:=pslA8/.b7ToEt;

PslGenB["1"]:={{1}};
PslGenB["3"]:=pslB3/.b7ToEt;
PslGenB["3b"]:=pslB3b/.b7ToEt;
PslGenB["6"]:=pslB6/.b7ToEt;
PslGenB["7"]:=pslB7/.b7ToEt;
PslGenB["8"]:=pslB8/.b7ToEt;

On[Assert]
VerifyEmbed[Psl27ToS4]
BuildCGTermsAll[Psl27ToS4]



Options[ClaculateAndPrintPslCG]=Join[{},Options[CalculateCG]];
ClaculateAndPrintPslCG[r1_,r2_,r3_, input_,opts:OptionsPattern[]]:=Module[{m,i,rr3, rules},
	rules = FilterRules[{opts}, Options[CalculateCG]];
	rules = Join[rules, {EquationSolver -> SolveCGEquations}];
	CalculateCG[r1,r2,r3,Psl27ToS4,input,{PslGenB}, rules];
	m=GetCGMultiplicity[Psl27,r1,r2,r3];
	If[m==1,
		PrintCG[r1,r2,r3,Psl27ToS4],
		For[i=1,i<= m,i++,
			rr3=SetRepMultiplicity[r3, i];
			PrintCG[r1,r2,rr3,Psl27ToS4]
		];
	];
];
