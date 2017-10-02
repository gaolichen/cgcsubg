(* ::Package:: *)

LoadPackage[file_]:=Get[FileNameJoin[{DirectoryName[$InputFileName],file}]];
(*LoadPackage[file_]:= If[$InputFileName \[NotEqual] "",
	Print["input=",$InputFileName, ", file=",file];
	Print["notebook=",NotebookDirectory[], ", file=",file];
	Get[FileNameJoin[{DirectoryName[$InputFileName],file}]],
	Print["input=",$InputFileName, ", file=",file];
	Print["notebook=",NotebookDirectory[], ", file=",file];
	Get[FileNameJoin[{NotebookDirectory[],file}]];
];*)

LoadPackage["A4.m"];
LoadPackage["../psl27-common.m"];
LoadPackage["../../extractGroupData.m"];


(* S4 group.*)
(* Generators of S4: a^4=b^2=(ab)^3=e *)
(* First load S4 representations from GAP. *)
On[Assert]
S4GroupByGap=LoadGroupFromFile[FileNameJoin[{NotebookDirectory[],"s4.txt"}]];
keys=S4GroupByGap["Keys"];
Assert[keys[[3]]== "DimensionsOfReps"]
Assert[Last[keys]== "Generators"]
Assert[S4GroupByGap[keys[[3]]]== {1,3,2,3,1}];

(* Set generators*)
gens=S4GroupByGap[Last[keys]];
ClearAll[GS4A1, GS4B1];
GS4A1["1_0"]=gens[[5,1]];
GS4B1["1_0"]=gens[[5,2]];
GS4A1["1_1"]=gens[[1,1]];
GS4B1["1_1"]=gens[[1,2]];
GS4A1["2"]=gens[[3,1]];
GS4B1["2"]=gens[[3,2]];
GS4A1["3_1"]=gens[[4,1]];
GS4B1["3_1"]=gens[[4,2]];
GS4A1["3_2"]=gens[[2,1]];
GS4B1["3_2"]=gens[[2,2]];

(* verify 3_1 and 3_2 characters. *)
Assert[Tr[GS4A1["3_1"]]==-1]
Assert[Tr[GS4B1["3_1"]]==1]
Assert[Tr[GS4A1["3_2"]]==1]
Assert[Tr[GS4B1["3_2"]]==-1]

Off[Assert]
ClearAll[keys,gens,S4GroupByGap];

(* Verify S4 generators. *)
ClearAll[VerifyS4Generators];
VerifyS4Generators[GA_, GB_]:=Module[{a,b,ab,i,reps},
	reps={"1_0","1_1", "2","3_1", "3_2"};
	(*reps={"3_1"};*)
	For[i=1,i<= Length[reps],i++,
		a=GA[reps[[i]]];
		b=GB[reps[[i]]];
		ab=a.b;
		(*Print["b^2=",MatrixForm[FullSimplify[b.b]]];*)
		Assert[Simplify[a.a.a.a]== IdentityMatrix[Length[a]]];
		Assert[Simplify[b.b]== IdentityMatrix[Length[a]]];
		Assert[Simplify[ab.ab.ab]== IdentityMatrix[Length[a]]];
	];
];

On[Assert];
VerifyS4Generators[GS4A1,GS4B1]




(* The relation of a, b with A4 generators s, t are: s=a^2, t=ab. *)
(* Embedding of A4 in S4 is: 3_1=3, 3_2=3*)
ClearAll[GA4S1,GA4T1];
tmps1=Simplify[GS4A1["3_1"].GS4A1["3_1"]];
tmpt1=Simplify[GS4A1["3_1"].GS4B1["3_1"]];
MatrixForm[tmps1];
MatrixForm[tmpt1];

(* Find the unitary tranformation between GA4T and tmpt1 *)
eigen=Eigensystem[tmpt1];
eigen[[1]];
MatrixForm[eigen[[2]]];
matU=Simplify[Sqrt[3]Inverse[Transpose[eigen[[2]]]]];
(* the unitary transformaion is only determined up to two phases. *)
matU[[2]]=Exp[I*p1]*matU[[2]];
matU[[3]]=Exp[I*p2]*matU[[3]];
matUI=Simplify[ConjugateTranspose[matU],Assumptions->{p1\[Element]Reals,p2\[Element]Reals}];
(*Print["matU=",MatrixForm[matU], ", matUI=",MatrixForm[matUI]];*)

(* Verify that matU transform GA4T1 to GA4T, and GA4S1 to GA4S*)
On[Assert]
Assert[Simplify[matU.matUI]==IdentityMatrix[3]]
matT2=Simplify[matU.tmpt1.matUI];
Assert[Chop[N[matT2-GA4T["3"]]]==ConstantArray[0,{3,3}]];
prep={p1->2Pi/3,p2->-2Pi/3};
matS2=Simplify[matU.tmps1.matUI/.prep];
Assert[Chop[N[matS2-GA4S["3"]]]==ConstantArray[0,{3,3}]];
matU=Simplify[matU/.prep];
matUI=Simplify[matUI/.prep];
(*Print["For 3_1, matU=", 1/Sqrt[3],MatrixForm[Simplify[Sqrt[3]*matU]], " matUI=", 1/Sqrt[3],MatrixForm[Simplify[Sqrt[3]*matUI]]];*)
ClearAll[tmps1,tmpt1];

(* Do the same thing for 3_2. *)
tmps2=Simplify[GS4A1["3_2"].GS4A1["3_2"]];
tmpt2=Simplify[GS4A1["3_2"].GS4B1["3_2"]];
MatrixForm[tmps2];
MatrixForm[tmpt2];

eigen=Eigensystem[tmpt2];
eigen[[1]];
MatrixForm[eigen[[2]]];
matU2=Simplify[Sqrt[3]Inverse[Transpose[eigen[[2]]]]];
(* the unitary transformaion is only determined up to two phases. *)
matU2[[2]]=Exp[I*p1]*matU2[[2]];
matU2[[3]]=Exp[I*p2]*matU2[[3]];
matUI2=Simplify[ConjugateTranspose[matU2],Assumptions->{p1\[Element]Reals,p2\[Element]Reals}];

On[Assert]
Assert[Simplify[matU2.matUI2]==IdentityMatrix[3]]
matT2=Simplify[matU2.tmpt2.matUI2];
Assert[Chop[N[matT2-GA4T["3"]]]==ConstantArray[0,{3,3}]];
prep={p1->2Pi/3,p2->-2Pi/3};
matS2=Simplify[matU2.tmps2.matUI2/.prep];
Assert[Chop[N[matS2-GA4S["3"]]]==ConstantArray[0,{3,3}]];

matU2=Simplify[matU2/.prep];
matUI2=Simplify[matUI2/.prep];
(*Print["For 3_2, matU2=", 1/Sqrt[3],MatrixForm[Simplify[Sqrt[3]*matU2]], " matUI2=", 1/Sqrt[3],MatrixForm[Simplify[Sqrt[3]*matUI2]]];*)


(* find the generators of S4 in the same basis of GA4 *)
GS4A["3_1"]=Simplify[matU.GS4A1["3_1"].matUI];
GS4B["3_1"]=Simplify[matU.GS4B1["3_1"].matUI];
GS4A["3_2"]=Simplify[matU2.GS4A1["3_2"].matUI2];
GS4B["3_2"]=Simplify[matU2.GS4B1["3_2"].matUI2];

GS4A["1_0"]={{1}};
GS4B["1_0"]={{1}};

GS4A["1_1"]={{-1}};
GS4B["1_1"]={{-1}};

(*GS4A["2"]={{0,omega},{omega^2,0}};
GS4B["2"]=Inverse[GS4A["2"]].{{GA4T["1_1"][[1,1]],0},{0,GA4T["1_2"][[1,1]]}};*)
(* find 2 dimensional representation from 3_1*3_1 \[Rule] 2 *)
tmp1 = {x1,y1,z1};
tmp2 = {x2,y2,z2};
tmp3a = GS4A["3_1"].tmp1;
tmp4a = GS4A["3_1"].tmp2;
tmp3b = GS4B["3_1"].tmp1;
tmp4b = GS4B["3_1"].tmp2;
tmp5={DotA4[tmp1,tmp2,"3","3", "1_1"][[1]],DotA4[tmp1,tmp2, "3","3","1_2"][[1]]};
tmp6=Simplify[{DotA4[tmp3a,tmp4a,"3","3", "1_1"][[1]],DotA4[tmp3a,tmp4a,"3","3", "1_2"][[1]]}];
tmp7=Simplify[{DotA4[tmp3b,tmp4b,"3","3", "1_1"][[1]],DotA4[tmp3b,tmp4b, "3","3","1_2"][[1]]}];

GS4A["2"]=DecomposePolyMat[tmp6, tmp5];
GS4B["2"]=DecomposePolyMat[tmp7, tmp5];

(*Print["a=",MatrixForm[GS4A["3_1"]], ", b=",MatrixForm[GS4B["3_1"]]];*)
VerifyS4Generators[GS4A,GS4B]

On[Assert]
(* verify s=a^2, t=ab*)
Assert[Chop[N[GS4A["3_1"].GS4A["3_1"]-GA4S["3"]]]==ConstantArray[0,{3,3}]];
Assert[Chop[N[GS4A["3_1"].GS4B["3_1"]-GA4T["3"]]]==ConstantArray[0,{3,3}]];
Assert[Chop[N[GS4A["3_2"].GS4A["3_2"]-GA4S["3"]]]==ConstantArray[0,{3,3}]];
Assert[Chop[N[GS4A["3_2"].GS4B["3_2"]-GA4T["3"]]]==ConstantArray[0,{3,3}]];
Assert[Chop[N[GS4A["2"].GS4B["2"]-ArrayFlatten[{{GA4T["1_1"],0},{0,GA4T["1_2"]}}]]]==ConstantArray[0,{2,2}]];
Assert[Chop[N[GS4A["2"].GS4A["2"]-ArrayFlatten[{{GA4S["1_1"],0},{0,GA4S["1_2"]}}]]]==ConstantArray[0,{2,2}]];

(*Print["a=",MatrixForm[ToExp[GS4A["2"],ToTex\[Rule]True]],", b=",MatrixForm[ToExp[GS4B["2"],ToTex\[Rule]True]]];
Print["a=",1/3,MatrixForm[ToExp[3*GS4A["3_1"],ToTex\[Rule]True]],", b=",1/3,MatrixForm[ToExp[3*GS4B["3_1"],ToTex\[Rule]True]]];
Print["a=",1/3,MatrixForm[ToExp[3*GS4A["3_2"],ToTex\[Rule]True]],", b=",1/3,MatrixForm[ToExp[3*GS4B["3_2"],ToTex\[Rule]True]]];*)

ClearAll[eigen];
ClearAll[tmp1,tmp2,tmp3a,tmp4a,tmp3b,tmp4b,tmp5,tmp6,tmp7];


(* find the matrx to transform the conjugate of S4 generators to themselves*)
On[Assert]
s4ct2={{0,1},{1,0}};
s4ct3={{1,0,0},{0,0,1},{0,1,0}};
Assert[TestConjugateTransform[GS4A["2"], s4ct2]==ConstantArray[0,{2,2}]]
Assert[TestConjugateTransform[GS4B["2"], s4ct2]==ConstantArray[0,{2,2}]]

Assert[TestConjugateTransform[GS4A["3_1"], s4ct3]==ConstantArray[0,{3,3}]]
Assert[TestConjugateTransform[GS4B["3_1"], s4ct3]==ConstantArray[0,{3,3}]]

Assert[TestConjugateTransform[GS4A["3_2"], s4ct3]==ConstantArray[0,{3,3}]]
Assert[TestConjugateTransform[GS4B["3_2"], s4ct3]==ConstantArray[0,{3,3}]]
