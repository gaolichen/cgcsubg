(* ::Package:: *)

Clear[GAPToMathematica];
GAPToMathematica[pstr_]:=StringReplace[pstr,{"["->"{","]"->"}",RegularExpression["E\\((\\d+)\\)"]->"Exp[2*Pi*I/$1]" }];

Clear[ReadGAP];
ReadGAP[fname_]:=Module[{f,str},
	f=OpenRead[fname];
	str=StringJoin[Map[StringJoin[GAPToMathematica[#],"\n"]&,ReadList[f,String]]];
	Close[f];
	Return[str];
];

ClearAll[ReadGAPDataFromFile];
ReadGAPDataFromFile[fname_]:=Module[{f},
	f=StringToStream[ReadGAP[fname]];
	Return[Read[f, Expression]]
];

ClearAll[LoadGroupFromFile];
LoadGroupFromFile[filename_, opts:OptionsPattern[]]:=Module[{f, ret, name, value,keys={}},
	f=StringToStream[ReadGAP[filename]];
	While[True, 
		name = Read[f, Expression];
		If[name == EndOfFile, Break[]];
		AppendTo[keys,name];
		ret[name]=Read[f,Expression];
	];

	ret["Keys"]=keys;
	Return[ret];
];
