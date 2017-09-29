(* ::Package:: *)

(* numerical function. *)

phaseMap={};
phaseNames={};

Enumphase[basis_, curr_, phaseindex_]:=Module[{i},
	(*Print["curr=",curr, ", phaseindex=",phaseindex, ", basis=",basis];*)
	If[phaseindex>Length[basis],
		If[curr != 1 && curr != -1,
			AppendTo[phaseMap,{N[Arg[curr]], curphase}];
		];
		
		Return[];
	];

	For[i=-basis[[phaseindex,2]],i <= basis[[phaseindex,2]],i++,
		curphase[[phaseindex]]=i;
		Enumphase[basis,Simplify[curr*basis[[phaseindex,1]]^i],phaseindex + 1];
	];
];

BuildPhaseMap[basePhases_,names_]:=Module[{i,val=1},
	phaseMap={};
	phaseNames=names;
	curphase=ConstantArray[0,Length[basePhases]];
	Enumphase[basePhases, 1, 1];
	Clear[curphase];

	phaseMap=Sort[phaseMap, #1[[1]] < #2[[1]] &];
	Return[phaseMap];
];

NIntegerQ[n_]:=Chop[N[n]-Round[Re[N[n]]]]==0;

ZToExp[z_]:=Module[{a,nz,index,diff,ph,i,j},
	nz=N[z];
	If[Chop[Im[nz]]==0, Return[Re[z]]];
	a=Chop[Arg[nz]];
	If[IntegerQ[a*2/Pi], Return[z]];

	For[i=1,i<=Length[phaseMap],i++,
		diff = (a-phaseMap[[i,1]])/Pi*2;
		If[NIntegerQ[diff],
			ph=Product[phaseNames[[j]]^phaseMap[[i,2,j]],{j,1,Length[phaseMap[[i,2]]]}];
			Return[Simplify[Abs[z]]*Simplify[ph]*I^Round[diff]];
		];
	];

	Return[z]
];

ClearAll[ToExactPhase];
Options[ToExactPhase]={ToTex->False,Angle->(-1+I*Sqrt[7])/(2Sqrt[2]),ToNum->False};
ToExactPhase[ph_,opts:OptionsPattern[]]:=Module[{vb7,vd7,i,j,k,v,vomega,a,diff,basis,pos},
	v=N[ph];
	vb7=OptionValue[Angle];
	basis={vb7, b7,d7,Subscript[b, 7],ToExpression["\\Bar{b}_7",TeXForm]};
	(*vd7=(-1-I*Sqrt[7])/(2Sqrt[2]);*)
	vomega=(-1+I*Sqrt[3])/2;

	For[i=-7,i<= 7,i++,
		For[j=0,j<= 2,j++,
			a=N[Arg[vb7^i*vomega^j]];
			diff=(v-a)/Pi*2;
			(*Print["i=",i,", j=", j, ", diff=", diff];*)
			If[NIntegerQ[diff],
				If[OptionValue[ToNum], 
					Return[vb7^i*omg^j*I^Round[diff]]
				];
				If[i<0,pos=3, pos=2];
				If[OptionValue[ToTex],
					Return[basis[[pos+2]]^Abs[i]*\[Omega]^j*I^Round[diff]],
					Return[basis[[pos]]^Abs[i]*omg^j*I^Round[diff]]
				];
			];
		]
	];

	Return[Infinity]
];

ClearAll[ToExp];
SetAttributes[ToExp,Listable]
Options[ToExp]=Join[{},Options[ToExactPhase]];
ToExp[a_,opts:OptionsPattern[]]:=Module[{r,c,i,ph},
	If[Im[a]==0, Return[Re[a]]];
	c=Arg[a];
	If[IntegerQ[c*2/Pi], Return[a]];
	ph=ToExactPhase[c,FilterRules[{opts},Options[ToExactPhase]]];
	If[SameQ[ph, Infinity], 
		Return[a],
		Return[Simplify[Abs[a]]ph]
	]
];

ClearAll[N2Exact];
SetAttributes[N2Exact,Listable]
Options[N2Exact]=Join[{},Options[ToExactPhase]];
N2Exact[nn_,opts:OptionsPattern[]]:=Module[{c,ph,n},
	n=Chop[N[nn]];
	c=Arg[n];
	If[NIntegerQ[c*2/Pi], 
		Return[RootApproximant[n]]
	];

	ph=ToExactPhase[Arg[n],FilterRules[{opts},Options[ToExactPhase]]];
	If[SameQ[ph, Infinity], 
		Return[RootApproximant[n]],
		Return[RootApproximant[Abs[n]]ph]
	]
];

ClearAll[IsIntegerSqure];
SetAttributes[IsIntegerSqure,Listable]
IsIntegerSqure[n_]:=Round[Sqrt[N[n]]]^2-n==0;

ClearAll[SqrtQudraticForm];
SetAttributes[SqrtQudraticForm,Listable]
SqrtQudraticForm[q_]:=Module[{nq,aq,a,d,b2c,x,pol,t,sgn,p1,p2},
	nq=N[q];
	If[Chop[nq]==0, Return[0]];
	aq=RootReduce[q];
	If[QuadraticIrrationalQ[aq]==False, Return[ToRadicals[RootReduce[Sqrt[q]]]]];
	If[nq<0, sgn=I;aq=-aq,sgn=1];
	d=Denominator[aq];

	(* Now the numerator part is a+b*Sqrt[c], the minimal polynomail is x^2-2ax+a^2-b^2c*)
	pol = MinimalPolynomial[Numerator[aq],x];
	a = -Coefficient[pol,x]/2;
	b2c=(a^2-(pol/.{x->0}));
	(*Print["a=",a, ", b^2c=",b2c, ", d=",d,", pol=",pol];*)
	If[IsIntegerSqure[a^2-b2c]==False, Return[ToRadicals[RootReduce[Sqrt[q]]]]];
	t=Sqrt[a^2-b2c];
	p1=Sqrt[(a+t)/2]/Sqrt[d];
	p2=Sqrt[(a-t)/2]/Sqrt[d];
	If[Chop[N[(p1+p2)^2-aq]]==0, Return[sgn*(p1+p2)],Return[sgn*(p1-p2)]]
];

ClearAll[SqrtComplex];
SetAttributes[SqrtComplex,Listable]
SqrtComplex[n_]:=Module[{a,b,x2,y2,dlt,x,y,arg,pol},
	pol = MinimalPolynomial[n,x];
	If[Exponent[pol,x]>4, Return[Simplify[Sqrt[n]]]];

	a=Re[n];
	b=Im[n];
	dlt=Simplify[a^2+b^2];
	dlt=SqrtQudraticForm[dlt];
	x2=Simplify[(dlt+a)/2];
	y2=Simplify[(dlt-a)/2];
	x = SqrtQudraticForm[x2];
	y = SqrtQudraticForm[y2];
	arg=Arg[N[n]]/2;
	x *= Sign[Cos[arg]];
	y *= Sign[Sin[arg]];
	(*Print["a=",a,", b=", b, ", dlt=",dlt, ",x2=",x2, ",y2=",y2];*)
	Return[x + y*I];
];

SetAttributes[Reciprocal,Listable]
Reciprocal[n_]:=SimplifyNum2[RootReduce[1/n]];

(* check whether or not a number is rational or quadratic irational *)
ClearAll[NiceRealQ,NiceComplexQ];
SetAttributes[NiceRealQ,Listable]
NiceRealQ[n_]:= Element[n,Rationals]===True || QuadraticIrrationalQ[n]===True;
SetAttributes[NiceComplexQ,Listable]
NiceComplexQ[n_]:=NiceRealQ[Re[n]] && NiceRealQ[Im[n]];

ClearAll[SimplifyNum2]
SetAttributes[SimplifyNum2,Listable]
SimplifyNum2::CannotSimplify="SimplifyNum2 cannot simplify `1`.";
SimplifyNum2[n_]:=Module[{nn,pol,x,ord, n2,ret},
	nn = RootReduce[n];
	pol = MinimalPolynomial[nn,x];
	ord = Exponent[pol,x];
	If[ord<=2, Return[nn]];
	If[ord != 4 || Coefficient[pol,x^3] != 0, Message[SimplifyNum2::CannotSimplify, nn]; Return[ToRadicals[nn]]];

	n2 = ToRadicals[nn^2];
	If[Im[n2]==0, 
		ret=SqrtQudraticForm[n2],
		ret = SqrtComplex[n2]
	];

	If[Chop[N[ret-nn]] == 0, 
		Return[ret],
		Assert[Chop[N[ret+nn]]==0];
		Return[-ret]
	];
];
