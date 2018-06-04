(* ::Package:: *)

BeginPackage["ScalarMixedSpins`"]
ScalarMixedSpins::usage = "package for scalar and mixed ...
Designations(7): d t it p pp collectPP pTimes
Symbolic(9): expandSigma expandSigTimes HBasis basisH coordinates matrixTransform fullCoordinates(...) fullTransform(...) RemBasis
Traces(4): fastTr1 fastTr fastTr10 gramMatrix symGramMatrix
RhoGen(16): lastKP firstKP nextKP listKPs compoze swapToPerm generateGroup normolizeKP KPToExpr invariantKPsets squareInvariantKPsets KPsetsToExpr rhoGen invariantKPTsets listKPTs allKPs depsGen
Linerear algebra(10): RowSimplify RowReduceUpTo RowReduceUpToShow RowReduceInfo LinDeps ApplyLinDeps LinDependent LinIndependent DeleteReduced
ExplicitMatrices(13): getSi getSz getSp getSm getSx getSy KP scalar scalarSparse mixed mixedSparse explicit explicitSparse
Utilities(5):  FE foundQ firstFound printTo plusToList getInt"

(* ====== Utilities(5) ====== *)

foundQ::usage = "foundQ[expr,pattern] - analog MatchQ[], but return True if found any subexpr"
firstFound::usage = "firstFound[expr,pattern] - analog FirstPosition[], but return first founded subexpr (if not found return Missing[\"NotFound\"])"
printTo::usage = "printTo[file,expr] - \:0432\:044b\:0432\:043e\:0434 \:0438\:0437 expr \:043f\:0435\:0440\:0435\:043d\:0430\:043f\:0440\:0430\:0432\:043b\:0435\:0442 \:0432 \:0444\:0430\:0439\:043b, \:043d\:0430\:043f\:0440\:0438\:043c\:0435\:0440 \:0432 NUL(windows) \:0438\:043b\:0438 /dev/null(unix), \:043f\:043e\:0441\:043b\:0435 \:0447\:0435\:0433\:043e \:0432\:043e\:0437\:0432\:0440\:0430\:0449\:0430\:0435\:0442 \:0440\:0435\:0437\:0443\:043b\:044c\:0442\:0430\:0442 \:0432\:044b\:0440\:0430\:0436\:0435\:043d\:0438\:044f"
FE::usage = "(ForEach): expr1~FE~expr2 === expr2/@expr1"
plusToList::usage = "plusToList[expr] - return list of terms"
getInt::usage="getInt[sum] - get integer from sum"
Begin["`Private`"]

foundQ[expr_,pattern_]:=(FirstPosition[expr,pattern]//Head//SymbolName)!="Missing";
firstFound[expr_,pattern_]:=Module[{pos=FirstPosition[expr,pattern]},If[pos===Missing["NotFound"],pos,If[Length[pos]==0,expr,expr[[pos]]]]];
FE[list_,fun_]:=fun/@list;
plusToList[sum_]:=If[Head[sum]===Plus,List@@sum,{sum}];
getInt[sum_]:=Module[{tmp=sum//plusToList//First},If[Head[tmp]===Integer,tmp,0]];
myMonitor=Monitor;
fakeMonitor[body_,smth_]:=body;
printTo[file_,expr_]:=Module[
	{output = $Output,res},
	If[Length[Streams[file]]==0,
        $Output = OpenWrite[file]; (*"/dev/null" on unix or "NUL" on windows *)
        res=expr;
        Close[$Output];
        $Output = output
    ,
        $Output = Streams[file]; (*"/dev/null" on unix or "NUL" on windows *)
        res=expr;
        $Output = output
    ];
	res
]
SetAttributes[printTo,HoldAll]

End[]



(* ====== Designations(7) ====== *)
d::usage = "d[s_no_1,s_no_2] - scalar prodict of 2 Pauli matrices (orderless)"
t::usage = "t[s_no_1,s_no_2,s_no_3] - mixed prodict of 3 Pauli matrices"
it::isage = "it[a,b,c] == \[ImaginaryI] t[a,b,c]; use expr/.t[a_,b_,c_]:>-\[ImaginaryI] it[a,b,c]"
p::usage = "p[args] - my own product for d[] and t[] (and it[]) with order"
pp::usage = "pp[args] - my own product for d[] and t[] (and it[]) without order (orderless)"
SetAttributes[d,Orderless]
SetAttributes[pp,Orderless]
collectPP::usage = "collectPP[expr] - take expr without pp[], put d[] and t[] (and it[]) into pp[] (orderless) and collect them"
pTimes::usage = "pTimes[exprs...] - distribute and multiply(Times) exprs by p[] (with order)"

Begin["`Private`"]

pTimes[args___]:=(Expand/@p[args]//Distribute)//.
	p[aa___,Times[k_,smth__],bb___]:>p[aa,k,smth,bb]//.
	p[aa___,bb_/;(!MatchQ[bb,d[_,_]]&&!MatchQ[bb,t[_,_,_]]&&!MatchQ[bb,it[_,_,_]]) ,dd___]:>bb p[aa,dd]

collectPP[arg_]:=Collect[
	(arg pp[]//Expand)//.{
		d[a_,b_]pp[smth___]:>pp[d[a,b],smth],
		t[a_,b_,c_]pp[smth___]:>pp[t[a,b,c],smth],
		it[a_,b_,c_]pp[smth___]:>pp[it[a,b,c],smth]
	}
	,pp[___]
]

End[]



(* ====== Symbolic(9) ====== *)
expandSigma::usage = "expandSigma[expr] - return expanded expr without p[]; input d[_,_] and t[_,_,_] must be in p[]"
expandSigTimes::usage = "expandSigTimes[exprs...] - multiply exprs (by p[]) and then expand it by expandSigma[]"
(* tr[a,b] - deprecated *)
Hbasis::usage = "Hbasis[H,basis] - multiply left each vector from basis by H and return them"
basisH::usage = "basisH[basis,H] - multiply right each vector from basis by H and return them"
coordinates::usage = "coordinates[vector,basis] - return {coordinates,remainder}"
matrixTransform::usage = "matrixTransform[vectors,basis] - return {coordinates of vectors in the basis (matrix),remainders of vectors};"
fillCoordinates::usage = "...fullCoordinates[vector,basis] - return coordinates"
fullTransform::usage = "...matrixTransform[vectors,basis] - return coordinates of vectors in the basis (matrix);"
RemBasis::usage = "RemBasis[remainders] - return {dependencies,forbasis}"

Begin["`Private`"]

expandSigma=Function[g,Module[
	{f=g,debug=False,verbose=Count[g,d[_,_]|t[_,_,_],{0,Infinity}]>500,
		c,cc,a,b,e,x,y,z,i,j,k,smth,smth1,smth2,aux,\[Alpha],\[Beta],forremove={},\[Epsilon],\[Delta]},
	SetAttributes[\[Delta],Orderless]
	If[debug,Print["input: ",f]];
	If[foundQ[f,p[___,x_/;(!MatchQ[x,d[_,_]|t[_,_,_]]),___]],
		Throw[{"wrong input to expandSigma",f,
			FirstPosition[f,p[___,x_/;(!MatchQ[x,d[_,_]|t[_,_,_]]),___]]}],
		If[verbose,Print["checked"]]
	];

	(* \:0420\:0430\:0441\:043a\:0440\:044b\:0442\:0438\:0435 d,t *)
	While[foundQ[f,p[___,d[_,_],___]],
		x=Unique[\[Alpha]];  AppendTo[forremove,x];
		f=f/.p[a___,d[i_,j_],b___]:>p[a,c[i,x],c[j,x],b];
	];
	While[foundQ[f,p[___,t[_,_,_],___]],
		x=Unique[\[Alpha]];y=Unique[\[Alpha]];z=Unique[\[Alpha]]; AppendTo[forremove,x]; AppendTo[forremove,y]; AppendTo[forremove,z];
		f=f/.p[a___,t[i_,j_,k_],b___]:>\[Epsilon][x,y,z]p[a,c[i,x],c[j,y],c[k,z],b];
	];
	If[debug,Print["\:0420\:0430\:0441\:043a\:0440\:044b\:043b\:0438 d,t: ",f]];
	If[verbose,Print["\:0420\:0430\:0441\:043a\:0440\:044b\:043b\:0438 d,t"]];

	(* \:0421\:043e\:0440\:0442\:0438\:0440\:043e\:0432\:043a\:0430 *)
	f=f/.p[c[smth___],b___]:>p[cc[smth],b];
	While[foundQ[f,p[___,cc[___],c[___],___]],
		f=f/.p[a___,cc[smth1___],c[smth2___],b___]:>p[a,cc[smth1],aux[smth2],b];
		While[foundQ[f,p[___,cc[___],aux[___],___]],
			f=f/.p[a___,cc[i_,smth1___],aux[i_,smth2___],b___]:>p[a,cc[i,smth1,smth2],b];
			f=f/.p[a___,cc[i_,smth1___],aux[j_,smth2___],b___]:>p[a,aux[j,smth2],cc[i,smth1],b];
		];
		f=f/.p[aux[smth___],b___]:>p[cc[smth],b];
	];
	f=f/.p[smth___]:>pp[smth];
	If[debug,Print["\:041e\:0442\:0441\:043e\:0440\:0442\:0438\:0440\:043e\:0432\:0430\:043b\:0438: ",f]];
	If[verbose,Print["\:041e\:0442\:0441\:043e\:0440\:0442\:0438\:0440\:043e\:0432\:0430\:043b\:0438"]];

	(* \:0420\:0430\:0441\:043a\:0440\:044b\:0442\:0438\:0435 \:041f\:0430\:0443\:043b\:0438 \:0438 \:041b\:0435\:0432\:0438-\:0427\:0435\:0432\:0438\:0442\:044b *)
	While[foundQ[f,pp[___,cc[_,_,_,___],___]],
		x=Unique[\[Gamma]]; AppendTo[forremove,x];
		f=f/.pp[a___,cc[i_,\[Alpha]_,\[Beta]_,smth___],b___]:>\[Delta][\[Alpha],\[Beta]]pp[a,cc[i,smth],b]+I \[Epsilon][\[Alpha],\[Beta],x]pp[a,cc[i,x,smth],b]//Expand;
		f=f/.pp[a___,cc[i_],b___]:>pp[a,b];
		f=f/.pp[]:>1;
		f=f/.\[Epsilon][a_,b_,c_]^2:>6;
		f=f/.\[Epsilon][a_,b_,c_]\[Epsilon][a_,d_,e_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][a_,b_,c_]\[Epsilon][e_,a_,d_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][a_,b_,c_]\[Epsilon][d_,e_,a_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][c_,a_,b_]\[Epsilon][a_,d_,e_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][c_,a_,b_]\[Epsilon][e_,a_,d_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][c_,a_,b_]\[Epsilon][d_,e_,a_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][b_,c_,a_]\[Epsilon][e_,a_,d_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][b_,c_,a_]\[Epsilon][d_,e_,a_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][b_,c_,a_]\[Epsilon][a_,d_,e_]:>\[Delta][b,d]\[Delta][c,e]-\[Delta][b,e]\[Delta][c,d]//Expand;
	];
	If[debug,Print["\:0420\:0430\:0441\:043a\:0440\:044b\:043b\:0438 \:041f\:0430\:0443\:043b\:0438 \:0438 \:041b\:0435\:0432\:0438-\:0427\:0435\:0432\:0438\:0442\:044b: ",f]];
	If[verbose,Print["\:0420\:0430\:0441\:043a\:0440\:044b\:043b\:0438 \:041f\:0430\:0443\:043b\:0438 \:0438 \:041b\:0435\:0432\:0438-\:0427\:0435\:0432\:0438\:0442\:044b"]];

	(* \:0423\:043f\:0440\:043e\:0449\:0435\:043d\:0438\:0435 \:041a\:0440\:043e\:043d\:0435\:043a\:0435\:0440\:043e\:0432 *)
	While[foundQ[f,\[Delta][_,_]] (*&& index<100*),
		f=f/.\[Delta][a_,b_]\[Epsilon][b_,c_,d_]:>\[Epsilon][a,c,d];
		f=f/.\[Delta][a_,c_]\[Epsilon][b_,c_,d_]:>\[Epsilon][b,a,d];
		f=f/.\[Delta][a_,d_]\[Epsilon][b_,c_,d_]:>\[Epsilon][b,c,a];
		f=f/.\[Epsilon][a_,b_,c_]^2:>6;
		f=f/.\[Epsilon][a_,b_,c_]\[Epsilon][a_,d_,e_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][a_,b_,c_]\[Epsilon][e_,a_,d_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][a_,b_,c_]\[Epsilon][d_,e_,a_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][c_,a_,b_]\[Epsilon][a_,d_,e_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][c_,a_,b_]\[Epsilon][e_,a_,d_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][c_,a_,b_]\[Epsilon][d_,e_,a_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][b_,c_,a_]\[Epsilon][e_,a_,d_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][b_,c_,a_]\[Epsilon][d_,e_,a_]:>\[Epsilon][b,c,a]\[Epsilon][a,d,e];
		f=f/.\[Epsilon][b_,c_,a_]\[Epsilon][a_,d_,e_]:>\[Delta][b,d]\[Delta][c,e]-\[Delta][b,e]\[Delta][c,d]//Expand;
		f=f//.\[Delta][a_,b_]\[Delta][b_,c_]:>\[Delta][a,c];
		f=f/.\[Delta][a_,a_]:>3;
		f=f/.\[Delta][a_,b_]^2:>3;
		f=f/.\[Epsilon][a_,a_,b_]:>0;
		f=f/.\[Epsilon][a_,b_,a_]:>0;
		f=f/.\[Epsilon][b_,a_,a_]:>0;
		f=f/.\[Delta][a_,b_]pp[cc[i_,a_],smth___]:>pp[cc[i,b],smth];
		(*Print["debug: ",f];
		index++;*)
	];
	If[verbose,Print["\:0443\:043f\:0440\:043e\:0441\:0442\:0438\:043b\:0438 \:043a\:0440\:043e\:043d\:0435\:043a\:0435\:0440\:044b"]];
	If[debug,Print["\:0443\:043f\:0440\:043e\:0441\:0442\:0438\:043b\:0438 \:043a\:0440\:043e\:043d\:0435\:043a\:0435\:0440\:044b: ",f]];

	(* \:0412\:044b\:0434\:0435\:043b\:0435\:043d\:0438\:0435 d,t *)
	f=f//.pp[cc[i_,\[Alpha]_],cc[j_,\[Alpha]_],smth___]:>d[i,j]pp[smth];
	f=f//.\[Epsilon][\[Alpha]_,\[Beta]_,\[Gamma]_]pp[cc[i_,\[Alpha]_],cc[j_,\[Beta]_],cc[k_,\[Gamma]_],smth___]:>t[i,j,k]pp[smth];
	f=f/.t[x___/;!OrderedQ[{x}]]:>Signature[t[x]]Sort[t[x]];
	Remove@@forremove;
	If[verbose,Print["sigma expanded"]];
	If[debug,Print["sigma expanded: ",f]];
	If[FirstPosition[f,pp[__]]=!=Missing["NotFound"],Throw[{"internal error in expandSigma",f}]];
	f=f/.pp[]:>1;
	f//.t[a_,b_,c_]t[k_,l_,m_]:>(Det[{
 {d[a,k], d[b,k], d[c,k]},
 {d[a,l], d[b,l], d[c,l]},
 {d[a,m], d[b,m], d[c,m]}
}])//Expand
]];

tr[arg_]:=collectPP[arg]/.pp[]->1/.pp[smth___]->0

expandSigTimes[args___]:=expandSigma[pTimes[args]]

(* Coefficient based coordinates *)
coordinates1[vector_,basis_,bbasis_]:=Module[
	{vCoord={},i,j,coef,except,flag,coef2},
	For[i=1,i<=Length[basis],i++,
		coef=Coefficient[vector,bbasis[[i,1]]];
		AppendTo[vCoord,coef]
	];
	(*Print[Expand[vCoord.basis]," ",vCoord," ",basis];*)
	except=vector-Expand[vCoord.basis];
	If[except=!=0,
		vCoord={};
		flag=True;
		Monitor[
			For[i=1,i<=Length[basis],i++,
				coef=Coefficient[vector,bbasis[[i,1]]];
				For[j=2,j<=Length[bbasis[[i]]],j++,
					coef2=\:0421oefficient[vector,bbasis[[i,j]]];
					If[coef2!=coef,
						If[flag,Print["for vector ",vector];flag=False];
						Print["coefficient ",i," (",basis[[i]],") equals ",coef,
							" but for subcoefficient ",j," (",bbasis[[i,j]],") equals ",coef2];
						coef=0;
						Break[];
					]
				];
				AppendTo[vCoord,coef]
			],
			ProgressIndicator[i/Length[basis]]
		];
		except=vector-Expand[vCoord.basis];
		If[!flag,Print["except: ",vCoord," ",except]]
	];
	{vCoord,except/.pp->Times}
]

(*coordinates[vector_,basis_]:=coordinates1[collectPP[vector],collectPP/@basis,getBbasis[collectPP/@basis]]*)

(* Collect based coordinates *)
coordinates2[vector_,basis_,bbasis_,symbs_]:=Module[
	{eqs,eqss,except,res},
	eqs=Last[Reap[Collect[vector-Expand[basis.symbs],bbasis,Sow];]];
	(*Print[Expand[basis.symbs]-vector];
	Print[bbasis];
	Print[eqs];*)
	{except,eqss}=If[Length[eqs[[1]]]>Length[bbasis],
		{Last[eqs[[1]]]/.pp->Times,Delete[eqs[[1]],Length[eqs[[1]]]]},
		{0,eqs}
	];
	res=Solve[Union[eqss]==0,symbs];
	If[Length[res]==1,
		{symbs/.res[[1]],except},
		(*Print["can't decompose vector over basis: ",basis];*)
		Throw[{"newbasis",bbasis/.pp[x__]:>Times[x]},"newbasis"];
		{ConstantArray[0,Length[basis]],vector}
	]
]

coordinates[rawvector_,rawbasis_]:=Module[
	{symbs=Unique[ConstantArray["x",Length[rawbasis]]],(* \:0441\:0438\:043c\:0432\:043e\:043b\:043e\:0432 \:043f\:043e \:043a\:043e\:043b\:0438\:0447\:0435\:0441\:0442\:0432\:0443 \:044d\:043b\:0435\:043c\:0435\:043d\:0442\:043e\:0432 \:0431\:0430\:0437\:0438\:0441\:0430 *)
		vector=collectPP[rawvector/.t[a_,b_,c_]:>-I it[a,b,c]], (* \:043f\:043e\:0434\:0433\:043e\:0442\:043e\:0432\:043b\:0435\:043d\:043d\:044b\:0439 \:0432\:0435\:043a\:0442\:043e\:0440 *)
		basis=collectPP/@(rawbasis), (* \:043f\:043e\:0434\:0433\:043e\:0442\:043e\:0432\:043b\:0435\:043d\:043d\:044b\:0439 \:0431\:0430\:0437\:0438\:0441 *)
		bbasis (* \:043a\:0430\:0436\:0434\:044b\:0439 \:044d\:043b\:0435\:043c\:0435\:043d\:0442 \:043f\:043e\:0434\:0433\:043e\:0442\:043e\:0432\:043b\:0435\:043d\:043d\:043e\:0433\:043e \:0431\:0430\:0437\:0438\:0441\:0430 \:0440\:0430\:0437\:0431\:0438\:0432\:0430\:0435\:043c \:043d\:0430 \:043e\:0442\:0434\:0435\:043b\:044c\:043d\:044b\:0435 \:0441\:043b\:0430\:0433\:0430\:0435\:043c\:044b\:0435 (\:0442\:0438\:043f\:0430 plusToList) 
			\:0438 \:0432 \:043a\:0430\:0436\:0434\:043e\:043c \:0441\:043b\:0430\:0433\:0430\:0435\:043c\:043e\:043c \:043e\:0441\:0442\:0430\:0432\:043b\:044f\:0435\:043c \:0442\:043e\:043b\:044c\:043a\:043e pp[], \:0430 \:043f\:0440\:043e\:0447\:0438\:0435 \:043c\:043d\:043e\:0436\:0438\:0442\:0435\:043b\:0438 \:0443\:0434\:0430\:043b\:044f\:0435\:043c *)
	},
	bbasis=basis/.Plus->List/.{-x_:>x,a_ pp[smth___]:>pp[smth]}//Flatten;
	(Remove@@symbs; #)&[coordinates2[vector,basis,bbasis,symbs]]
]

matrixTransform[rawvectors_,rawbasis_]:=Module[
	{bbasis,matrix={},i,vector,coord,excepts={},except,
		basis=collectPP/@rawbasis,
		vectors=collectPP/@(rawvectors/.t[a_,b_,c_]:>-I it[a,b,c]),
		symbs=Unique[ConstantArray["x",Length[rawbasis]]]
	},
	bbasis=basis/.Plus->List/.{-x_:>x,a_ pp[smth___]:>pp[smth]}//Flatten;
	myMonitor[
		For[i=1,i<=Length[vectors],i++,
			vector=vectors[[i]](*printTo["NUL",expandSigTimes[H,basis[[i]]]]*);
			{coord,except}=coordinates2[vector,basis,bbasis,symbs];
			(*If[except=!=0,
				Print[i,")"(*,except*)];
			];*)
			AppendTo[excepts,except];
			AppendTo[matrix,coord]
		],
		ProgressIndicator[i/Length[vectors]]
	];
	Remove@@symbs;
	{Transpose[matrix](* \:0434\:043b\:044f \:043a\:0430\:0436\:0434\:043e\:0433\:043e \:0432\:0435\:043a\:0442\:043e\:0440\:0430 \:0435\:0433\:043e \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:044b - \:044d\:0442\:043e \:0441\:0442\:043e\:043b\:0431\:0435\:0446 *),excepts}
]

Hbasis[H_,basis_]:=Module[{i,vectors={}},
	Monitor[
		For[i=1,i<=Length[basis],i++,
			AppendTo[vectors,printTo["NUL",expandSigTimes[H,basis[[i]]]]];
		],
		ProgressIndicator[i/Length[basis]]
	];
	vectors
]

basisH[basis_,H_]:=Module[{i,vectors={}},
	Monitor[
		For[i=1,i<=Length[basis],i++,
			AppendTo[vectors,printTo["NUL",expandSigTimes[basis[[i]],H]]];
		],
		ProgressIndicator[i/Length[basis]]
	];
	vectors
]

RemBasis[remsin_]:=Module[{
		rems=remsin,
		forbasis={},
		deps={},
		list,b,depsrow,remstmp,tmp,c,i,j,newdeps,newtmp2
	},
	list=(If[#===0,+Infinity,#//plusToList//Length]&)/@rems;
	Monitor[
		myMonitor=fakeMonitor;
		While[Min[list]<Infinity,
										(*Print[list];*)
			b=Position[list,Min[list],{1}][[1,1]];
										(*Print[Position[list,Min[list],{1}]," b=",b];*)
			tmp=Catch[{depsrow,remstmp}=matrixTransform[rems,{rems[[b]]}],"newbasis"];
			If[Head[tmp]===List && Length[tmp]===2 && tmp[[1]]==="newbasis",
				(*Print[tmp];*)
				{depsrow,remstmp}=matrixTransform[rems,tmp[[2]]];
				(*Print[depsrow//MatrixForm];Print[tmp[[2]]//TableForm];*)
				(*Print[depsrow//TableForm];*)
				newdeps={}; newtmp2={};
				For[i=1,i<=Length[depsrow],i++,
					(*\:043e\:0442\:043d\:043e\:0440\:043c\:0438\:0440\:043e\:0432\:0430\:0442\:044c \:0441\:0442\:0440\:043e\:043a\:0438 \:043c\:0430\:0442\:0440\:0438\:0446\:044b depsrow \:043f\:043e \:043f\:0435\:0440\:0432\:044b\:043c \:043d\:0435\:043d\:0443\:043b\:0435\:0432\:044b\:043c \:044d\:043b\:0435\:043c\:0435\:043d\:0442\:0430\:043c (\:0432\:043c\:0435\:0441\:0442\:0435 \:0441 \:0441\:043e\:043e\:0442\:0432. \:0431\:0430\:0437\:0438\:0441\:043d\:044b\:043c\:0438 \:0432\:0435\:043a\:0442\:043e\:0440\:0430\:043c\:0438)*)
					c=Position[depsrow[[i]],_?(#=!=0&)][[2,1]];
					tmp[[2,i]]*=depsrow[[i,c]];
					depsrow[[i]]/=depsrow[[i,c]];
					(*\:0441\:0433\:0440\:0443\:043f\:043f\:0438\:0440\:043e\:0432\:0430\:0442\:044c \:043e\:0434\:0438\:043d\:0430\:043a\:043e\:0432\:044b\:0435 \:0441\:0442\:0440\:043e\:043a\:0438 \:0438 \:0441\:043e\:043e\:0442\:0432. \:0431\:0430\:0437\:0438\:0441\:043d\:044b\:0435 \:0432\:0435\:043a\:0442\:043e\:0440\:0430*)
					For[j=1,j<=Length[newdeps],j++,
						If[newdeps[[j]]===depsrow[[i]],
							newtmp2[[j]]+=tmp[[2,i]];
							Break[];
						]
					];
					If[j>Length[newdeps],
						AppendTo[newdeps,depsrow[[i]]];
						AppendTo[newtmp2,tmp[[2,i]]];
					]
				];
				(*Print[depsrow//MatrixForm];	Print[tmp[[2]]//TableForm];
				Print[newdeps//MatrixForm];	Print[newtmp2//TableForm];*)
				forbasis=Join[forbasis,newtmp2];
				deps=Join[deps,newdeps];
			,
				AppendTo[forbasis,rems[[b]]];
				AppendTo[deps,depsrow[[1]]];
			];
			rems=remstmp;
			list=(If[#===0,+Infinity,#//plusToList//Length]&)/@rems;
		];
		myMonitor=Monitor;
		,
		ProgressIndicator[Count[list,Infinity]/Length[list]]
	];
	{deps,forbasis}
]

End[]



(* ====== Linerear algebra(10) ====== *)

(* LinDeps ApplyLinDeps *)
RowSimplify::usage = "RowSimplify[matrix,step] - cycle { m[[;;i]]=m[[;;i]]//RowReduce//Simplify } , where i increases by step each iteration"
RowReduceUpTo::usage = "RowReduceUpTo[matrix,last_col] - RowReduce[matrix] and stop reducing at last coloumn"
RowReduceUpToShow::usage = "RowReduceUpToShow[matrix,last_col] - RowReduce[matrix] and stop reducing at last coloumn and show process"
RowReduceInfo::usage = "RowReduceInfo[m] - return {RowReduce[m],k} such that RowReduce[m]==k.m"
LinDeps::usage = "LinDeps[m] - RowReduceInfo[m][[2]] \:0438 \:043f\:043e\:043a\:0430\:0437\:044b\:0432\:0430\:0435\:0442 \:043f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:0438\:044f \:0442\:043e\:043b\:044c\:043a\:043e \:0434\:043b\:044f \:043d\:0443\:043b\:0435\:0432\:044b\:0445 \:0441\:0442\:0440\:043e\:043a RowReduce[m]"
LinIndependent::usage = "LinIndependent[m] - return indices of coloumns, which can be basis"
LinDependent::usage = "LinDependent[m] - return indices of coloumns, which are dependent from basis (which has only one '1')"
ApplyLinDeps::usage = "ApplyLinDeps[matrix,deps,dependent] - return matrix with removed dependencies (apply to rows)
ApplyLinDeps[matrix,deps] - automatically find dependent rows and return {matrix without dependencies, dependent}"
DeleteReduced::usage = "DeleteReduced[m] - delete zero rows"

Begin["`Private`"]

RowSimplify[inmatr_,step_]:=Module[{m=inmatr,i},
	Monitor[
		For[i=step,i<=Length[m],i+=step,
			m[[;;i]]=m[[;;i]]//RowReduce//Simplify
		],
		ProgressIndicator[i/Length[m]]
	];
	m//RowReduce//Simplify
];

RowReduceUpTo::overflow="`1` overflow `2`"
RowReduceUpTo[matr_,maxll_]:=Module[
	{m=matr,maxl=maxll,h=Length[matr],l=Length[matr[[1]]],i,j,curi=1,tmp},
	If[maxl>l,Message[RowReduceUpTo::overflow,maxl,l];maxl=l];
	Monitor[
		For[i=1;curi=1,i<=maxl&&curi<=h,i++, (* i -horizontal; curi - vertical *) 
			For[j=curi,j<=h,j++,
				If[m[[j,i]]!=0,Break[]]
			];
			If[j>h,Continue[]];
			If[j!=curi,tmp=m[[curi]]; m[[curi]]=m[[j]];m[[j]]=tmp];
			m[[curi]]/=m[[curi,i]];
			tmp=m[[;;,i]];
			tmp[[curi]]=0;
			If[Head[m[[1]]]===SparseArray && Mod[curi,100]===0,
				For[j=1,j<=h,j++,
					m[[j]] = SparseArray[m[[j]]-m[[curi]]*tmp[[j]]];
				];
			,
				For[j=1,j<=h,j++,
					m[[j]]-=m[[curi]]*tmp[[j]];
				];
			];
			curi++;
			(*Pause[1];*)
		],
		ProgressIndicator[i/maxl]
	];
	If[Head[m[[1]]]===SparseArray,
		For[j=1,j<=h,j++,
			m[[j]] = SparseArray[m[[j]]];
		];
	];
	m
]
RowReduceUpToShow[matr_,maxll_]:=Module[
	{m=matr,maxl=maxll,h=Length[matr],l=Length[matr[[1]]],i,j,curi=1,tmp},
	If[maxl>l,Message[RowReduceUpTo::overflow,maxl,l];maxl=l];
	Monitor[
		For[i=1;curi=1,i<=maxl&&curi<=h,i++,
			For[j=curi,j<=h,j++,
				If[m[[j,i]]=!=0,Break[]]
			];
			If[j>h,Continue[]];
			If[j!=curi,tmp=m[[curi]]; m[[curi]]=m[[j]];m[[j]]=tmp];
			m[[curi]]/=m[[curi,i]];
			tmp=m[[;;,i]];
			tmp[[curi]]=0;
			For[j=1,j<=h,j++,
				m[[j]]-=m[[curi]]*tmp[[j]];
			];
			curi++;
			Pause[1];
		],
		m//MatrixPlot
	];
	m
]

RowReduceInfo[m_]:=Module[{
	r=RowReduceUpTo[Transpose[Join[Transpose[m],IdentityMatrix[Length[m]]]],Length[m[[1]]]],
	l=Length[m[[1]]]
	},
	{r[[All,;;l]],r[[All,l+1;;]]}
]

LinDeps[m_]:=Module[{reduced,transform,i,res={},zero=ConstantArray[0,m[[1]]//Length]},
	{reduced,transform} = RowReduceInfo[m];
	For[i=1,i<=Length[m],i++,
		If[reduced[[i]]===zero,AppendTo[res,transform[[i]]]]
	];
	res
]

DeleteReduced[m_]:=Module[{
		i,
		zero=If[Head[m[[1]]]===SparseArray,
			SparseArray[{},{Length[m[[1]]]}]
		,
			ConstantArray[0,Length[m[[1]]]]
		]
	},
	For[i=1,i<=Length[m] && m[[i]]=!=zero,i++,42];
	Delete[m,{#}&/@Range[i,Length[m]] ]
]

LinDependent[m_]:=Module[{reduced=(*RowReduce[*)m(*]*),i,j,indep={}},
	For[i=1;j=1,i<=Length[m] && j<=Length[m[[1]]],j++,
		If[reduced[[i,j]]=!=0,
			AppendTo[indep,j];
			i++
		]
	];
	indep
]

LinIndependent[m_]:=Module[{reduced=(*RowReduce[*)m(*]*),i,j,imax=Length[m],jmax=Length[m[[1]]],dep={}},
	For[i=1;j=1,i<=imax && j<=jmax,j++,
		If[reduced[[i,j]]=!=0,
			i++
		,
			AppendTo[dep,j];
		]
	];
	For[j,j<=jmax,j++,
		AppendTo[dep,j];
	];
	dep
]

ApplyLinDeps[matri_,deps_,xdependent_]:=Module[{
		i,j,res={},matr=matri,
		trdeps=Transpose[deps],curdep,curdepv,usedDeps={},dependent=Sort[xdependent]
	},
	If[Length[matr]!=Length[trdeps],Throw["Length[matr]\[NotEqual]Length[trdeps]"]];
	For[i=1,i<=Length[dependent],i++, (* \:0441 \:043a\:0430\:0436\:0434\:044b\:043c \:0437\:0430\:0432\:0438\:0441\:0438\:043c\:044b\:043c \:0432\:0435\:043a\:0442\:043e\:0440\:043e\:043c *)
		curdepv=dependent[[i]]; (* Coloumn number *)
		If[Count[trdeps[[curdepv]],1]!=1 || Count[trdeps[[curdepv]],1]+Count[trdeps[[curdepv]],0]!=Length[trdeps[[curdepv]]],
			Throw[{"coloumn ",curdepv," is not clear"}]
		];
		curdep=FirstPosition[trdeps[[curdepv]],1][[1]]; (* Row number *)
		(*Print[curdep];*)
		If[foundQ[usedDeps,curdep],Throw[{"row ",curdep," is already used"}]];
		AppendTo[usedDeps,curdep]; (* \:043d\:043e\:043c\:0435\:0440\:0430 \:0438\:0441\:043f\:043e\:043b\:044c\:0437\:043e\:0432\:0430\:043d\:043d\:044b\:0445 \:0437\:0430\:0432\:0438\:0441\:0438\:043c\:043e\:0441\:0442\:0435\:0439 (\:0441\:0442\:0440\:043e\:043a) *)
		For[j=1,j<=Length[matr],j++,
			If[j!=curdepv,
				matr[[j]]-=matr[[curdepv]]*deps[[curdep,j]]
			]
		]
	];
	For[i=1,i<=Length[matr],i++,
		If[!foundQ[dependent,i],
			AppendTo[res,matr[[i]]]
		]
	];
	res
]

ApplyLinDeps[matr_,deps_]:=Module[{rdeps=RowReduce[deps],dependent},
	dependent=LinDependent[rdeps];
	(*Print[dependent];
	Print[MatrixForm[rdeps]];*)
	{ApplyLinDeps[matr,rdeps,dependent],dependent}
]

End[]



(* ====== rhoGen(16) ====== *)

lastKP::usage = "lastKP[number_of_pairs, number_of_spins] - return last KP"
firstKP::usage = "firstKP[number_of_pairs] - return first KP"
nextKP::usage = "nextKP[KP, number_of_spins] - return next KP"
listKPs::usage = "listKPs[number_of_pairs, number_of_spins] - return list of all KPs"
listKPTs::usage = "listKPTs[number_of_pairs, number_of_spins] - return list of all KPs transformed to expr multiplied by it[_._._]"
allKPs::usage = "allKPs[nspins] - return listKPTs[] or listKPs[]~FE~KPToExpr, where each vector uses all nspins spins"
compoze::usage = "compoze[first_permutation, second_permutation] - multiply two permutations"
swapToPerm::usage = "swapToPerm[swap, number_of_points] - construct permutation from swap"
generateGroup::usage = "generateGroup[list_of_permutations] - return group - list of all permutations which generated from specified permutations"
normolizeKP::usage = "normolizeKP[KP] - normolize KP (to standard form)"
KPToExpr::usage = "KPToExpr[KP] - converts KP to expr of d[] functions"
invariantKPsets::usage = "invariantKPsets[number_of_pairs, number_of_spins, group] - return list of sets_of_KPs, each set_of_KP is invariant with respect to group"
squareInvariantKPsets::usage = "squareInvariantKPsets[number_of_pairs, cluster] - 
return list of sets_of_KPs, each set_of_KP is invariant with respect to translation group of cluster"
invariantKPTsets::usage = "invariantKPTsets[number_of_pairs, number_of_spins, group] - like invariantKPsets, but KPs - exprs with it[_,_,_]"
KPsetsToExpr::usage = "KPsetsToExpr[group_of_KPs, name_of_param] - converst list of groups_of_KPs to expr in which each groups_of_KP is parametrized by param_i, 
and return {expr,list_of_params}"
rhoGen::usage = "rhoGen[number_of_spins, generators, names_of_params] - return {Rho,list_of_params}"
depsGen::usage = "depsGen[nspins,basis] - return dependencies-matrix based on (1,2)(3,4,5)-(1,3)(2,4,5)+(1,4)(2,3,5)-(1,5)(2,3,4)==0"

Begin["`Private`"];

lastKP=Function[{npair,npart},Module[
	{l=npart+1-2 npair,h=npart,llist={},hlist={}},
	While[l<h,
		llist=Append[llist,l++];
		hlist=Append[hlist,h--]
	];
	{llist,hlist}
]];

firstKP=Function[npair,Module[
	{l=1,h=1+npair,llist={},hlist={}},
	While[l<=npair,
		llist=Append[llist,l++];
		hlist=Append[hlist,h++]
	];
	{llist,hlist}
]];

nextKP=Function[{list,npart},Module[{
		llist=list[[1]],
		hlist=list[[2]],
		ll,
		used=Table[False,{x,1,npart}],
		dopUsed,
		newHlistElement,
		nextHlistElement,
		newLlistElement,
		nextLlistElement,
		i
	},
	ll=Length[llist];
	For[i=1,i<=ll,i++,used[[llist[[i]]]]=True];
	For[i=1,i<ll,i++,(*\:043f\:043e\:0441\:043b\:0435\:0434\:043d\:044e\:044e \:0446\:0438\:0444\:0440\:0443 \:043d\:0435 \:043a\:043b\:0430\:0434\:0435\:043c*)used[[hlist[[i]]]]=True];
	dopUsed=llist[[ll]]==npart-1;
	(*\:0433\:0435\:043d\:0435\:0440\:0438\:0440\:0443\:0435\:0442-\:0438\:043d\:0438\:0446\:0438\:0430\:043b\:0438\:0437\:0438\:0440\:0443\:0435\:0442 \:044d\:043b\:0435\:043c\:0435\:043d\:0442 \:0441\:0442\:0430\:0440\:0448\:0435\:0433\:043e \:0441\:043f\:0438\:0441\:043a\:0430,\:0412\:043e\:0437\:0432\:0440\:0449\:0430\:0435\:0442,\:0443\:0434\:0430\:0447\:043d\:043e \:043b\:0438 \:044d\:0442\:043e \:043f\:043e\:043b\:0443\:0447\:0438\:043b\:0441\:044c*)
	newHlistElement[n_]:=Module[{val},
		If[dopUsed&&n!=ll,
			val=llist[[n]]+1;
			While[val<npart&&used[[val]],val++];
			If[val>=npart,Return[False]];
			For[{},val<npart,val++,
				If[used[[val]],Continue[]];
				hlist[[n]]=val;
				used[[val]]=True;
				If[newHlistElement[n+1],Return[True]];
				used[[val]]=False;
			];
			Return[False];
		,
			val=llist[[n]]+1;
			While[val<=npart&&used[[val]],val++];
			If[val>npart,Return[False]];
			If[n==ll,
				hlist[[n]]=val;
				Return[True];
			];
			For[{},val<=npart,val++,
				If[used[[val]],Continue[]];
				hlist[[n]]=val;
				used[[val]]=True;
				If[newHlistElement[n+1],Return[True]];
				used[[val]]=False;
			];
			Return[False];
		]
	];
	nextHlistElement[n_]:=Module[{val},
		If[n==0,Return[nextLlistElement[ll]]];
		If[dopUsed,
			If[n==ll,Return[nextHlistElement[n-1]]];
			val=hlist[[n]];
			used[[val]]=False;
			val++;
			While[val<npart&&used[[val]],val++];
			If[val>=npart,Return[nextHlistElement[n-1]]];
			For[{},val<npart,val++,
				If[used[[val]],Continue[]];
				hlist[[n]]=val;
				used[[val]]=True;
				If[newHlistElement[n+1],Return[True]];
				used[[val]]=False;
			];
			Return[nextHlistElement[n-1]];
		,
			val=hlist[[n]];
			used[[val]]=False;
			val++;
			While[val<=npart&&used[[val]],val++];
			If[val>npart,Return[nextHlistElement[n-1]]];
			For[{},val<=npart,val++,
				If[used[[val]], Continue[]];
				hlist[[n]]=val;
				If[n==ll,Return[True]];
				used[[val]]=True;
				If[newHlistElement[n+1],Return[True]];
				used[[val]]=False;
			];
			Return[nextHlistElement[n-1]];
		]
	];
	newLlistElement[n_]:=Module[{},
		If[n==1,
			llist[[n]]=1;
			used[[1]]=True;
			If[ll==1,
				Return[newHlistElement[1]];(*\:0434\:043e\:043b\:0436\:043d\:043e \:0431\:044b\:0442\:044c True*)
			,
				Return[newLlistElement[n+1]];(*\:0434\:043e\:043b\:0436\:043d\:043e \:0431\:044b\:0442\:044c True*)
			];
		,
			If[n==ll,
				llist[[n]]=llist[[n-1]]+1;
				used[[llist[[n]]]]=True;
				dopUsed=llist[[ll]]==npart-1;
				Return[newHlistElement[1]];(*\:0434\:043e\:043b\:0436\:043d\:043e \:0431\:044b\:0442\:044c True*)
			,
				llist[[n]]=llist[[n-1]]+1;
				used[[llist[[n]]]]=True;
				Return[newLlistElement[n+1]];(*\:0434\:043e\:043b\:0436\:043d\:043e \:0431\:044b\:0442\:044c True*)
			]
		]
	];
	nextLlistElement[n_]:=Module[{val},
		If[n==0,Return[newLlistElement[1]]];
		val=llist[[n]];
		used[[val]]=False;
		val++;
		For[{},val<2*(n-ll)+npart,val++,
			llist[[n]]=val;
			If[n==ll,
				dopUsed=val==npart-1;
				used[[val]]=True;
				If[newHlistElement[1],Return[True]];
				used[[val]]=False;
			,
				used[[val]]=True;
				If[newLlistElement[n+1],Return[True]];
				used[[val]]=False;
			]
		];
		Return[nextLlistElement[n-1]];
	];
	nextHlistElement[ll];
	{llist,hlist}
]];

listKPs=Function[{npair,npart},Module[{stop=firstKP[npair],tmp=firstKP[npair],res={}},
	res=Append[res,tmp];
	For[tmp=nextKP[tmp,npart],tmp!=stop,tmp=nextKP[tmp,npart],
		res=Append[res,tmp]
	];
	res
]];
listKPTs[p_,n_]:=Module[{set=Range[n],KPset=Range[n-3],KPs},
	If[2p+3>n,Throw["wrong arguments for listKPTs"]];
	If[p==0,
		(*Print["p==0"];*)
		Subsets[set,{3}]~FE~(t@@#&)
	,
		(*Print["p!=0"];*)
		KPs=listKPs[p,n-3]~FE~KPToExpr;
		(*Print[KPs];*)
		Subsets[set,{3}]~FE~Function[{tt},
			(KPs/.MapThread[#1->#2&,{KPset,Complement[set,tt]}])t@@tt
		]//Flatten
	]
];

compoze[second_,first_]:=#/.(a_->b_):>(a->(b/.second))&/@first;

swapToPerm=Function[{list,length},Module[{res=<||>,a,b,i},
	If[Head[length]=!=Integer,Throw["swapToPerm: missed second argument"]];
	For[i=1,i<=Length[list],i++,
		a=list[[i]]/.((x_->y_):>x);
		b=list[[i]]/.((x_->y_):>y);
		res=Append[res,a->b];
		res=Append[res,b->a];
	];
	For[i=1,i<=length,i++,
		If[(res[i]//Head//SymbolName)=="Missing",
			res=Append[res,i->i]]
	];
	Normal[res]//Sort
]];

generateGroup=Function[listarg,Module[{list=listarg,set=<||>,res={},l,cur,tmp,tmp2,i,xl,xr},
	(*Print[list];*)
	For[i=1,i<=Length[list],i++,
		AppendTo[set,list[[i]]->i]
	];
	Monitor[
	While[Length[list]!=0,
		(*Print["\:043e\:0441\:0442\:0430\:043b\:043e\:0441\:044c(",list//Length,"):",list];
		Print["\:0440\:0430\:0441\:0441\:043c\:043e\:0442\:0440\:0435\:043d\:043e(",set//Length,"):",set];
		Print["\:0441\:0434\:0435\:043b\:0430\:043d\:043e(",res//Length,"):",res];*)
		cur=list[[1]];list=Delete[list,1];
		(*Print["current: " ,cur];*)
		AppendTo[res,cur];
		l=Length[res];
		For[i=1,i<=l,i++,
			(*Print[i,set];*)
			tmp=res[[i]];
			tmp2=compoze[tmp,cur]; (*Print["check ",tmp2];*)
			If[(set[tmp2]//Head//SymbolName)=="Missing",
				AppendTo[set,tmp2->{set[tmp],set[cur]}];AppendTo[list,tmp2](*;Print["Append ",tmp2]*)
			];
			tmp2=compoze[cur,tmp]; (*Print["check ",tmp2];*)
			If[(set[tmp2]//Head//SymbolName)=="Missing",
				AppendTo[set,tmp2->{set[cur],set[tmp]}];AppendTo[list,tmp2](*;Print["Append ",tmp2]*)
			];
		];
		(*Pause[1];*)
	];
	,ProgressIndicator[Length[res]/Length[set]]];
	(*Keys[set]//Sort*)
	set
]];

normolizeKP[{llist_,hlist_}]:=Module[{l=Length[llist],a,b,tmplist={},tllist={},thlist={},i},
	For[i=1,i<=l,i++,
		AppendTo[tmplist,{llist[[i]],hlist[[i]]}//Sort]
	];
	tmplist=tmplist//Sort;
	For[i=1,i<=l,i++,
		AppendTo[tllist,tmplist[[i,1]]];
		AppendTo[thlist,tmplist[[i,2]]];
	];
	{tllist,thlist}
];

KPToExpr[{llist_,hlist_}]:=Module[{res=1,ll=Length[llist],i},
	For[i=1,i<=ll,i++,
		res*=d[llist[[i]],hlist[[i]]]
	];
	res
];

KPSets=Function[{npair,npart,makeGroupSet},Module[{
		map(*\:0438\:0437 \:041a\:041f \:0432 \:2116 \:0433\:0440\:0443\:043f\:043f\:044b \:041a\:041f*)=<||>,
		listGrKP={},
		stopKP=firstKP[npair],
		stopSize=npart!/(2 npair)!/(npart-2 npair)!*(2 npair-1)!!,
		curKP=firstKP[npair],
		tmp,
		grKP,
		noGrKP,
		stop=0,
		stopLoop=Infinity (* \:043e\:0442\:043b\:0430\:0434\:043e\:0447\:043d\:043e\:0435 *)
	},
	(*Print[stopSize,"  ",gl];*)
	While[
		Label[loopStart];
		(*Print["loop start"];*)
		If[stop++>=stopLoop,Print["looped"];Return[looped]];
		If[(map[curKP]//Head//SymbolName)!="Missing",(* \:0442\:0435\:043a\:0443\:0449\:0430\:044f \:041a\:041f \:0443\:0436\:0435 \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f \:0432 \:043a\:0430\:043a\:043e\:0439-\:0442\:043e \:0433\:0440\:0443\:043f\:043f\:0435 *)
			(*Print["continue:",curKP];*)
			curKP=nextKP[curKP,npart]; (* \:043f\:0435\:0440\:0435\:0445\:043e\:0434\:0438\:043c \:043a \:0441\:043b\:0435\:0434\:0443\:044e\:0449\:0435\:0439 \:041a\:041f *)
			Goto[loopStart](*Continue[]*)
		];
		noGrKP=Length[listGrKP]+1; (* \:0435\:0435 \:043d\:043e\:043c\:0435\:0440 *)
		grKP=makeGroupSet[curKP];
		(AppendTo[map,#->noGrKP];&)/@grKP;
		AppendTo[listGrKP,grKP];
		curKP=nextKP[curKP,npart];
	
		(*Print["---"];
		Print[noGrKP,grKP,"   ",curKP,"=?=",stopKP];
		Print[map,Length[map]," ",stopSize];*)
	
		If[Length[map]>stopSize,Return[Error]];
		(*Print[Length[map]<stopSize&&curKP!=stopKP(*DoWhile*)];*)
		Length[map]<stopSize&&curKP!=stopKP(*DoWhile*)
	];
	listGrKP
]];
invariantKPsets[npair_,npart_,group_]:=Module[{
	makeGroupSet,
	gl=Length[group]
},
	makeGroupSet[curKP_]:=Module[{grKP,i,tmp,map=<||>},
		grKP={}; (* \:0441\:043e\:0437\:0434\:0430\:0435\:043c \:043d\:043e\:0432\:0443\:044e \:0433\:0440\:0443\:043f\:043f\:0443 \:041a\:041f *)
		For[i=1,i<=gl,i++, (* \:0433\:0435\:043d\:0435\:0440\:0438\:0440\:0443\:0435\:043c \:0433\:0440\:0443\:043f\:043f\:0443 *)
			tmp=(curKP/.group[[i]]);
			(*Print["before norm:",tmp,i," ",gl];*)
			tmp=tmp//normolizeKP;
			(*Print["after norm:",tmp,i," ",gl];*)
			(*If[stop++\[GreaterEqual]stopLoop,Print["looped"];Return[looped]];*)
			
			If[(map[tmp]//Head//SymbolName)=="Missing",
				AppendTo[map,tmp->True]; (* map - \:043a\:0430\:0436\:0434\:043e\:0439 \:041a\:041f \:0441\:043e\:043f\:043e\:0441\:0442\:0430\:0432\:043b\:044f\:0435\:0442\:0441\:044f \:043d\:043e\:043c\:0435\:0440 \:0433\:0440\:0443\:043f\:043f\:044b \:041a\:041f \:0432 \:043a\:043e\:0442\:043e\:0440\:043e\:0439 \:043e\:043d\:0430 \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f *)
				AppendTo[grKP,tmp]
			]
		];
		grKP
	];
	KPSets[npair,npart,makeGroupSet]
];
squareInvariantKPsets[npair_,pos2n_]:=Module[{
	makeGroupSet,
	npart=Max[pos2n],
	n2pos=ConstantArray[0,Max[pos2n]],
	imax=Length[pos2n],jmax=Length[pos2n[[1]]],
	i,j
},
	For[i=1,i<=Length[pos2n],i++,
		For[j=1,j<=Length[pos2n[[1]]],j++,
			If[pos2n[[i,j]]=!=0,n2pos[[pos2n[[i,j]]]]={i,j}]
		]
	];
	makeGroupSet[curKP_]:=Module[{grKP,tmp,iMin,jMin,map=<||>(*\:043d\:0430 \:0441\:0430\:043c\:043e\:043c \:0434\:0435\:043b\:0435 set*),ijTrans,iInv,jInv,ijSwap},
		grKP={}; (* \:0441\:043e\:0437\:0434\:0430\:0435\:043c \:043d\:043e\:0432\:0443\:044e \:0433\:0440\:0443\:043f\:043f\:0443 \:041a\:041f *)
		(* \:043a\:043f \:0437\:0430\:043f\:0438\:0441\:044b\:0432\:0430\:0435\:043c \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:0430\:043c\:0438 \:0430 \:043d\:0435 \:043d\:043e\:043c\:0435\:0440\:0430\:043c\:0438 *)
		ijTrans[kp_,il_,jl_]:=Module[{i,j,nkp,flag},
			(* \:0435\:0441\:043b\:0438 \:043d\:0430\:0447\:0430\:043b\:044c\:043d\:0430\:044f \:041a\:041f \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f \:0432 map, \:0442\:043e \:0432\:044b\:0445\:043e\:0434\:0438\:043c 
				for i=0, i\[LessEqual]il
					for j=0, j\[LessEqual]jl
						\:0434\:043e\:0431\:0430\:0432\:043b\:044f\:0435\:043c (\:0442\:0430\:043a, \:0447\:0442\:043e \:043a \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:0430\:043c \:043f\:0440\:0438\:0431\:0430\:0432\:043b\:044f\:0435\:043c {i,j}) \:0432 map
						\:0434\:043e\:0431\:0430\:0432\:043b\:044f\:0435\:043c (\:0442\:0430\:043a, \:0447\:0442\:043e \:043a \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:0430\:043c \:043f\:0440\:0438\:0431\:0430\:0432\:043b\:044f\:0435\:043c {i,j}) \:0432 grKP (\:0435\:0441\:043b\:0438 \:0432\:0441\:0435 \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:044b \:043f\:0435\:0440\:0435\:0432\:043e\:0434\:044f\:0442\:0441\:044f \:0432 \:043d\:0435\:043d\:0443\:043b\:0435\:0432\:044b\:0435 \:043d\:043e\:043c\:0435\:0440\:0430),
			*)
			If[(map[kp]//Head//SymbolName)==="Missing",
				For[i=0,i<=imax-il,i++,
					For[j=0,j<=jmax-jl,j++,
						nkp=kp/.{ii_Integer,jj_Integer}:>{ii+i,jj+j};
						If[(map[nkp]//Head//SymbolName)=!="Missing",Throw[Error]];
						AppendTo[map,nkp->True];
						flag=True;
						nkp=nkp/.{ii_Integer,jj_Integer}:>(If[pos2n[[ii,jj]]==0,flag=False];pos2n[[ii,jj]]);
						If[flag,AppendTo[grKP,nkp//normolizeKP]];
					]
				]
			]
		];
		jInv[kp_,il_]:=Module[{jl},
			(* \:0435\:0441\:043b\:0438 \:043d\:0430\:0447\:0430\:043b\:044c\:043d\:0430\:044f \:041a\:041f \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f \:0432 map, \:0442\:043e \:0432\:044b\:0445\:043e\:0434\:0438\:043c, \:0438\:043d\:0430\:0447\:0435 
				ijTrans \:041a\:041f,
				\:043d\:0430\:0439\:0442\:0438 \:043c\:0430\:043a\:0441\:0438\:043c\:0430\:043b\:044c\:043d\:0443\:044e \:0432\:0442\:043e\:0440\:0443\:044e \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:0443
				\:0443 \:043a\:0430\:0436\:0434\:043e\:0439 \:0442\:043e\:0447\:043a\:0438 \:0438\:043d\:0432\:0435\:0440\:0442\:0438\:0440\:043e\:0432\:0430\:0442\:044c \:0432\:0442\:043e\:0440\:0443\:044e \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:0443 \:0438 \:043f\:0440\:0438\:0431\:0430\:0432\:0438\:0442\:044c \:044d\:0442\:043e \:0447\:0438\:0441\:043b\:043e+1
				\:0438 \:043d\:043e\:0440\:043c\:043e\:043b\:0438\:0437\:043e\:0432\:0430\:0442\:044c \:043a\:0430\:043a nomalizeKP, \:0442\:043e\:043b\:044c\:043a\:043e \:0441\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:0435 \:0441\:043d\:0430\:0447\:0430\:043b\:0430 i, \:043f\:043e\:0442\:043e\:043c j - \:043f\:0440\:043e\:0432\:0435\:0440\:0438\:0442\:044c \:0441\:0442\:0430\:043d\:0434\:0430\:0440\:0442\:043d\:044b\:0439 nomalizeKP
				ijTrans \:041a\:041f,
			*)
			If[(map[kp]//Head//SymbolName)==="Missing",
				jl=Max[kp/.{i_Integer,j_Integer}:>j//Flatten];
				ijTrans[kp,il,jl];
				ijTrans[kp/.{i_Integer,j_Integer}:>{i,-j+1+jl}//normolizeKP,il,jl]
			]
		];
		iInv[kp_]:=Module[{il},
			(* \:0435\:0441\:043b\:0438 \:043d\:0430\:0447\:0430\:043b\:044c\:043d\:0430\:044f \:041a\:041f \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f \:0432 map, \:0442\:043e \:0432\:044b\:0445\:043e\:0434\:0438\:043c, \:0438\:043d\:0430\:0447\:0435 
				jInv \:041a\:041f,
				\:043d\:0430\:0439\:0442\:0438 \:043c\:0430\:043a\:0441\:0438\:043c\:0430\:043b\:044c\:043d\:0443\:044e \:043f\:0435\:0440\:0432\:0443\:044e \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:0443
				\:0443 \:043a\:0430\:0436\:0434\:043e\:0439 \:0442\:043e\:0447\:043a\:0438 \:0438\:043d\:0432\:0435\:0440\:0442\:0438\:0440\:043e\:0432\:0430\:0442\:044c \:043f\:0435\:0440\:0432\:0443\:044e \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:0443 \:0438 \:043f\:0440\:0438\:0431\:0430\:0432\:0438\:0442\:044c \:044d\:0442\:043e \:0447\:0438\:0441\:043b\:043e+1
				\:0438 \:043d\:043e\:0440\:043c\:043e\:043b\:0438\:0437\:043e\:0432\:0430\:0442\:044c \:043a\:0430\:043a nomalizeKP, \:0442\:043e\:043b\:044c\:043a\:043e \:0441\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:0435 \:0441\:043d\:0430\:0447\:0430\:043b\:0430 i, \:043f\:043e\:0442\:043e\:043c j
				jInv \:041a\:041f,
			*)
			If[(map[kp]//Head//SymbolName)==="Missing",
				il=Max[kp/.{i_Integer,j_Integer}:>i//Flatten];
				jInv[kp,il];
				jInv[kp/.{i_Integer,j_Integer}:>{-i+1+il,j}//normolizeKP,il]
			]
		];
		ijSwap[kp_]:=Module[{},
			(* iInv \:041a\:041f,
				\:0443 \:043a\:0430\:0436\:0434\:043e\:0439 \:0442\:043e\:0447\:043a\:0438 \:043f\:043e\:043c\:0435\:043d\:044f\:0442\:044c \:043c\:0435\:0441\:0442\:0430\:043c\:0438 \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:044b
				\:0438 \:043d\:043e\:0440\:043c\:043e\:043b\:0438\:0437\:043e\:0432\:0430\:0442\:044c \:043a\:0430\:043a nomalizeKP, \:0442\:043e\:043b\:044c\:043a\:043e \:0441\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:0435 \:0441\:043d\:0430\:0447\:0430\:043b\:0430 i, \:043f\:043e\:0442\:043e\:043c j
				iInv \:041a\:041f,
			*)
			iInv[kp];
			iInv[kp/.{i_Integer,j_Integer}:>{j,i}//normolizeKP];
		];
		tmp=curKP/.n_Integer:>n2pos[[n]]//normolizeKP;
		iMin=Min[tmp/.{i_Integer,j_Integer}:>i//Flatten];
		jMin=Min[tmp/.{i_Integer,j_Integer}:>j//Flatten];
		ijSwap[tmp/.{i_Integer,j_Integer}:>{i+1-iMin,j+1-jMin}];
		grKP
	];
	KPSets[npair,npart,makeGroupSet]
];

KPTsets[npair_,npart_,makeGroupSet_]:=Module[{
		map(*\:0438\:0437 \:041a\:041f \:0432 \:2116 \:0433\:0440\:0443\:043f\:043f\:044b \:041a\:041f*)=<||>,
		listGrKP={},
		grKP,
		KPTs=listKPTs[npair,npart],
		stopSize=(npart-3)!/(2 npair)!/((npart-3)-2 npair)!*(2 npair-1)!!*npart!/3!/(npart-3)!,
		curKP,
		curKPn=1,
		noGrKP,
		stop=0,
		stopLoop=Infinity
	},
	(*Print[stopSize,"  ",gl];*)
	curKP = KPTs[[curKPn]];
	(*Print[KPTs];*)
	While[
		Label[loopStart1];
		(*Print["loop start"];*)
		If[stop++>=stopLoop,Print["looped"];Return[looped]];
		If[(map[curKP]//Head//SymbolName)!="Missing",(* \:0442\:0435\:043a\:0443\:0449\:0430\:044f \:041a\:041f \:0443\:0436\:0435 \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f \:0432 \:043a\:0430\:043a\:043e\:0439-\:0442\:043e \:0433\:0440\:0443\:043f\:043f\:0435 *)
			(*Print["continue:",curKP];*)
			curKP = KPTs[[++curKPn]]; (* \:043f\:0435\:0440\:0435\:0445\:043e\:0434\:0438\:043c \:043a \:0441\:043b\:0435\:0434\:0443\:044e\:0449\:0435\:0439 \:041a\:041f *)
			Goto[loopStart1](*Continue[]*)
		];
		noGrKP=Length[listGrKP]+1; (* \:0435\:0435 \:043d\:043e\:043c\:0435\:0440 *)
		grKP=makeGroupSet[curKP];
		(AppendTo[map,#->noGrKP];&)/@grKP;
		AppendTo[listGrKP,grKP];
		curKP = KPTs[[++curKPn]];
	
		(*Print["---"];
		Print[noGrKP,grKP,"   ",curKPn,"=?=",Length[KPTs]];
		Print[map,Length[map]," ",stopSize];*)
	
		If[Length[map]>stopSize,Return[Error]];
		(*Print[Length[map]<stopSize&&curKP!=stopKP(*DoWhile*)];*)
		Length[map]<stopSize&&curKPn!=Length[KPTs](*DoWhile*)
	];
	listGrKP
];
invariantKPTsets[npair_,npart_,group_]:=Module[{
	makeGroupSet,
	gl=Length[group]
},
	makeGroupSet[curKP_]:=Module[{grKP,i,tmp,map=<||>},
		grKP={}; (* \:0441\:043e\:0437\:0434\:0430\:0435\:043c \:043d\:043e\:0432\:0443\:044e \:0433\:0440\:0443\:043f\:043f\:0443 \:041a\:041f *)
		For[i=1,i<=gl,i++, (* \:0433\:0435\:043d\:0435\:0440\:0438\:0440\:0443\:0435\:043c \:0433\:0440\:0443\:043f\:043f\:0443 *)
			tmp=(curKP/.group[[i]]);
			(*Print["before norm:",tmp,i," ",gl];*)
			tmp=tmp/.it[x___/;!OrderedQ[{x}]]:>Signature[it[x]]Sort[it[x]];
			(*Print["after norm:",tmp,i," ",gl];*)
			(*If[stop++\[GreaterEqual]stopLoop,Print["looped"];Return[looped]];*)
			
			If[(map[tmp]//Head//SymbolName)=="Missing",
				AppendTo[map,tmp->True]; (* map - \:043a\:0430\:0436\:0434\:043e\:0439 \:041a\:041f \:0441\:043e\:043f\:043e\:0441\:0442\:0430\:0432\:043b\:044f\:0435\:0442\:0441\:044f \:043d\:043e\:043c\:0435\:0440 \:0433\:0440\:0443\:043f\:043f\:044b \:041a\:041f \:0432 \:043a\:043e\:0442\:043e\:0440\:043e\:0439 \:043e\:043d\:0430 \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f *)
				AppendTo[grKP,tmp]
			]
		];
		grKP
	];
	KPTSets[npair,npart,makeGroupSet]
]
invariantKPTsets1[npair_,npart_,group_]:=Module[{
		gl=Length[group],
		map(*\:0438\:0437 \:041a\:041f \:0432 \:2116 \:0433\:0440\:0443\:043f\:043f\:044b \:041a\:041f*)=<||>,
		listGrKP={},
		grKP,
		KPTs=listKPTs[npair,npart],
		stopSize=(npart-3)!/(2 npair)!/((npart-3)-2 npair)!*(2 npair-1)!!*npart!/3!/(npart-3)!,
		curKP,
		curKPn=1,
		tmp,
		noGrKP,
		stop=0,
		stopLoop=Infinity,
		i,
		res=0
	},
	(*Print[stopSize,"  ",gl];*)
	curKP = KPTs[[curKPn]];
	(*Print[KPTs];*)
	While[
		Label[loopStart1];
		(*Print["loop start"];*)
		If[stop++>=stopLoop,Print["looped"];Return[looped]];
		If[(map[curKP]//Head//SymbolName)!="Missing",(* \:0442\:0435\:043a\:0443\:0449\:0430\:044f \:041a\:041f \:0443\:0436\:0435 \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f \:0432 \:043a\:0430\:043a\:043e\:0439-\:0442\:043e \:0433\:0440\:0443\:043f\:043f\:0435 *)
			(*Print["continue:",curKP];*)
			curKP = KPTs[[++curKPn]]; (* \:043f\:0435\:0440\:0435\:0445\:043e\:0434\:0438\:043c \:043a \:0441\:043b\:0435\:0434\:0443\:044e\:0449\:0435\:0439 \:041a\:041f *)
			Goto[loopStart1](*Continue[]*)
		];
		grKP={}; (* \:0441\:043e\:0437\:0434\:0430\:0435\:043c \:043d\:043e\:0432\:0443\:044e \:0433\:0440\:0443\:043f\:043f\:0443 \:041a\:041f *)
		noGrKP=Length[listGrKP]+1; (* \:0435\:0435 \:043d\:043e\:043c\:0435\:0440 *)
		For[i=1,i<=gl,i++, (* \:0433\:0435\:043d\:0435\:0440\:0438\:0440\:0443\:0435\:043c \:0433\:0440\:0443\:043f\:043f\:0443 *)
			tmp=(curKP/.group[[i]]);
			(*Print["before norm:",tmp,i," ",gl];*)
			tmp=tmp/.it[x___/;!OrderedQ[{x}]]:>Signature[it[x]]Sort[it[x]];
			(*Print["after norm:",tmp,i," ",gl];*)
			(*If[stop++\[GreaterEqual]stopLoop,Print["looped"];Return[looped]];*)
			
			If[(map[tmp]//Head//SymbolName)=="Missing",
				AppendTo[map,tmp->noGrKP]; (* map - \:043a\:0430\:0436\:0434\:043e\:0439 \:041a\:041f \:0441\:043e\:043f\:043e\:0441\:0442\:0430\:0432\:043b\:044f\:0435\:0442\:0441\:044f \:043d\:043e\:043c\:0435\:0440 \:0433\:0440\:0443\:043f\:043f\:044b \:041a\:041f \:0432 \:043a\:043e\:0442\:043e\:0440\:043e\:0439 \:043e\:043d\:0430 \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f *)
				AppendTo[grKP,tmp]
			]
		];
		AppendTo[listGrKP,Plus@@grKP];
		curKP = KPTs[[++curKPn]];
	
		(*Print["---"];
		Print[noGrKP,grKP,"   ",curKPn,"=?=",Length[KPTs]];
		Print[map,Length[map]," ",stopSize];*)
	
		If[Length[map]>stopSize,Return[Error]];
		(*Print[Length[map]<stopSize&&curKP!=stopKP(*DoWhile*)];*)
		Length[map]<stopSize&&curKPn!=Length[KPTs](*DoWhile*)
	];
	listGrKP
];
	
KPsetsToExpr=Function[{listGr,name},Module[{ngr,res=0,names={}},
	For[ngr=1,ngr<=(listGr//Length),ngr++,
		Module[{grName=Subscript[name, ngr],grRes=0,i,grKP=listGr[[ngr]]},
			For[i=1,i<=(grKP//Length),i++,
				grRes+=KPToExpr[grKP[[i]]];
			];
			res+=grName(grRes);
			AppendTo[names,grName];
		]
	];
	{res,names}
]];

rhoGen=Function[{npart,groupGens,names},Module[
	{(*names={a,b,c,d,e,f,g,h},*)npair=npart/2//Floor,i,res=0,group=generateGroup[groupGens],rnames={},lnames,lres},
	Print["group generated"];
	For[i=1,i<=npair,i++,
		{lres,lnames}=KPsetsToExpr[invariantKPsets[i,npart,group],names[[i]]];
		res+=lres;
		AppendTo[rnames,lnames];
		Print[i," pairs completed"];
	];
	{res,rnames//Flatten}
]];

allKPs[nspins_]:=If[Mod[nspins,2]!=0,
	listKPTs[(nspins-3)/2,nspins],
	listKPs[(nspins)/2,nspins]~FE~KPToExpr
];

depsGen[nspins_,basis_]:=Module[{
		i,j,k,l,
		deps={},
		dep,tmp,
		nbasis=Length[basis],
		cases={{1,2,3,4,5},{2,1,3,4,5},{3,1,2,4,5},{4,1,2,3,5}},
		subsets=Subsets[Range[nspins],{5}],
		case,
		compsubsets,
		KPs=allKPs[nspins-5],
		formula
	},
	Monitor[
	For[i=1,i<=Length[subsets],i++,
		For[j=1,j<=4,j++,
			case=subsets[[i]][[cases[[j]]]];
			case=d[case[[1]],case[[2]]]t[case[[3]],case[[4]],case[[5]]]
				-d[case[[1]],case[[3]]]t[case[[2]],case[[4]],case[[5]]]
				+d[case[[1]],case[[4]]]t[case[[2]],case[[3]],case[[5]]]
				-d[case[[1]],case[[5]]]t[case[[2]],case[[3]],case[[4]]];
			compsubsets = KPs/.MapThread[#1->#2&,{Range[nspins-5],Complement[Range[nspins],subsets[[i]]]}];
			For[k=1,k<=Length[compsubsets],k++,
				formula=Expand[case*compsubsets[[k]]]/.t[a_,b_,c_]t[x_,y_,z_]:>Det[{
 {d[a,x], d[b,x], d[c,x]},
 {d[a,y], d[b,y], d[c,y]},
 {d[a,z], d[b,z], d[c,z]}
}]//Expand//plusToList;
				dep=SparseArray[{},{Length[basis]}];(*ConstantArray[0,Length[basis]];*)
				For[l=1,l<=Length[formula],l++,
					(*Print[i," ",j," ",k," ",l," ",formula];*)
					(* \:043a\:0430\:0436\:0434\:044b\:0439 \:0447\:043b\:0435\:043d \:0444\:043e\:0440\:043c\:0443\:043b\:044b \:043f\:0440\:0435\:0432\:0440\:0430\:0442\:0438\:0442\:044c \:0432 +- \:0438\:043d\:0434\:0435\:043a\:0441 \:0431\:0430\:0437\:0438\:0441\:0430 *)
					If[MatchQ[formula[[l]],-_],
						dep[[FirstPosition[basis,-formula[[l]]][[1]]]]=-1
					,
						dep[[FirstPosition[basis,formula[[l]]][[1]]]]=1
					];
				];
				(*Print[i," ",j," ",k," ",dep.basis];*)
				AppendTo[deps,dep];
				(*If[Length[deps]\[GreaterEqual]Length[basis],Monitor[
					deps=RowReduce[deps];
					deps=DeleteReduced[deps];
				,"reducing"	
				]]*)
			]
		]
	],
	ProgressIndicator[i/Length[subsets]]];
	(*Print["return"];*)
	deps
];

End[]



(* ====== Traces(4) ====== *)

fastTr1::usage = "fastTr1[expr1,expr2] each expr \:0434\:043e\:043b\:0436\:0435\:043d \:044f\:0432\:043b\:044f\:0442\:044c\:0441\:044f \:0442\:043e\:043b\:044c\:043a\:043e \:043f\:0440\:043e\:0438\:0437\:0432\:0435\:0434\:0435\:043d\:0438\:0435\:043c \:0438\:0437 d[] \:0438 t[], \:043f\:0440\:0438\:0447\:0435\:043c t[] \:0434\:043e\:043b\:0436\:0435\:043d \:0432\:0441\:0442\:0440\:0435\:0447\:0430\:0442\:044c\:0441\:044f \:043d\:0435 \:0431\:043e\:043b\:044c\:0448\:0435 \:043e\:0434\:043d\:043e\:0433\:043e \:0440\:0430\:0437\:0430"
fastTr::usage = "fastTr[expr1,expr2] each expr \:043c\:043e\:0436\:0435\:0442 \:0431\:044b\:0442\:044c \:0441\:0443\:043c\:043c\:043e\:0439"
fastTr10::usage = "fastTr10[expr1,expr2] each expr \:043c\:043e\:0436\:0435\:0442 \:0431\:044b\:0442\:044c \:0441\:0443\:043c\:043c\:043e\:0439, \:043d\:043e \:043e\:0433\:0440\:0430\:043d\:0438\:0447\:0435\:043d\:0438\:0435: \:0432\:0441\:0435\:0433\:043e \:0441\:043f\:0438\:043d\:043e\:0432 \:043d\:0435 \:0431\:043e\:043b\:044c\:0448\:0435 14"
gramMatrix::usage = "gramMatrix[lhs_,rhs_] = matrix Tr[lhs[[i]],rhs[[j]]]"
symGramMatrix::usage = "symGramMatrix[vecs_] = matrix Tr[vecs[[i]],vecs[[j]]]"

Begin["`Private`"]

rmPair[expr_,num_]:=Module[{tmp=firstFound[expr,d[num,_]]},(*Print[tmp];*)
	If[tmp===Missing["NotFound"],{expr,Missing["NotFound"]},{expr/tmp,If[FirstPosition[tmp,num][[1]]==1,tmp[[2]],tmp[[1]]]}]]
(*
\:0435\:0441\:043b\:0438 \:043d\:0438 \:0440\:0430\:0437\:0443 \:043d\:0435 \:043d\:0430\:0448\:0435\:043b \[Rule] {lhs,rhs,start,0}
\:0435\:0441\:043b\:0438 \:043d\:0430\:0448\:0435\:043b 1 \:0440\:0430\:0437 \[Rule] {rhs/d[start,new_stop],lhs,new_stop,1} 
\:0435\:0441\:043b\:0438 \:043d\:0430\:0448\:0435\:043b 2 \:0440\:0430\:0437 \[Rule] {lhs/d[tmp,new_stop],rhs/d[start,tmp],new_stop,2} 
*)
rmChain=Function[{expr1x,expr2x,startx},Module[{expr1=expr1x,expr2=expr2x,start=startx,oldstart,count=0,tmp},
	While[start=!=Missing["NotFound"],
		oldstart=start;
		(*{expr2,start}=rmPair[expr2,start];*)
		tmp=firstFound[expr2,d[start,_]];
		{expr2,start}=If[tmp===Missing["NotFound"],
			{expr2,Missing["NotFound"]}
		  , {expr2/tmp,If[FirstPosition[tmp,start][[1]]==1,tmp[[2]],tmp[[1]]]}
		];
		{expr1,expr2}={expr2,expr1};
		count++;
	];
	{expr2,expr1,oldstart,count-1}
]];

timesToList[sum_]:=If[Head[sum]===Times,List@@sum,{sum}];
fastTr1=Function[{lhs2,rhs2},Module[{lhs1=timesToList[lhs2],rhs1=timesToList[rhs2],
		lhs=1,rhs=1,lcoef=1,rcoef=1,tmp1={},tmp2={},start,stop,used,tl,tr,count,i,accum
	},
									(*Print["lhs=",lhs1,"   rhs=",rhs1];*)
	(If[Head[#]===t, AppendTo[tmp1,#[[1]]]; AppendTo[tmp1,#[[2]]]; AppendTo[tmp1,#[[3]]];
	, If[Head[#]===d, AppendTo[tmp1,#[[1]]]; AppendTo[tmp1,#[[2]]];
		, lcoef*=#
	  ]
	];&)/@lhs1;
	tmp1=tmp1//Sort;
	(If[Head[#]===t, AppendTo[tmp2,#[[1]]]; AppendTo[tmp2,#[[2]]]; AppendTo[tmp2,#[[3]]];
	, If[Head[#]===d, AppendTo[tmp2,#[[1]]]; AppendTo[tmp2,#[[2]]];
		, rcoef*=#
	  ]
	];&)/@rhs1;
	tmp2=tmp2//Sort;
									(*Print[lcoef," ",rcoef];*)
	If[tmp2!=tmp1,
		(*Print["different sets"];*)
		0
	,
		(*Print["common sets"];*)
		lhs=(Times@@lhs1)/lcoef;
		rhs=(Times@@rhs1)/rcoef;
									(*Print["lhs=",lhs,"   rhs=",rhs];*)
		accum=1;
		tmp1=foundQ[lhs,t[_,_,_]];
		tmp2=foundQ[rhs,t[_,_,_]];
		If[tmp1&&!tmp2||tmp2&&!tmp1,Print["t and no t"];Return[0,Module]];
		If[tmp1&&tmp2,
			tl=firstFound[lhs,t[_,_,_]]; lhs/=tl;
			tr=firstFound[rhs,t[_,_,_]]; rhs/=tr;
			used={};
			For[i=1,i<=3,i++,
				start=tl[[i]];
				{lhs,rhs,stop,count} = rmChain[lhs,rhs,start];
				If[EvenQ[count](*\:0447\:0435\:0442\:043d\:044b\:0439*),
					If[!foundQ[tr,stop],
						Throw["internal error 1 in fastTr1 or its arguments"];
					,
						If[foundQ[used,FirstPosition[tr,stop][[1]]],
							Throw["inernal error 2 in fastTr1 or its arguments"];
						,
							AppendTo[used,FirstPosition[tr,stop][[1]]];
						]
					]
				,
					If[!foundQ[tl,stop],
						Throw["internal error 3 in fastTr1 or its arguments"];
					,
						Return[0,Module];
					]
				]
			];
			(*Print[used];*)
			accum=6 Signature[used];
		];
		(*Print["start search ",lhs," --- ",rhs];*)
		While[foundQ[lhs,d[_,_]],
			(*Print[lhs," --- ",rhs];*)
			tmp1=firstFound[lhs,d[_,_]];
			{lhs,rhs,stop,count}=rmChain[lhs,rhs,tmp1[[1]]];
			If[stop=!=tmp1[[1]] || OddQ[count],
				Print["start=",tmp1[[1]]," stop=",stop," count=",count];
				Throw["internal error 4 in fastTr1 or its arguments"];
			];
			accum*=3
		];
		accum*lcoef*rcoef
	]
]];
fastTr[lhs_,rhs_]:=(Expand/@p[lhs,rhs]//Distribute)/.p[l_,r_]:>If[
	Count[l,d[_,_]]!=Count[r,d[_,_]] || Count[l,t[_,_,_]]!=Count[r,t[_,_,_]],0,fastTr1[l,r]];
(*fastTr[lhs_,rhs_]:=(Expand/@p[lhs,rhs]//Distribute)/.p[1,1]->1/.{p[1,x_]->0,p[x_,1]->0}/.
	p[l_,r_]:>p[q[l]//.q[aa___,Times[k_,smth__],bb___]:>q[aa,k,smth,bb] , q[r]//.q[aa___,Times[k_,smth__],bb___]:>q[aa,k,smth,bb]]//.
	{p[lhs1_,q[aa___,bb_/;(!MatchQ[bb,d[_,_]]&&!MatchQ[bb,t[_,_,_]]) ,dd___]]:>bb p[lhs1,q[aa,dd]],
	p[q[aa___,bb_/;(!MatchQ[bb,d[_,_]]&&!MatchQ[bb,t[_,_,_]]) ,dd___],rhs1_]:>bb p[q[aa,dd],rhs1]}/.q[arg___]:>Times[arg]/.
	p[1,1]:>1/.{p[1,x_]:>0,p[x_,1]:>0}/.p[l_,r_]:>fastTr1[l,r]
*)
traceRules={
	p[pp[lsmth___ ,d[a1_,a2_]],
	pp[rsmth___,d[a1_,a2_]]]:>
	3 p[pp[lsmth],pp[rsmth]],
	p[pp[lsmth___ ,d[a1_,a2_],d[a3_,a4_]],
	pp[rsmth___,d[a2_,a3_],d[a4_,a1_]]]:>
	3 p[pp[lsmth],pp[rsmth]],
	p[pp[lsmth___ ,d[a1_,a2_],d[a3_,a4_],d[a5_,a6_]],
	pp[rsmth___,d[a2_,a3_],d[a4_,a5_],d[a6_,a1_]]]:>
	3 p[pp[lsmth],pp[rsmth]],
	p[pp[lsmth___ ,d[a1_,a2_],d[a3_,a4_],d[a5_,a6_],d[a7_,a8_]],
	pp[rsmth___,d[a2_,a3_],d[a4_,a5_],d[a6_,a7_],d[a8_,a1_]]]:>
	3 p[pp[lsmth],pp[rsmth]],
	p[pp[lsmth___ ,d[a1_,a2_],d[a3_,a4_],d[a5_,a6_],d[a7_,a8_],d[a9_,a10_]],
	pp[rsmth___,d[a2_,a3_],d[a4_,a5_],d[a6_,a7_],d[a8_,a9_],d[a10_,a1_]]]:>
	3 p[pp[lsmth],pp[rsmth]],
	p[pp[lsmth___ ,d[a1_,a2_],d[a3_,a4_],d[a5_,a6_],d[a7_,a8_],d[a9_,a10_],d[a11_,a12_]],
	pp[rsmth___,d[a2_,a3_],d[a4_,a5_],d[a6_,a7_],d[a8_,a9_],d[a10_,a11_],d[a12_,a1_]]]:>
	3 p[pp[lsmth],pp[rsmth]],
	p[pp[lsmth___ ,d[a1_,a2_],d[a3_,a4_],d[a5_,a6_],d[a7_,a8_],d[a9_,a10_],d[a11_,a12_],d[a13_,a14_]],
	pp[rsmth___,d[a2_,a3_],d[a4_,a5_],d[a6_,a7_],d[a8_,a9_],d[a10_,a11_],d[a12_,a13_],d[a14_,a1_]]]:>
	3 p[pp[lsmth],pp[rsmth]]
}
fastTr10[lhs_,rhs_]:=(Expand/@p[lhs,rhs]//Distribute)/.
	p[l_,r_]:>p[If[Head[l]===Times,pp@@l,pp[l]],If[Head[r]===Times,pp@@r,pp[r]]]/.
	p[l_,r_]:>Module[{
		ld=Count[l,d[_,_],{1}],
		lt=Count[l,t[_,_,_],{1}],
		rd=Count[r,d[_,_],{1}],
		rt=Count[r,t[_,_,_],{1}],
		lc,tmp=p[l,r]
	},
	If[
		ld!=rd || lt!=rt,
		0,
		If[Sort[Flatten[Cases[l,d[_,_]|t[_,_,_]]/.{d[a_,b_]:>{a,b},t[a_,b_,c_]:>{a,b,c}}]]!=
			Sort[Flatten[Cases[r,d[_,_]|t[_,_,_]]/.{d[a_,b_]:>{a,b},t[a_,b_,c_]:>{a,b,c}}]],
			0
		,
			If[lt!=0,
				fastTr1[Times@@l,Times@@r]
			,
				Print["fastTr10-begin: ",tmp];
				For[lc=1,lc<=ld,lc++,
					Print["   before: lc=",lc," ld=",ld," tmp=",tmp];
					tmp=(tmp//.traceRules[[lc]]);
					ld=Count[tmp[[1]],d[_,_],{1}];
					Print["   after:  lc=",lc," ld=",ld," tmp=",tmp];
				];
				Print["fastTr10-end: ",tmp];
				(*tmp=tmp//.traceRules[[1;;ld]];*)
				tmp/.pp[smth___]:>Times[smth]/.p[x_,y_]:>x y
			]
		]
	]]

gramMatrix[lhs_,rhs_]:=Module[{l},
	Monitor[Array[(l=#1;fastTr[lhs[[#1]],rhs[[#2]]])&,{lhs//Length,rhs//Length}],ProgressIndicator[l/Length[lhs]]]
]

symGramMatrix[lvecs_,rvecs_]:=Module[{
		m=ConstantArray[0,{lvecs//Length,rvecs//Length}],
		i,j,p=0
	},
	If[lvecs!=rvecs,Throw["lvecs\[NotEqual]rvecs"]];
	Monitor[
		For[i=1,i<=Length[lvecs],i++,
			For[j=i,j<=Length[lvecs],j++;p++,
				(*Print["Tr ",vecs[[i]]," * ",vecs[[j]]," = ",];*)
				m[[i,j]]=fastTr[lvecs[[i]],rvecs[[j]]]
			]
		]
	,ProgressIndicator[p/(Length[lvecs]*(Length[lvecs]+1)/2)]
	];
	For[i=2,i<=Length[lvecs],i++,
		For[j=1,j<i,j++,
			m[[i,j]]=m[[j,i]]
		]
	];
	m
]

symGramMatrix[lvecs_]:=symGramMatrix[lvecs,lvecs]

End[]


(* ::InheritFromParent:: *)
(*"package for scalar and mixed ...\nDesignations: d t p pp collectPP pTimes\nUtilities:  FE foundQ firstFound printTo\nExplicitMatrices: getSi getSz getSp getSm getSx getSy KP scalar mixed\nRhoGen: lastKP firstKP nextKP listKPs compoze swapToPerm generateGroup normolizeKP KPToExpr invariantKPsets KPsetsToExpr rhoGen\nmatrixTransform: expandSigma expandSigTimes\ngramMatrix: fastTr1 fastTr"*)


(* ::InheritFromParent:: *)
(*"invariantKPsets[number_of_pairs, number_of_spins, group] - return list of sets_of_KPs, each set_of_KP is invariant with respect to group"*)


(* ::InheritFromParent:: *)
(*"KPsetsToExpr[group_of_KPs, name_of_param] - converst list of groups_of_KPs to expr in which each groups_of_KP is parametrized by param_i, \nand return {expr,list_of_params}"*)


(* ====== ExplicitMatrices(13) ====== *)

getSi::usage = "getSi[l] - return identity matrix for spin l"
getSz::usage = "getSz[l] - return Sz matrix for spin l"
getSp::usage = "getSp[l] - return S+ matrix for spin l"
getSm::usage = "getSm[l] - return S- matrix for spin l"
getSx::usage = "getSx[l] - return Sx matrix for spin l"
getSy::usage = "getSy[l] - return Sy matrix for spin l"
KP::usage = "KP=KroneckerProduct"
scalar::usage = "scalar[l,N,{n1,n2}] - return scalar product of vectors of doubled spin matrices of spins n1 and n2; all number of spins = N, maximum spin = l"
mixed::usage = "mixed[l,N,{n1,n2,n3}] - return mixed product of vectors of doubled spin matrices of spins n1, n2 and n3; all number of spins = N, maximum spin = l"
scalarSparse::usage = "scalarSparse[l,N,{n1,n2}] - return scalar product of vectors of doubled spin sparse matrices of spins n1 and n2; 
all number of spins = N, maximum spin = l"
mixedSparse::usage = "mixedSparse[l,N,{n1,n2,n3}] - return mixed product of vectors of doubled spin sparse matrices of spins n1, n2 and n3; 
all number of spins = N, maximum spin = l"
explicit::usage = "explicit[l,N,expr] - transform expr to explicit matrix form"
explicitSparse::usage = "explicitSparse[l,N,expr] - transform expr to explicit sparse matrix form"

Begin["`Private`"]

getSi[l_]:=If[l==0,i,Array[If[#1==#2,1,0]&,{2l+1,2l+1}]]
getSz[l_]:=If[l==0,z,Array[If[#1==#2,l+1-#1,0]&,{2l+1,2l+1}]]
getSp[l_]:=If[l==0,p,Array[If[#1==#2-1,Sqrt[(l+(l+1-#1))(l-(l+1-#1)+1)],0]&,{2l+1,2l+1}]]
getSm[l_]:=If[l==0,m,Array[If[#1==#2+1,Sqrt[(l+(l+1-#2))(l-(l+1-#2)+1)],0]&,{2l+1,2l+1}]]
getSx[l_]:=If[l==0,x,(getSp[l]+getSm[l])/2]
getSy[l_]:=If[l==0,y,(getSp[l]-getSm[l])/2/I]
KP=KroneckerProduct;
scalar[l_,N_,{n1_,n2_}]:=Module[{si=getSi[l],sxyz={getSx[l],getSy[l],getSz[l]},i},
	If[n1>N||n2>N,Throw[{"numbers of spins ",n1,n2," more than max ",N}]];
	4*Sum[KP@@Array[If[#==n1||#==n2,sxyz[[i]],si]&,{N}],{i,1,3}]
]
mixed[l_,N_,{n1_,n2_,n3_}]:=Module[{si=getSi[l],sxyz={getSx[l],getSy[l],getSz[l]},i,j,k},
	If[n1>N||n2>N||n3>N,Throw[{"numbers of spins ",n1,n2,n3," more than max ",N}]];
	8*Sum[Signature[{i,j,k}]KP@@Array[Switch[#,n1,sxyz[[i]],n2,sxyz[[j]],n3,sxyz[[k]],_,si]&,{N}],{i,1,3},{j,1,3},{k,1,3}]
]
scalarSparse[l_,N_,{n1_,n2_}]:=Module[{si=SparseArray[getSi[l]],sxyz=SparseArray/@{getSx[l],getSy[l],getSz[l]},i},
	If[n1>N||n2>N,Throw[{"numbers of spins ",n1,n2," more than max ",N}]];
	4*Sum[KP@@Array[If[#==n1||#==n2,sxyz[[i]],si]&,{N}],{i,1,3}]//SparseArray
]
mixedSparse[l_,N_,{n1_,n2_,n3_}]:=Module[{si=SparseArray[getSi[l]],sxyz=SparseArray/@{getSx[l],getSy[l],getSz[l]},i,j,k},
	If[n1>N||n2>N||n3>N,Throw[{"numbers of spins ",n1,n2,n3," more than max ",N}]];
	8*Sum[Signature[{i,j,k}]KP@@Array[Switch[#,n1,sxyz[[i]],n2,sxyz[[j]],n3,sxyz[[k]],_,si]&,{N}],{i,1,3},{j,1,3},{k,1,3}]//SparseArray
]

explicit[l_,N_,expr_]:=collectPP[expr]/.{pp[]:>pp[KP@@Array[getSi[l]&,{N}]],d[i_,j_]:>scalar[l,N,{i,j}],t[i_,j_,k_]:>mixed[l,N,{i,j,k}]}/.pp->Dot
explicitSparse[l_,N_,expr_]:=collectPP[expr]/.{pp[]:>pp[KP@@Array[SparseArray[getSi[l]]&,{N}]],d[i_,j_]:>scalarSparse[l,N,{i,j}],t[i_,j_,k_]:>mixedSparse[l,N,{i,j,k}]}/.
	pp->Dot//SparseArray

End[]

EndPackage[]



































































