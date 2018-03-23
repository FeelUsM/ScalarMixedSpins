(* ::Package:: *)

BeginPackage["ScalarMixedSpins`"]
ScalarMixedSpins::usage = "package for scalar and mixed ...
Designations(7): d t it p pp collectPP pTimes
Utilities(5):  FE foundQ firstFound printTo plusToList
ExplicitMatrices(13): getSi getSz getSp getSm getSx getSy KP scalar scalarSparse mixed mixedSparse explicit explicitSparse
RhoGen(14): lastKP firstKP nextKP listKPs compoze swapToPerm generateGroup normolizeKP KPToExpr invariantKPsets KPsetsToExpr rhoGen invariantKPTsets listKPTs
Symbolic(7): expandSigma expandSigTimes getVectors coordinates matrixTransform fullCoordinates(...) fullTransform(...) fastTr1 fastTr gramMatrix(...) symGramMatrix(...)
Linerear algebra(2): RowReduceUpTo RowReduceUpToShow RowReduceInfo LinDeps ApplyLinDeps"

(*Global Symbols*)
d::usage = "d[s_no_1,s_no_2] - scalar prodict of 2 Pauli matrices (orderless)"
t::usage = "t[s_no_1,s_no_2,s_no_3] - mixed prodict of 3 Pauli matrices"
it::isage = "it[a,b,c] == \[ImaginaryI] t[a,b,c]; use expr/.t[a_,b_,c_]:>-\[ImaginaryI] it[a,b,c]"
p::usage = "p[args] - my own product for d[] and t[] with order"
pp::usage = "pp[args] - my own product for d[] and t[] without order (orderless)"
SetAttributes[d,Orderless]
SetAttributes[pp,Orderless]
collectPP::usage = "collectPP[expr] - take expr without pp[], put d[] and t[] and it[] into pp[] (orderless) and collect them"
pTimes::usage = "pTimes[exprs...] - distribute and multiply(Times) exprs by p[] (with order)"

foundQ::usage = "foundQ[expr,pattern] - analog MatchQ[], but return True if found any subexpr"
firstFound::usage = "firstFound[expr,pattern] - analog FirstPosition[], but return first founded subexpr (if not found return Missing[\"NotFound\"])"
printTo::usage = "printTo[file,expr] - \:0432\:044b\:0432\:043e\:0434 \:0438\:0437 expr \:043f\:0435\:0440\:0435\:043d\:0430\:043f\:0440\:0430\:0432\:043b\:0435\:0442 \:0432 \:0444\:0430\:0439\:043b, \:043d\:0430\:043f\:0440\:0438\:043c\:0435\:0440 \:0432 NUL(windows) \:0438\:043b\:0438 /dev/null(unix), \:043f\:043e\:0441\:043b\:0435 \:0447\:0435\:0433\:043e \:0432\:043e\:0437\:0432\:0440\:0430\:0449\:0430\:0435\:0442 \:0440\:0435\:0437\:0443\:043b\:044c\:0442\:0430\:0442 \:0432\:044b\:0440\:0430\:0436\:0435\:043d\:0438\:044f"
FE::usage = "(ForEach): expr1~FE~expr2 === expr2/@expr1"
plusToLost::usage = "plusToList[expr] - return list of terms"
myRowReduce::usage = "myRowReduce[m] - return {RowReduce[m],k} such that RowReduce[m]==k.m"

expandSigma::usage = "expandSigma[expr] - return expanded expr without p[]; input d[_,_] and t[_,_,_] must be in p[]"
expandSigTimes::usage = "expandSigTimes[exprs...] - multiply exprs (by p[]) and then expand it by expandSigma[]"
(* tr[a,b] - deprecated *)
coordinates::usage = "coordinates[vector,basis] - return {coordinates,remainder}; vector,basis and bbasis should Not be wrapped by pp[]"
matrixTransform::usage = "matrixTransform[vectors,basis] - return {coordinates of vectors in the basis (matrix),remainders of vectors}; 
vectors and basis should Not be wrapped by pp[]"
getVectors::usage = "getVectors[H,basis] - multiply each vector from basis by H(from left) and return them"

Begin["`Private`"]

ClearAttributes[RowReduce,Protected]
RowReduce::overflow="`1` overflow `2`"
RowReduce[matr_,maxll_]:=Module[
	{m=matr,maxl=maxll,h=Length[matr],l=Length[matr[[1]]],i,j,curi=1,tmp},
	If[maxl>l,Message[RowReduce::overflow,maxl,l];maxl=l];
	(*Monitor[*)
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
			(*Pause[1];*)
		(*],
		m//MatrixPlot*)
	];
	m
]
SetAttributes[RowReduce,Protected]

myRowReduce[m_]:=Module[{
	r=RowReduce[Transpose[Join[Transpose[m],IdentityMatrix[Length[m]]]],Length[m[[1]]]],
	l=Length[m[[1]]]
	},
	{r[[All,;;l]],r[[All,l+1;;]]}
]
foundQ[expr_,pattern_]:=(FirstPosition[expr,pattern]//Head//SymbolName)!="Missing"
firstFound[expr_,pattern_]:=Module[{pos=FirstPosition[expr,pattern]},If[pos===Missing["NotFound"],pos,If[Length[pos]==0,expr,expr[[pos]]]]]
FE[list_,fun_]:=fun/@list
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

plusToList[sum_]:=If[Head[sum]===Plus,List@@sum,{sum}]

(*coordinates[vector_,basis_]:=coordinates1[collectPP[vector],collectPP/@basis,getBbasis[collectPP/@basis]]*)

(* Collect based coordinates *)
coordinates2[vector_,basis_,bbasis_,symbs_]:=Module[
	{eqs,eqss,except,res},
	eqs=Last[Reap[Collect[Expand[basis.symbs]-vector,bbasis,Sow];]];
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
		Print["can't decompose vector over basis"];
		{ConstantArray[0,Length[basis]],vector}
	]
]

coordinates[rawvector_,rawbasis_]:=Module[
	{symbs=Unique[ConstantArray["x",Length[rawbasis]]],
		vector=collectPP[rawvector/.t[a_,b_,c_]:>-I it[a,b,c]],
		basis=collectPP/@(rawbasis),
		bbasis
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
	Monitor[
		For[i=1,i<=Length[vectors],i++,
			vector=vectors[[i]](*printTo["NUL",expandSigTimes[H,basis[[i]]]]*);
			{coord,except}=coordinates2[vector,basis,bbasis,symbs];
			If[except=!=0,
				Print[i,")"(*,except*)];
			];
			AppendTo[excepts,except];
			AppendTo[matrix,coord]
		],
		ProgressIndicator[i/Length[vectors]]
	];
	Remove@@symbs;
	{Transpose[matrix],excepts}
]

getVectors[H_,basis_]:=Module[{i,vectors={}},
	Monitor[
		For[i=1,i<=Length[basis],i++,
			AppendTo[vectors,printTo["NUL",expandSigTimes[H,basis[[i]]]]];
		],
		ProgressIndicator[i/Length[basis]]
	];
	vectors
]

End[]


(* ================================= \:0413\:0435\:043d\:0435\:0440\:0430\:0442\:043e\:0440 \:0420\:043e =============================================================== *)

lastKP::usage = "lastKP[number_of_pairs, number_of_spins] - return last KP"
firstKP::usage = "firstKP[number_of_pairs] - return first KP"
nextKP::usage = "nextKP[KP, number_of_spins] - return next KP"
listKPs::usage = "listKPs[number_of_pairs, number_of_spins] - return list of all KPs"
listKPTs::usage = "listKPTs[number_of_pairs, number_of_spins] - return list of all KPs transformed to expr multiplied by it[_._._]"
compoze::usage = "compoze[first_permutation, second_permutation] - multiply two permutations"
swapToPerm::usage = "swapToPerm[swap, number_of_points] - construct permutation from swap"
generateGroup::usage = "generateGroup[list_of_permutations] - return group - list of all permutations which generated from specified permutations"
normolizeKP::usage = "normolizeKP[KP] - normolize KP (to standard form)"
KPToExpr::usage = "KPToExpr[KP] - converts KP to expr of d[] functions"
invariantKPTsets::usage = "invariantKPTsets[number_of_pairs, number_of_spins, group] - like invariantKPsets, but KPs - exprs with it[_,_,_]"
invariantKPsets::usage = "invariantKPsets[number_of_pairs, number_of_spins, group] - return list of sets_of_KPs, each set_of_KP is invariant with respect to group"
KPsetsToExpr::usage = "KPsetsToExpr[group_of_KPs, name_of_param] - converst list of groups_of_KPs to expr in which each groups_of_KP is parametrized by param_i, 
and return {expr,list_of_params}"
rhoGen::usage = "rhoGen[number_of_spins, generators, names_of_params] - return {Rho,list_of_params}"

Begin["`Private`"]

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
		Subsets[set,{3}]~FE~(it@@#&)
	,
		(*Print["p!=0"];*)
		KPs=listKPs[p,n-3]~FE~KPToExpr;
		(*Print[KPs];*)
		Subsets[set,{3}]~FE~Function[{tt},
			(KPs/.MapThread[#1->#2&,{KPset,Complement[set,tt]}])it@@tt
		]//Flatten
	]
]

compoze[second_,first_]:=#/.(a_->b_):>(a->(b/.second))&/@first

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

generateGroup=Function[listarg,Module[{list=listarg,set=<||>,l,cur,tmp,tmp2,i},
	While[Length[list]!=0,
		(*Print["\:043e\:0441\:0442\:0430\:043b\:043e\:0441\:044c(",list//Length,"):",list," \:0441\:0434\:0435\:043b\:0430\:043d\:043e(",set//Length,"):",set];*)
		cur=list[[1]];list=Delete[list,1];
		If[(set[cur]//Head//SymbolName)!="Missing",Continue[]];
		AppendTo[set,cur->1];
		l=Length[set];
		For[i=1,i<=l,i++,
			(*Print[i,set];*)
			tmp=Keys[set][[i]];
			tmp2=compoze[tmp,cur];
			If[(set[tmp2]//Head//SymbolName)=="Missing",AppendTo[list,tmp2]];
			tmp2=compoze[cur,tmp];
			If[(set[tmp2]//Head//SymbolName)=="Missing",AppendTo[list,tmp2]];
		]
	];
	Keys[set]//Sort
]];

normolizeKP[{llist_,hlist_}]:=Module[{l=Length[llist],a,b,tmplist={},tllist={},thlist={},i},
	For[i=1,i<=l,i++,
		tmplist=Append[tmplist,{llist[[i]],hlist[[i]]}//Sort]
	];
	tmplist=tmplist//Sort;
	For[i=1,i<=l,i++,
		AppendTo[tllist,tmplist[[i,1]]];
		AppendTo[thlist,tmplist[[i,2]]];
	];
	{tllist,thlist}
]

KPToExpr[{llist_,hlist_}]:=Module[{res=1,ll=Length[llist]},
	For[i=1,i<=ll,i++,
		res*=d[llist[[i]],hlist[[i]]]
	];
	res
]

invariantKPTsets[npair_,npart_,group_]:=Module[{
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
invariantKPsets=Function[{npair,npart,group},Module[{
		gl=Length[group],
		map(*\:0438\:0437 \:041a\:041f \:0432 \:2116 \:0433\:0440\:0443\:043f\:043f\:044b \:041a\:041f*)=<||>,
		listGrKP={},
		grKP,
		stopKP=firstKP[npair],
		stopSize=npart!/(2 npair)!/(npart-2 npair)!*(2 npair-1)!!,
		curKP=firstKP[npair],
		tmp,
		noGrKP,
		stop=0,
		stopLoop=Infinity, (* \:043e\:0442\:043b\:0430\:0434\:043e\:0447\:043d\:043e\:0435 *)
		i,
		res=0
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
		grKP={}; (* \:0441\:043e\:0437\:0434\:0430\:0435\:043c \:043d\:043e\:0432\:0443\:044e \:0433\:0440\:0443\:043f\:043f\:0443 \:041a\:041f *)
		noGrKP=Length[listGrKP]+1; (* \:0435\:0435 \:043d\:043e\:043c\:0435\:0440 *)
		For[i=1,i<=gl,i++, (* \:0433\:0435\:043d\:0435\:0440\:0438\:0440\:0443\:0435\:043c \:0433\:0440\:0443\:043f\:043f\:0443 *)
			tmp=(curKP/.group[[i]]);
			(*Print["before norm:",tmp,i," ",gl];*)
			tmp=tmp//normolizeKP;
			(*Print["after norm:",tmp,i," ",gl];*)
			(*If[stop++\[GreaterEqual]stopLoop,Print["looped"];Return[looped]];*)
			
			If[(map[tmp]//Head//SymbolName)=="Missing",
				AppendTo[map,tmp->noGrKP]; (* map - \:043a\:0430\:0436\:0434\:043e\:0439 \:041a\:041f \:0441\:043e\:043f\:043e\:0441\:0442\:0430\:0432\:043b\:044f\:0435\:0442\:0441\:044f \:043d\:043e\:043c\:0435\:0440 \:0433\:0440\:0443\:043f\:043f\:044b \:041a\:041f \:0432 \:043a\:043e\:0442\:043e\:0440\:043e\:0439 \:043e\:043d\:0430 \:043d\:0430\:0445\:043e\:0434\:0438\:0442\:0441\:044f *)
				AppendTo[grKP,tmp]
			]
		];
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

End[]

(* =================== fastTr ====================================================== *)

fastTr1::usage = "fastTr1[expr1,expr2] each expr \:0434\:043e\:043b\:0436\:0435\:043d \:044f\:0432\:043b\:044f\:0442\:044c\:0441\:044f \:0442\:043e\:043b\:044c\:043a\:043e \:043f\:0440\:043e\:0438\:0437\:0432\:0435\:0434\:0435\:043d\:0438\:0435\:043c \:0438\:0437 d[] \:0438 t[], \:043f\:0440\:0438\:0447\:0435\:043c t[] \:0434\:043e\:043b\:0436\:0435\:043d \:0432\:0441\:0442\:0440\:0435\:0447\:0430\:0442\:044c\:0441\:044f \:043d\:0435 \:0431\:043e\:043b\:044c\:0448\:0435 \:043e\:0434\:043d\:043e\:0433\:043e \:0440\:0430\:0437\:0430"
fastTr::usage = "fastTr[expr1,expr2] each expr \:043c\:043e\:0436\:0435\:0442 \:0431\:044b\:0442\:044c \:0441\:0443\:043c\:043c\:043e\:0439"

Begin["`Private`"]

rmPair[expr_,num_]:=Module[{tmp=firstFound[expr,d[num,_]]},(*Print[tmp];*)
	If[tmp===Missing["NotFound"],{expr,Missing["NotFound"]},{expr/tmp,If[FirstPosition[tmp,num][[1]]==1,tmp[[2]],tmp[[1]]]}]]
(*
\:0435\:0441\:043b\:0438 \:043d\:0438 \:0440\:0430\:0437\:0443 \:043d\:0435 \:043d\:0430\:0448\:0435\:043b \[Rule] {lhs,rhs,start,0}
\:0435\:0441\:043b\:0438 \:043d\:0430\:0448\:0435\:043b 1 \:0440\:0430\:0437 \[Rule] {rhs/d[start,new_stop],lhs,new_stop,1} 
\:0435\:0441\:043b\:0438 \:043d\:0430\:0448\:0435\:043b 2 \:0440\:0430\:0437 \[Rule] {lhs/d[tmp,new_stop],rhs/d[start,tmp],new_stop,2} 
*)
rmChain=Function[{expr1x,expr2x,startx},Module[{expr1=expr1x,expr2=expr2x,start=startx,oldstart,count=0},
	While[start=!=Missing["NotFound"],
		oldstart=start;
		{expr2,start}=rmPair[expr2,start];
		{expr1,expr2}={expr2,expr1};
		count++;
	];
	{expr2,expr1,oldstart,count-1}
]];
fastTr1=Function[{lhs1,rhs1},Module[{lhs=lhs1,rhs=rhs1,tmp1,tmp2,start,stop,used,tl,tr,count,i},
	(*Print["lhs=",lhs,"   rhs=",rhs];*)
	tmp1=(List@@lhs//.{{a___,d[x_,y_],b___}:>{a,x,y,b},{a___,t[x_,y_,z_],b___}:>{a,x,y,z,b}}//Sort);
	tmp2=(List@@rhs//.{{a___,d[x_,y_],b___}:>{a,x,y,b},{a___,t[x_,y_,z_],b___}:>{a,x,y,z,b}}//Sort);
	If[tmp2!=tmp1,
		(*Print["different sets"];*)
		0
	,
		(*Print["common sets"];*)
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
						Throw["inernal error 1 in fastTr1 or its arguments"];
					,
						If[foundQ[used,FirstPosition[tr,stop][[1]]],
							Throw["inernal error 2 in fastTr1 or its arguments"];
						,
							AppendTo[used,FirstPosition[tr,stop][[1]]];
						]
					]
				,
					If[!foundQ[tl,stop],
						Throw["inernal error 3 in fastTr1 or its arguments"];
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
				Throw["inernal error 4 in fastTr1 or its arguments"];
			];
			accum*=3
		];
		accum
	]
]];
fastTr[lhs_,rhs_]:=(Expand/@p[lhs,rhs]//Distribute)/.p[1,1]->1/.{p[1,x_]->0,p[x_,1]->0}/.
	p[l_,r_]:>p[q[l]//.q[aa___,Times[k_,smth__],bb___]:>q[aa,k,smth,bb] , q[r]//.q[aa___,Times[k_,smth__],bb___]:>q[aa,k,smth,bb]]//.
	{p[lhs1_,q[aa___,bb_/;(!MatchQ[bb,d[_,_]]&&!MatchQ[bb,t[_,_,_]]) ,dd___]]:>bb p[lhs1,q[aa,dd]],
	p[q[aa___,bb_/;(!MatchQ[bb,d[_,_]]&&!MatchQ[bb,t[_,_,_]]) ,dd___],rhs1_]:>bb p[q[aa,dd],rhs1]}/.q[arg___]:>Times[arg]/.
	p[1,1]:>1/.{p[1,x_]:>0,p[x_,1]:>0}/.p[l_,r_]:>fastTr1[l,r]

End[]


(* ::InheritFromParent:: *)
(*"package for scalar and mixed ...\nDesignations: d t p pp collectPP pTimes\nUtilities:  FE foundQ firstFound printTo\nExplicitMatrices: getSi getSz getSp getSm getSx getSy KP scalar mixed\nRhoGen: lastKP firstKP nextKP listKPs compoze swapToPerm generateGroup normolizeKP KPToExpr invariantKPsets KPsetsToExpr rhoGen\nmatrixTransform: expandSigma expandSigTimes\ngramMatrix: fastTr1 fastTr"*)


(* ::InheritFromParent:: *)
(*"invariantKPsets[number_of_pairs, number_of_spins, group] - return list of sets_of_KPs, each set_of_KP is invariant with respect to group"*)


(* ::InheritFromParent:: *)
(*"KPsetsToExpr[group_of_KPs, name_of_param] - converst list of groups_of_KPs to expr in which each groups_of_KP is parametrized by param_i, \nand return {expr,list_of_params}"*)


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

















































