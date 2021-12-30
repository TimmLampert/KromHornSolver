(* ::Package:: *)

(* :Title: KromHornSolver*)

(* :Authors: Timm Lampert, Anderson Nakano*)

(* :Summary: This package provides the background of our paper "Explaining Undecidability of First-Order Logic (FOL)" (2021). This paper explains why FOL cannot be decided by pattern detection within automated theorem proving (ATP).
It takes a definition of a splitting Turing machine (STM) plus an upper bound for the execution as input. It then goes through the following steps:
      Step 1: Generate the array for the steps of the STM and print its color diagram.
 Step 2: Translate the STM to clauses (with skolem functions) and to a pure FOL-formula (without skolem functions).
Step 3: Generate the deterministic tableau for the clauses and print its color diagram.
 Step 4: Translate the tableau proof to a pure FOL-formula encoding the corresponding proof in the NNF-calculus and print its color diagram.
Step 5: Check attempts to specify a loop-criterion.*)
(* Copyright: 2021 by Timm Lampert and Anderson Nakano.*)

(* :Context: KromHornSolver`*)

BeginPackage["KromHornSolver`"]

Unprotect[exists,forAll,A,B,x,y,xx,yy,uu,vv,zz,sat,oo,ii,jj,kk,and,or,
R,L,S,H,W,G,sk,P,
Q01,Q02,Q03,P1,P2,P3,P4,P5,P6,P7,P8,P9,P10,P11,P12,P13,
Faux0,FauxR,FauxL,Faux1A,Faux2,Faux3A,Faux4,Faux5A,Faux6,Faux7,
Faux8A,Faux9,Faux10A,Faux11,Faux12A,FauxS0,FauxS,
Rrule,Lrule,Wrule,Srule,STM,
tradiRules,tradi,untradiRules1,untradiRules2,untradi,normal,
freeAllQ,wf,indicesToSameLevel,varImp,varImpSort,
indicesToOriginalLevel,varExp,varExpSort,maxIndices,
qSeq,minIndices1,minIndices2,minIndices,matrix,
pn3,pn5,pn9,pn10,inpn3,inpn5,apn,pn,
CTM2Clauses,Clauses2FOL,STM2Clauses,folForm,
skolemize,maxIndicesForAll,toClauseNormalForm,prependBoolToLits,appendNoToLits,
negativeClauseQ,sbranch,notation,status,firstBranch,no,purelit,
unifyArgs,unifyLits,unify,singleUnification,
expansionStep,infExp,performInfStep,regularityQ,
firstIndex,skolemReduce,solve,printTableau,colorTableau,
litQ,litPairs,newAllExp1,newAllExp2,newAllExprs,newExpr,uniStep,printFinalExpr,colorExpr,
duplicateUKpairs,duplicateConjs,loopIsomo,sequenceQ,loopTableau,loopNNFAux,loopNNF,
iterate4,proofCheck]

Begin["`Private`"]
$RecursionLimit=10^10;


(*SECTION 0: PRINTING EVOLUTION OF STMs*)

(*The 4 rules of STMs:*)
Rrule[configuration_]:=Append[Rest[configuration],First[configuration]];
Lrule[configuration_]:=Prepend[Most[configuration],Last[configuration]];
Wrule[configuration_,symbol_]:=ReplacePart[configuration,1->symbol];
Srule[configuration_]:=Prepend[configuration,First[configuration]];

(*Generating the evolution with upper bound @steps as an array and printing its color diagram.*)
STM[{states_List, symbols_List, rules_List, q1_, qf_, tape_List},steps_]:=Module[{array,lastConfiguration,nextRule,nextConfiguration,lastConfigurationRest},
array = {Prepend[tape,q1]}; 
Do[lastConfiguration= Last[array];
If[First[lastConfiguration]===H, array={array,1};Break[],
(*nextRule=FirstCase[rules,rule_/;First[rule]===First[lastConfiguration]&&rule[[2]]===lastConfiguration[[2]]]; *)
nextRule=First[Cases[rules,rule_/;First[rule]===First[lastConfiguration]&&rule[[2]]===lastConfiguration[[2]]]];
lastConfigurationRest=Rest[lastConfiguration]; 
If[nextRule[[3]]==={R}, nextConfiguration=Rrule[lastConfigurationRest],
If[nextRule[[3]]==={L}, nextConfiguration=Lrule[lastConfigurationRest],
If[nextRule[[3]]==={S}, nextConfiguration=Srule[lastConfigurationRest],
nextConfiguration=Wrule[lastConfigurationRest,nextRule[[3,2]]]]]]; 
nextConfiguration=Prepend[nextConfiguration,Last[nextRule]]; 
array=Append[array,nextConfiguration]],
{steps}]; 
If[Last[array]=!=1,array={array,0};  Print["STM does not halt within ", steps, " steps."], Print["STM halts."]]; 
Print["The evolution of the STM up to ", steps, " steps as array: "]; Print[TableForm[First[array]]]; (*Print[TableForm[array]];*) 
Print["The evolution of the STM up to ", steps, " steps as color diagram: "];
ArrayPlot[First[array],ColorRules->{P->Red,Q01->LightPurple,Q02->LightBrown,Q03->LightGreen,P1->RGBColor[0.1,0.5,0.5],P2->RGBColor[0.9,0.5,0.5],P3->RGBColor[0.3,0.1,0.3],
P4->RGBColor[0.1,0.5,0.9],P5->RGBColor[0.9,0.5,0.1],P6->RGBColor[0.5,0.5,0.1],P7->RGBColor[0.5,0.1,0.5],P8->
RGBColor[0.5,0.5,0.9],P9->RGBColor[0.5,0.9,0.5],P10->RGBColor[0.1,0.3,0.3],P11->RGBColor[0.3,0.3,0.1],P12->RGBColor[0.1,0.9,0.5],H->Blue},ImageSize->50]];


(*SECTION 1: SOME AUXILIARY COMMANDS FROM THE DECIDER.WL PACKAGE*)

exists[{yvar__}, False] := False;
forAll[{xvar__}, False] := False;
exists[{yvar__}, True] := True;
forAll[{xvar__}, True] := True;
exists[{yvar__}, sat]:= sat;
forAll[{xvar__}, sat]:= sat;

tradiRules = {exists[{yvar_}, scope_] :> Exists[yvar, scope], forAll[{xvar_}, scope_] :> ForAll[xvar, scope],
              exists[{yvar__}, scope_] :> Exists[{yvar}, scope], forAll[{xvar__}, scope_] :> ForAll[{xvar}, scope]};
tradi[veexpression_]:= TraditionalForm[Replace[veexpression, tradiRules, {0, Infinity}]];
(*tradi[NNF] prints NNF in TraditionalForm. Each variable must be bound by a single quantifier, i.e. forAll[{x[1]},forAll[{x[2]},F[x[1],x[2]]]] instead of 
forAll[{x[1],x[2]]},F[x[1],x[2]]]. This command is only used in Print-commands within decide[FOLexpression].*)

untradiRules1 = {aa_*bb_ :> aa[bb], A -> forAll, E -> exists, ForAll -> forAll, Exists -> exists, "\[Exists]" -> exists, "\[ForAll]" -> forAll};
untradiRules2 = {(quantor:(forAll|exists))[yvar__, scope_] /; Not[ListQ[yvar]] :> quantor[{yvar}, scope], EllipticF :> F};
untradi[expression_]:= With[{rules2 = untradiRules2, rules1 = untradiRules1}, MapAll[# /. rules2&, (expression /. rules1)]];
(*untradi[FOL-expression] converts FOL-expressions in TraditionalForm or abbreviated form (A for ForAll, E for Exists) to FOL-expressions computed within the program.*)

normal[expression_]:= tradi[untradi[expression]];
(*normal[FOL-expression]. This command first applies untradi and then tradi. It converts FOL-expressions in abbreviated form to FOL-expressions in traditional form. It is not used within the program.*)

freeAllQ[expression_,list_]:= (Scan[If[FreeQ[expression, #], True, Return[False]]&, list] =!= False);
(*freeAllQ[expression, list] returns True if expression does not contain any member of list.*)

wf[expression_] := expression//. {(quantor:(forAll|exists))[var_, scope_] /; freeAllQ[scope, var] :> scope,
(quantor:(forAll|exists))[var_]:>Sequence[]}; 
(*wf[notwellformedFOL-expression] eliminates quantifiers with scopes that do not contain the bound variable. 
wf is necessary because simplifications such as applying ip-laws, simplifym7, BooleanMinimize, satReduce
or pn9 and pn10 may result in FOL-expressions that contain quantifiers with scopes that do not contain the bound variable. 
Example: simplifym7[forAll[{x},(f[x]||!f[x])&&exists[{y},g[y]]]]-> forAll[{x},exists[{y},g[y]]]; wf[forAll[{x},exists[{y},g[y]]]] -> exists[{y},g[y]].*)

indicesToSameLevel[var_Symbol]:= var;
indicesToSameLevel[var_[jj__]] := var[jj] //. varxy_[vv_][ww__] :> varxy[vv, ww];
(*indicesToSameLevel[variable] writes several indices preceding a variable in one bracket.
Example: x[1][2][3] -> x[1,2,3].*)

varImp[expr_,quantor_,con_]:=  Replace[expr, quantor[{var__}, quantor[{var2__}, scope_con]] :> 
    quantor[{var, var2}, scope], {0, Infinity}];
varImp[expr_]:=  Replace[expr, (quantor:(forAll|exists))[{var__}, (quantor:(forAll|exists))[{var2__}, scope_]] :> 
    quantor[{var, var2}, scope], {0, Infinity}];
(*varImp[FOLexpression] >implodes< bound variables.
Example: forAll[{x[1][1]},forAll[{x[1][2]}, f[x[1][1],x[1][2]]]] && exists[{y[1]},exists[{y[2]}, f[y[1],y[2]]]] -> 
forAll[{x[1][1],x[1][2]},f[x[1][1],x[1][2]]]&&exists[{y[1],y[2]},f[y[1],y[2]]].
Indices are not imploded.*)

varImpSort[expr_,quantor_,con_]:=  
    Module[{varcmp, sorted},
	  Replace[varImp[expr,quantor,con], quantor[vars_/; (Length[vars]>1), scope_con] :> 
       (varcmp = Map[{#, Length[DeleteDuplicates[Position[scope, #][[All, 1]]]]}&, vars];
        sorted = Sort[varcmp, If[#1[[2]]=== #2[[2]], First[#1]< First[#2], #1[[2]]> #2[[2]]]&];
       quantor[Map[First[#]&, sorted], scope]), {0, Infinity}]];
varImpSort[expr_]:=  
    Module[{varcmp, sorted},
	  Replace[varImp[expr], (quantor:(forAll|exists))[vars_/; (Length[vars]>1), scope_] :> 
       (varcmp = Map[{#, Length[DeleteDuplicates[Position[scope, #][[All, 1]]]]}&, vars];
        sorted = Sort[varcmp, If[#1[[2]]=== #2[[2]], First[#1]< First[#2], #1[[2]]> #2[[2]]]&];
       quantor[Map[First[#]&, sorted], scope]),{0, Infinity}]];
(*varImpSort[FOLexpression] implodes and sorts bound variables according to 
the number of their occurrences in subexpressions of the scope of the respective quantifier.
Example: forAll[{x[1],x[2]},(f[x[1]] && g[x[2]]) ||(exists[{y[1],y[2]}, j[y[2],x[2]] && k[y[2],y[1],x[2]] || l[x[2]]] ->
forAll[{x[2],x[1]},(f[x[1]]&&g[x[2]])||(exists[{y[2],y[1]},j[y[2],x[2]]&&k[y[2],y[1],x[2]]])||l[x[2]]. *)

indicesToOriginalLevel[var_Symbol]:= var;
indicesToOriginalLevel[var_[no__]]:= var[no]//.varnew_[noenum__, newno_Integer]:> varnew[noenum][newno];
 (*indicesToOriginalLevel[variable] writes indices in single brackets. 
  Example: x[1,2,3] -> x[1][2][3].*)

varExp[expr_,quantor_,con_]:= Replace[expr, quantor[{var__}, scope_con] /; Length[{var}] > 1 :> Fold[quantor[{#2}, #1]&, scope, Reverse[{var}]], {0, Infinity}];
varExp[expr_]:= Replace[expr, (quantor:(forAll|exists))[{var__}, scope_] /; Length[{var}] > 1 :> Fold[quantor[{#2}, #1]&, scope, Reverse[{var}]], {0, Infinity}];
(*varEr2,r3,r4,R,F1,F2,F3,F4,F5xp[expression_] := Replace[varExpC[expression], var_[no__]:> indicesToOriginalLevel[var[no]], {-2}];*)
(* varExp[FOLexpression] >explodes< the quantifiers of a FOLexpression.
Example: forAll[{x[1,1],x[1,2]},f[x[1,1],x[1,2]]] -> forAll[{x[1,1]},forAll[{x[1,2]},f[x[1,1],x[1,2]]]]. 
Exploded notation of quantifiers with binding variables with indices to the same level is the standard notation.*)

varExpSort[expr_,quantor_,con_]:=varExp[varImpSort[expr,quantor,con],quantor,con];
varExpSort[expression_]:= varExp[varImpSort[expression]];
(*varExpSort[FOLexpression] sorts quantifers according to the number of their occurrences 
in subexpressions of the scopes of quantifers and returns exploded forms.
Example: exists[{y[1]},exists[{y[2]},f[y[1],y[2]]&&g[y[2]]]] -> exists[{y[2]},exists[{y[1]},f[y[1],y[2]]&&g[y[2]]]].*)

maxIndices[expression_] := 
    Module[{xs=0, ys=0, expr}, 
	expr = varExp[expression] /. {x -> xx, y -> yy}/.var_[no__]:>indicesToSameLevel[var[no]];
	expr = expr //. Cases[expr, forAll[{var_/;var=!=xx}, scope_] :> forAll[{var}, scope2_] :> forAll[{x[++xs]}, scope2 /. var :> x[xs]], {0, Infinity}]
	     //. Cases[expr, exists[{var_/;var=!=yy}, scope_] :> exists[{var}, scope2_] :> exists[{y[++ys]}, scope2 /. var :> y[ys]], {0, Infinity}];
    expr //. forAll[{xx}, scope_] :>(forAll[{xx}, scope] /. xx -> x[++xs]) //. exists[{yy}, scope_] :>(exists[{yy}, scope] /. yy -> y[++ys])]; 
(*maxIndices[FOL-expression] replaces variables such that universal quantified variables are x-variables and existential quantified variables are y-variables. Furthermore,
these variables are indicated in such a way that no variable is bound twice. Thus, each quantifier is identifiable by its variable. In the output each variable is bound by a single quantifier (exploded form).
Example: forAll[{z},f[z]]&& forAll[{z},g[z]]-> forAll[{x[1]},f[x[1]]]&& forAll[{x[2]},g[x[2]]].*)

qSeq[maxexpr_]:= Cases[maxexpr, (quantor:(forAll|exists))[{var_}, scope_]/; FreeQ[scope, exists] && FreeQ[scope, forAll]
                   :> Reverse[Cases[maxexpr, (quantor2:(forAll|exists))[{var2_}, scope2_] /;Not[FreeQ[scope2, var]]:> var2, {0, Infinity}]],
                   {0, Infinity}];
(*qSeq[maxexpr] identifies all sequences of quantifiers by returning lists of variables.
Example: forAll[{x[1]},exists[{y[1]},f[x[1],y[1]]]||exists[{y[2]},g[x[1],y[2]]]] -> {{x[1],y[1]},{x[1],y[2]}}.*)

minIndices1[expression_] := 
	Module[{vs, expr, qs},
	  expr = maxIndices[expression] /.  {x -> xx, y -> yy}; 
	  qs = qSeq[expr]; 
	  expr //. DeleteDuplicates[Flatten[Map[(vs=0; Cases[#, xx[id__] :> (xx[id] -> x[++vs])])&, qs]]]
         //. DeleteDuplicates[Flatten[Map[(vs=0; Cases[#, yy[id__] :> (yy[id] -> y[++vs])])&, qs]]]];
(*minIndices1[FOLexpression] minimizes the number of variables.
Example: forAll[{x[1]},f[x[1]]]&&forAll[{x[2]},g[x[2]]] -> forAll[{x[1]},f[x[1]]]&&forAll[{x[1]},g[x[1]]];*)

minIndices2[expression_] :=
    Module[{expr, varpos, varcmp, sorted, varmod},
        expr = varImp[expression] /. {x -> xx, y -> yy};
        expr = MapAll[Replace[#,(quantor:(forAll|exists))[var_,scope1_]/;Length[var]>1  :> ( 
                    varpos = Map[Position[scope1, #]&, var];
                    varcmp = Transpose[{var, Map[LeafCount[#]&, varpos], Map[FromDigits[Flatten[#]]&, varpos]}];
                    sorted = Sort[varcmp, If[#1[[2]]=== #2[[2]], #1[[3]]< #2[[3]], #1[[2]]>= #2[[2]]]&];
                    varmod = Map[First[#]&, sorted];
                    quantor[var, scope1 /. Thread[RuleDelayed[varmod, var]]])]&, expr];
         expr = expr /.  {xx -> x, yy -> y};
         varExp[expr]];  
(*minIndices2[FOLexpression] standardizes the position of variables in expression with a minimum of variables.
Example: exists[{y[1]},exists[{y[2]},F[y[2],y[1]]&&G[y[2],y[1]]]] -> exists[{y[1]},exists[{y[2]},F[y[1],y[2]]&&G[y[1],y[2]]]]*)

minIndices[expression_]:= minIndices2[minIndices1[expression]];
(*minIndices[FOL-expression] minimizes the number of variables to a maximal extent and standardizes their positions.  
Example: forAll[{x[1]},exists[{y[1]},f[x[1],y[1]]]||exists[{y[2]},g[x[1],y[2]]]] -> forAll[{x[1]},exists[{y[1]},f[x[1],y[1]]]||exists[{y[1]},g[x[1],y[1]]]]. 
This function is needed to optimize FOL-expressions.*)

matrix[maxexpr_]:=
	Module[{newexpr},
      newexpr = maxexpr//.expr_/;Head[expr]===exists||Head[expr]===forAll:>expr[[2]];
newexpr];
(*matrix[FOL-expression] returns the matrix of a prenex normal form of FOL-expression.*)

pn3[expression_]:= Map[Replace[#, forAll[{xvar_},scope_Or]:> 
             forAll[{xvar}, Select[scope, Not[freeAllQ[#,{xvar}]] &]] || Select[scope, freeAllQ[#,{xvar}] &]] &, expression, {-Infinity, -4}];                     
(*pn3[maxexpr] applies PN3/PN4 to maxexpr in expanded standard (exploded) form to pull quantifiers in.
Example: forAll[{x},f[x]\[Or]p] -> forAll[{x},f[x]]\[Or]p.*)

pn5[expression_]:= Map[Replace[#, exists[{yvar_},scope_And]:> 
             exists[{yvar}, Select[scope, Not[freeAllQ[#,{yvar}]] &]] && Select[scope, freeAllQ[#,{yvar}] &]] &, expression, {-Infinity, -4}];           
(*pn5[maxexpr] applies PN5/PN6 to maxexpr in expanded standard (exploded) form to pull quantifiers in.
Example: exists[{y},f[y]\[And]p] -> exists[{y},f[y]]\[And]p.*)

pn9[expression_]:= wf[expression //. forAll[{xvar_}, scope_And] :> Map[forAll[{xvar}, #] &, scope]];
(*pn9[maxexpr] applies PN1/PN2/PN9 to maxexpr in standard (exploded) form to pull quantifiers in.
Example: forAll[{x},f[x]\[And]g[x]]-> forAll[{x},f[x]]\[And]forAll[{x},g[x]].*)

pn10[expression_]:= wf[expression //. exists[{yvar_}, scope_Or] :> Map[exists[{yvar}, #] &, scope]];
(*pn10[maxexpr] applies PN7/PN8/PN10 to maxexpr in standard (exploded) form to pull quantifiers in.
Example: exists[{y},f[y]\[Or]g[y]]-> exists[{y},f[y]]\[Or]exists[{y},g[y]].*)

inpn3[maxexpr_]:= Map[(ReplaceRepeated[#, {forAll[{xvar1_}, scope1_] || disj_ :> forAll[{xvar1}, scope1 || disj],
                                           disj_||forAll[{xvar1_}, scope1_]:> forAll[{xvar1}, scope1 || disj]}])&, maxexpr, {-Infinity, -4}];
(*inpn3[maxexpr] applies PN3 to generate prenex normal forms.*)

inpn5[maxexpr_]:= Map[(ReplaceRepeated[#, {exists[{yvar1_}, scope1_] && conj_ :> (exists[{yvar1}, scope1 && conj]),
                                          conj_ && exists[{yvar1_}, scope1_] :> (exists[{yvar1}, scope1 && conj])}])&, maxexpr, {-Infinity, -4}];
(*inpn5[maxexpr] applies PN5 to generate prenex normal forms.*)

apn[maxexpr_]:=
    Module[{expr},	
      expr = pn9[maxexpr];  
      expr = pn10[expr]; 
      expr = inpn3[expr];
      expr = varExpSort[expr,forAll,Or];
      expr = pn3[expr]; 
      expr = inpn5[expr]; 
      expr = varExpSort[expr,exists,And];
      expr = pn5[expr];
    expr];
pn[maxexpr_]:= FixedPoint[apn, maxexpr];
(*pn[maxexpr] applies PN-laws to a maximal extent without converting the scopes of universal quantifiers to CNFs and the 
scope of existential quantifiers to DNFs.*)


(*SECTION 2: TRANSLATING CTM TO CLAUSES AND TO AN EXPRESSION IN PURE FOL*)

(*CTM2Clauses translates CTM to clauses. This is not needed for the paper "Explaining Undecidability".*)

CTM2Clauses[{states_List, symbols_List, rules_List, q1_, qf_, tape_List}] := Module[{ret,n, qx,s1, v, v2sk, qy, qyaux1, qyaux2, usedsymbols, nesting},
If[!MemberQ[states,q1]||!MemberQ[states,qf], Print["Error: The initial and end states of the machine must belong to the list of states."];Return[{}]];
If[!And@@Map[MemberQ[symbols, #]&,tape], Print["Error: The symbols in the tape must belong to the list of symbols."]; Return[{}]];
If[MemberQ[symbols, G], Print["Error: the symbol G is a special symbol that must not belong to the list of symbols."]];
If[!And@@Map[Length[#]===4&, rules], Print["Error: rules must be a list of lists, each list having four members."]];
If[!And@@Map[MemberQ[states,#[[1]]]&, rules], Print["Error: the first member of a rule must belong to the list of states"]];
If[!And@@Map[MemberQ[symbols,#[[2]]]&, rules], Print["Error: the second member of a rule must belong to the list of symbols"]];
If[!And@@Map[ListQ[#[[3]]]&&(Length[#[[3]]]==1||Length[#[[3]]]==2)&&And@@Map[MemberQ[symbols,#]&,#[[3]]]&, rules], Print["Error: the third member of a rule must be a list of size 1 or 2 with members belonging to the list of symbols"]];
n=Length[tape];
xr[b_,e_] := Sequence@@Map[x[#]&, Range[b,e]];
usedsymbols = Union[tape, Map[#[[2]]&,rules], Flatten[Map[If[Length[#[[3]]]===1, {#[[3,1]]},{#[[3,1]],#[[3,2]]} ]&,rules]]];
nesting = !And@@Map[(Length[#[[3]]]===1)&, rules];

ret = {
(*add the clause that corresponds to the initial configuration of the machine*)
{!q1[Sequence@@Map[sk[#, {sk[G,{} ]}]&,tape]]},
(*add the clauses that correspond to the rules *)
Sequence@@Map[(qx=#[[1]];s1=#[[2]];v=#[[3]];qy=#[[4]];v2sk = If[Length[v]===1,  sk[First[v],{sk[G,{}]}],sk[First[v],{sk[Last[v],{sk[G, {}]}]}]]; 
qyaux1 = ToExpression[ToString[qy]<>"aux1"];
qyaux2 = ToExpression[ToString[qy]<>"aux2"];
Sequence@@
(*6.1*)
{{qx[sk[s1, {sk[G, {}]}],xr[2,n]], !qy[Sequence@@Map[x[#]&, Range[2,Length[tape]]],v2sk]},
(*6.2*)
If[nesting,Sequence@@Map[{qx[sk[s1,{sk[#,{x[1]}]}], xr[2,n]], !qyaux1[sk[#,{x[1]}], xr[2,n-1],v2sk, sk[G,{}], x[n]]}&,usedsymbols],Nothing],
(*6.3*)
If[nesting,Sequence@@Map[{qyaux1[xr[1,n+1], sk[#, {x[n+2]}]], !qyaux1[xr[1,n], sk[#,{x[n+1]}],x[n+2]]}&,usedsymbols],Nothing],
If[nesting,Sequence@@Map[{qyaux1[xr[1,n+1], sk[G, {}]], !qyaux2[xr[1,n+1]]}&,usedsymbols],Nothing],
If[nesting,Sequence@@Map[{qyaux2[xr[1,n], sk[#, {x[n+1]}]], !qyaux2[xr[1,n-1], sk[#,{x[n]}],x[n+1]]}&,usedsymbols],Nothing],
If[nesting,Sequence@@Map[{qyaux2[xr[1,n], sk[G, {}]], !qy[xr[1,n]]}&,usedsymbols],Nothing]
})& ,rules],
(*add the clause that corresponds to the halting state of the machine*)
{qf[xr[1,n]]}
};
DeleteDuplicates[ret]];

(*Clauses2FOL translates clauses to pure FOL-formulas.*)
Clauses2FOL[clauses_, n_] :=Module[{ret,sks},
   ret = And@@Map[Or@@# &, clauses];
   Map[If[!FreeQ[ret,#], ret =A[#, ret], ret] &, {xr[1, n + 2]}];
ret = ret/.sk[G,{}]->a;
ret = ret//.sk[k_,{xvars__}]:>ToExpression["sk"~~ToString[k]][xvars]; 
   pn[untradi[ret]]];



(*SECTION 3: TRANSLATING STM TO CLAUSES AND TO AN EXPRESSION IN PURE FOL*)

(*STM2Clauses generates a pair {clauses, FOL-formula} from STMs.*)
STM2Clauses[{states_List, symbols_List, rules_List, q1_, qf_, tape_List}] := Module[{ret,n, qx,s1, v, v2sk, qy, qyaux1, qyaux2, usedsymbols, faux1, faux2, faux3, faux4, faux5, faux6, 
faux7, faux8, faux9, faux10, faux11, faux12,  fauxS, alpha, clauses, FOLform, lits},
If[!MemberQ[states,q1]||!MemberQ[states,qf], Print["Error: The initial and end states of the machine must belong to the list of states."];Return[{}]];
If[!And@@Map[MemberQ[symbols, #]&,tape], Print["Error: The symbols in the tape must belong to the list of symbols."]; Return[{}]];
If[MemberQ[symbols, G], Print["Error: the symbol G is a special symbol that must not belong to the list of symbols."]];
If[!And@@Map[Length[#]===4&, rules], Print["Error: rules must be a list of lists, each list having four members."]];
If[!And@@Map[MemberQ[states,#[[1]]]&, rules], Print["Error: the first member of a rule must belong to the list of states"]];
If[!And@@Map[MemberQ[symbols,#[[2]]]&, rules], Print["Error: the second member of a rule must belong to the list of symbols"]];

n=Length[tape];
xr[b_,e_] := Sequence@@Map[x[#]&, Range[b,e]];
usedsymbols = Union[tape, Map[#[[2]]&,rules], Flatten[Map[If[Length[#[[3]]]===1, Nothing ,{#[[3,2]]} ]&,rules]]];
RC[type_] := MemberQ[Map[First[#[[3]]]&,rules], type];

ret = {
(*add the clause that corresponds to the initial configuration of the machine*)
{!Faux0[Sequence@@Map[sk[G,{} ]&,tape]]},
{Faux0[Sequence@@Map[x[1]&,tape]], !q1[Sequence@@Map[sk[#, {x[1]}]&,tape],sk[G,{} ]]},

(*add the clauses that correspond to the rule L and R, but are only added once*)
If[RC[L]||RC[R],Sequence@@Map[(alpha = #;
faux1= ToExpression["Faux1A"<>ToString[alpha]];
faux2 = ToExpression["Faux2"];
faux3 = ToExpression["Faux3A"<>ToString[alpha]];
faux4 = ToExpression["Faux4"];
faux5 = ToExpression["Faux5A"<>ToString[alpha]];
faux6 = ToExpression["Faux6"];
faux7= ToExpression["Faux7"];
faux8= ToExpression["Faux8A"<>ToString[alpha]];
faux9= ToExpression["Faux9"];
faux10 = ToExpression["Faux10A"<>ToString[alpha]];
faux11 = ToExpression["Faux11"];
faux12 = ToExpression["Faux12A"<>ToString[alpha]];
Sequence@@{
{FauxR[x[2], sk[alpha, {x[1]}], xr[3,n+2]], !faux1[sk[alpha, {x[1]}],x[1], sk[G,{}], xr[3,n], x[2], x[n+1],x[n+2]]}, (*CLAUSE 4*) 
{faux1[xr[2,n+3], x[1], x[n+4]], !faux2[sk[alpha, {x[1]}],xr[3,n+3],x[1],x[n+4]]}, (*CLAUSE 5*)
{faux2[x[2], sk[alpha,{x[1]}],xr[3,n+4]], !faux3[x[2],x[1], xr[3,n+4]]}, (*CLAUSE 6*)
{faux3[x[2],x[3],x[1],xr[4,n+4]], !faux2[x[2],x[3], sk[alpha, {x[1]}], xr[4,n+4]]}, (*CLAUSE 7*)
{faux2[x[1],sk[G,{}], xr[2,n+3]], !faux4[xr[1,n+3]]}, (*CLAUSE 8*)
{faux4[x[2], sk[alpha,{x[1]}],xr[3,n+3]], !faux5[x[2],x[1], xr[3,n+3]]}, (*CLAUSE 9*)
{faux5[x[2],x[3],x[1],xr[4,n+3]], !faux4[x[2],x[3], sk[alpha, {x[1]}], xr[4,n+3]]}, (*CLAUSE 10*)
{faux4[x[1],sk[G,{}], xr[2,n+2]], !faux6[xr[1,n+2]]}, (*CLAUSE 11*)
If[RC[L],Sequence@@{
{FauxL[xr[1,n+2]], !faux7[sk[G,{}], xr[1,n],sk[G,{}], x[n+1],x[n+2]]}, (*CLAUSE 14*)
{faux7[xr[2,n+1], sk[alpha, {x[1]}], xr[n+2,n+4]], !faux8[xr[2,n+1], x[1], xr[n+2,n+4]]}, (*CLAUSE 15*)
{faux8[xr[2,n+2],x[1],x[n+3],x[n+4]],!faux7[xr[2,n+2],sk[alpha, {x[1]}], x[n+3],x[n+4]]}, (*CLAUSE 16*)
{faux7[xr[1,n], sk[G,{}], xr[n+1,n+3]], !faux9[xr[1,n+3]]}, (*CLAUSE 17*)
{faux9[xr[2,n+1], sk[alpha, {x[1]}], x[n+2], x[n+3]], !faux10[xr[2,n+1], x[1], x[n+2], x[n+3]]}, (*CLAUSE 18*)
{faux10[xr[1,n+3]], !faux11[sk[alpha,{x[1]}], xr[2,n+1], sk[G,{}],x[n+2],x[n+3]]}, (*CLAUSE 19*)
{faux11[xr[1,n], sk[G,{}], sk[G,{}], x[n+1], x[n+2]], !faux6[xr[1,n+2]]}, (*CLAUSE 20*)
{faux11[xr[2,n+1],sk[alpha, {x[1]}], xr[n+2,n+4]], !faux12[xr[2,n+1], x[1], xr[n+2,n+4]]}, (*CLAUSE 21*)
{faux12[xr[2,n+2], x[1], x[n+3], x[n+4]], !faux11[xr[2,n+2], sk[alpha, {x[1]}], x[n+3], x[n+4]]}, (*CLAUSE 22*)
{faux11[xr[1,n], sk[G,{}], xr[n+1,n+3]], !faux2[x[1], x[2], sk[G,{}], xr[3,n+3]]}},Nothing] (*CLAUSE 23*)
})&,usedsymbols],Nothing],
faux6 = ToExpression["Faux6"];
Sequence@@Map[{faux6[xr[1,n+1], sk[#,{}]], !#[xr[1,n+1]]}&,states], (*CLAUSE 12*)

(*add the clauses that correspond to the rule S, but are only added once*)
If[RC[S],Sequence@@Map[(fauxS = ToExpression["FauxS"<>ToString[First[#]]];
{fauxS[x[2], x[1], xr[3,n+1], sk[Last[#], {}]], !Last[#][x[2], sk[First[#], {x[1]}], xr[3,n+1]]})&, Flatten[Outer[List, symbols, states], 1]],Nothing],(*CLAUSE 26*)

(*add the clauses that correspond to the rules *)
Sequence@@Map[(qx=#[[1]];s1=#[[2]];v=#[[3]];qy=#[[4]];
Sequence@@{
Switch[First[v],
S, fauxS = ToExpression["FauxS"<>ToString[s1]];{qx[sk[s1, {x[1]}], xr[2, n+1]], !fauxS[sk[s1, {x[1]}], xr[2,n+1], sk[qy,{}]]},(*CLAUSE 25*)
R, {qx[sk[s1, {x[1]}], xr[2,n+1]], !FauxR[sk[s1, {x[1]}],xr[2,n+1], sk[qy,{}]]}, (*CLAUSE 3*)
L, {qx[sk[s1, {x[1]}], xr[2,n+1]], !FauxL[sk[s1, {x[1]}],xr[2,n+1], sk[qy,{}]]}, (*CLAUSE 13*)
W, {qx[sk[s1, {x[1]}], xr[2,n+1]], !qy[sk[Last[v], {x[1]}],xr[2,n+1]]} (*CLAUSE 24*)
]
})& ,rules],

(*add the clause that corresponds to the halt state*)
{qf[xr[1,n], sk[G,{}]]}
};

clauses = DeleteDuplicates[ret]; 
(*generate the corresponding FOL-expression*)
FOLform = folForm[clauses,symbols,states,n]; 
(*generate final clauses from FOLform.*)
(*We want clauses in anti-prenex form with the number of the initial literals corresponding to the numbers in the FOLform.*)
clauses = toClauseNormalForm[FOLform]; 
(*Note, that we cannot presume a one-to-one correspondence between x-variables in FOLform and clauses. Yet, we can presume a correspondence between an y-variable with index ii in FOLform to all those skolem-functions in clauses with number ii.*)
{clauses,FOLform}];

(*folForm generates an FOL-expression corresponding to the STM-clauses*)
folForm[clauses_,symbols_,states_,n_]:=Module[{FOLform,lits},
FOLform = And@@Map[Or@@# &, clauses];
Map[(FOLform = A[#,FOLform])&,Map[x[#]&, Range[2,n+4]]];
FOLform=pn9[untradi[FOLform]];
MapIndexed[(FOLform = E[y[Sequence@@#2], FOLform //. sk[#1, {x[1]}] -> y[Sequence@@#2]])&, symbols];
FOLform=pn5[varExpSort[untradi[FOLform],exists,And]];
FOLform =pn9[forAll[{x[1]},FOLform]];
FOLform=inpn5[FOLform];
MapIndexed[(FOLform = E[y[Sequence@@#2+Length[symbols]], FOLform //. sk[#1, {}] -> y[Sequence@@#2+Length[symbols]]])&, Join[{G},states]];
(*We want FOLform in anti-prenex normal form and with literals of form phi[boolean,arguments,number].*)
FOLform =maxIndices[untradi[FOLform]];
lits = Flatten[matrix[FOLform]/.{And->List,Or->List}];
Map[(If[Head[lits[[#]]]===Not,FOLform = FOLform/.lits[[#]]->Prepend[Append[!lits[[#]],#],False], FOLform = FOLform/.lits[[#]]->Prepend[Append[lits[[#]],#],True]])&,Range[Length[lits]]];
FOLform];


(*SECTION 4: PROOF SEARCH FOR KROM-HORN CLAUSES IN TABLEAU*)
(*The proof search does not differ from the search in resolution in the special case of Krom-Horn clauses.*)

(*skolemize implements Outer Skolemization of a formula given in negation normal form. cf. Nonnengart, Weidenbach, "Computing Small Clause Normal Forms", 
Handbook of automated Reasoning, chapter 6.5, cf. 6.3 and Baaz, Egly, Leitsch, "Normal Form Transformations", Handbook of Automated Reasoning,  chapter 5.5. *)
skolemize[forAll[{xvar_}, scope_], xvars_]:= forAll[{xvar}, skolemize[scope, Append[xvars, xvar]]] ;
(*skolemize[exists[{yvar_}, scope_], xvars_]:= skolemize[scope /. yvar -> sk[++funcount, xvars], xvars];*)
skolemize[exists[{yvar_}, scope_], xvars_]:= skolemize[scope /. yvar -> sk[First[yvar], xvars], xvars];
skolemize[f:(_And|_Or|_Not), xvars_]:= Head[f]@@Map[skolemize[#, xvars]&, List@@f];
skolemize[f_, xvars_]:= f;
skolemize[f_]:= (*(funcount=0;*)skolemize[f, {}](*)*);

(*maxIndicesForAll replaces vars in @expression such that universal quantified vars are x-vars. These vars are indicated such that no var is bound twice (rectification).*)
maxIndicesForAll[expression_] := Module[{xs=0, expr},
expr = expression /. x -> xx;expr = expr //. Cases[expr, forAll[{var_/;var=!=xx}, scope_] :> forAll[{var}, scope2_] :> 
  forAll[{x[++xs]}, scope2 /. var :> x[xs]], {0, Infinity}];expr //. forAll[{xx}, scope_] :>(forAll[{xx}, scope] /. xx -> x[++xs])]; 

(*toClauseNormalForm converts @expr into clauses.*)
toClauseNormalForm[expr_]:= Module[{nexpr},
	nexpr = skolemize[untradi[expr]];
	nexpr = maxIndicesForAll[pn9[nexpr]]; (*Cf. B\[ODoubleDot]rger et al, p. 388, Wikipedia on Resolution, cf. orkpairnurTeilformel*) 
	nexpr = nexpr//.forAll[{xvar_},scope_]:>scope; 
	(*nexpr = BooleanMinimize[nexpr,"CNF"];*)
	nexpr = If[Head[nexpr]===And, List@@nexpr, {nexpr}];
  nexpr = Map[If[Head[#]===Or, Sort[List@@#],{#}]&, nexpr]; 
nexpr];

(*prependBoolToLits prepends True or False to literals of @clauses to indicate whether they are positive or negative.*)
prependBoolToLits[clauses_]:= Module[{nclauses},
	nclauses = Map[If[Length[#]===0,  #[], If[Head[#]===Not && Length[Last[#]]===0, Not[Last[#][]], #]]&, clauses,{2}]; (*This line is needed in the case of atomic formulas.*)
	nclauses = Map[Map[If[Head[#] === Not, Prepend[Last[#], False], Prepend[#, True]]&, #]&, nclauses];
nclauses];

(*appendNoToLits numbers literals in @clauses and inserts the numbers as last member in literals.*)
appendNoToLits[clauses_]:= Module[{id=0}, Map[Map[Append[#, ++id]&, #]&, clauses]];

(*We restrict the initialisation step to negative clauses [see function iterate3]. See Handbook of Automated Reasoning, vol 2, p. 2040.*)
negativeClauseQ[clause_] := !Or@@Map[First, clause];
sbranch[cbranch_] := First[cbranch];
notation[cbranch_]:= Last[cbranch];
status[cbranch_]:= Last[cbranch]; 

(*firstBranch returns the position of the first branch of @tableau with status @s; it returns Missing["NotFound"] if there is none.*)
firstBranch[tableau_,s_] := FirstCase[Range[Length[tableau]], n_ /; status[tableau[[n]]] === s];

(*no returns the number of @lit.*)
no[lit_]:= Last[lit];

(*purelit returns @lit without its number and without its truth value (False for negation and True for affirmation).*)
purelit[lit_]:= Most[Rest[lit]];

(*unifyArgs tests the unification of arguments of literals. It returns False if no unification is possible; otherwise, it appends to osubs the substitution that makes the 
unification. value is "True" in case of condense and subCheck.*)
SetAttributes[unifyArgs, Orderless]; (*Orderless is incorrect in the case of value===True (which is needed for condense and subCheck.*)
unifyArgs[x[i__],x[i__],osubs_List]:= osubs;
unifyArgs[x[i__],sk[n_,args_],osubs_List]:= If[FreeQ[args,x[i]], {osubs,x[i]->sk[n,args]}, False];
unifyArgs[sk[n_,args_],x[i__],osubs_List]:= If[FreeQ[args,x[i]], {osubs,x[i]->sk[n,args]}, False];
unifyArgs[x[i__],x[j__],osubs_List]:= {osubs, Rule@@Sort[{x[i], x[j]}]}; 
(*Rule@@Sort is necessary, otherwise notref3 is incorrectly decided as False. Rule@@Sort is also necessary for minUnifierQAux.*)
unifyArgs[sk[n1_, args1_],sk[n2_,args2_],osubs_List]:= unifyLits[n1@@args1,n2@@args2,osubs];
(*unifyLits tests the unification of literals @lit1 and @lit2 and returns a substitution list in the case of unifiability.*)
unifyLits[lit1_,lit2_,osubs_] /; Head[lit1]===Head[lit2]&&Length[lit1]===Length[lit2] := Module[{subs}, subs=osubs;
    Scan[(subs=unifyArgs[First[#]//.subs,Last[#]//.subs,subs]; If[subs===False, Return[False], subs=Flatten@subs])&, Transpose[{List@@lit1, List@@lit2}]];
subs];
unifyLits[lit1_,lit2_,osubs_]:= False;

(*unify returns a substitution list to unify the pair of literals @olit1 and @olit2.*)
unify[olit1_,olit2_]/; First[olit1]=!=First[olit2]:= unifyLits[purelit[olit1], purelit[olit2],{}];
unify[olit1_,olit2_]:= False;

(*singleUnification computes the substitution list for a unifiable pair of literals stemming from the last member of a branch and a new literal. 
The unified pair of literals and its unifier are returned.*)
singleUnification[{entrylit_,newlit_}]/;unifiableQ[no[entrylit],no[newlit]]:= If[#=!=False,{{entrylit,newlit},#},{{entrylit,newlit},False}]&@unify[entrylit,newlit];
singleUnification[{entrylit_,newlit_}] := {False};

(*expansionStep creates a list of {nodes} from a given clause whose xvars are different from any node of the actual tableau.*)
expansionStep[clause_,tableau_]:= ReplaceAll[clause, Map[# -> Append[#, ++mpXvarIt[#]]&, mpClauseXvars[clause]]];
(*newfv[var_,tableau_]:= Module[{cases}, 
  cases = Cases[tableau, Head[var][First[var], n_] :> n, {0, Infinity}]; If[cases === {}, Append[var,1], Append[var, First[Complement[Range[Max[cases]+1],cases]]]]];
(*expansionStep creates a list of {nodes} from a given clause whose xvars are different from any node of the actual tableau.*)
expansionStep[clause_,tableau_]:= ReplaceAll[clause, Map[# -> newfv[#, tableau]&, mpClauseXvars[clause]]];*)

(*infExp computes the next expansion steps for the F-branch with number @cbno of @tableau.*)
infExp[tableau_,cbno_,clauses_]:= Module[{cbranch = tableau[[cbno]],lastlit,expclauses,expclause,unifiers}, 
 lastlit = Last[sbranch[cbranch]];
  expclauses = Map[expansionStep[#,tableau]&, Intersection[mpLitClauses[no[lastlit]],clauses]]; 
  unifiers=DeleteCases[Join@@Map[(expclause=#; unifiers = DeleteCases[Map[singleUnification[{lastlit,#}]&,expclause],unifier_/;Last[unifier]===False];  
    If[unifiers=!={}, Map[{cbno,First[#],expclause,Last[#]}&,unifiers], Nothing])&, 
  expclauses],Null]; If[unifiers==={},Print["dead end."]]; 
 unifiers];

(*performInfStep performs @infstep in @tableau. In case of an expansion step, we may generate N-branches as well as up to one P1-branch in addition to the S-branch.
We generate a P1-branch if we expand the loop (which I call the main branch, while the other N-branches are side-branches).*)
(*newCbranches[cbranch_,{cbno_,{lit1_,lit2_},clause_,subs_}] := Sequence@@Map[{Append[sbranch[cbranch],#], If[#===lit2, "S", "F"]} &, clause];*)
(*newCbranches[cbranch_,{cbno_,{lit1_,lit2_},clause_,subs_}] := Sequence@@Map[If[#===lit2, {Append[sbranch[cbranch],#],"S"}, {Append[sbranch[cbranch],#//.subs],"F"}]&, clause];
replaceInInfStep[tableau_,infstep_] := ReplacePart[tableau, First[infstep] -> newCbranches[tableau[[First[infstep]]],infstep]];
performInfStep[tableau_,infstep_] := replaceInInfStep[tableau,infstep];*)
performInfStep[tableau_,{cbno_,{lit1_,lit2_},clause_,subs_}] := If[Length[clause]===1, {{Append[sbranch[First[tableau]],lit2],"S"},Last[tableau]}//.subs,
{{Append[sbranch[First[tableau]],If[First[clause]===lit2,Last[clause],First[clause]]],"F"},{Append[sbranch[Last[tableau]],lit2],"S"}} //.subs];

(*regularityQ checks for regularity in @tableau, i.e. no duplicates on a branch. It returns True if the regularity condition is met; otherwise it returns False.*)
regularityQ[tableau_] := Scan[If[!DuplicateFreeQ[Map[Most,sbranch[#]]], (*Print["Regularity applies."];*) Return[True], False]&, tableau] === True;

(*firstIndex[expression] deletes all indices of variables of level >1.*)
firstIndex[expression_]:=  expression/.(v:(x|y))[i_, j___] :> v[i];
skolemReduce[expression_]:= expression/.sk[no_,xvars_List]:>sk[no,{}];

(*solve generates the tableau until either a proof is found, regularity applies or itscounter reaches the upperbound.*)
solve[tableau_, clauses_, Missing["NotFound"],upperbound_] :=  {True,tableau};
solve[tableau_,clauses_,cbno_,upperbound_] := Module[{ntableau,value},
Scan[({value,ntableau} = solve[performInfStep[tableau,#],clauses,upperbound]; If[value ===True ||value===sat, Return[{value,ntableau}],False])&, infExp[tableau,cbno,clauses]];
{value,ntableau}]; 
solve[tableau_,clauses_,upperbound_] := Module[{cbno}, itscounter++; 
   (*PRINT COMMANDS*) (*If[IntegerQ[Length[tableau]/1],printTableau[tableau]];*)(*If[itscounter\[GreaterEqual]40,Abort[]];  Print["tableau = ", tableau];*)
           (*If[regularityQ[tableau], Print["Regularity applies."];Return[{sat,tableau}]];*) (*We want to check our Loop-Criterion, even in the sat-case without applying regularity.*)
    If[itscounter===upperbound, Print["Upper bound reached."]; Return[{sat,tableau}]];
           cbno = firstBranch[tableau,"F"]; 
            solve[tableau,clauses,cbno,upperbound]];

(*printTableau prints the tableau in tree-form; known issue: if two nodes of the tableau have identical label, it creates only a single node.*)
printTableau[tableau_] := Module[{ntableau, m, edges = {}, index, kpairnos}, 
          ntableau = Map[{sbranch[#],notation[#]}&,tableau];
     ntableau = ntableau /. {F_[False, x__] -> !F[x], F_[True, x__] -> F[x]};
     ntableau = ntableau /. x[y_, z_] -> Subscript[x,Subscript[y, z]];
     ntableau = ntableau //. sk[n_, l_List] :>  If[l =!= {}, Subscript[sk, n]@@l, Subscript[sk, n]];
     ntableau = MapIndexed[(index = Sequence@@#2;{Map[{#, index}&, sbranch[#1]], notation[#1]})&, ntableau];
     Do[ntableau = MapIndexed[(index = Sequence@@#2;{MapIndexed[If[index>1&& Length[sbranch[ntableau[[index-1]]]] >= 
       Sequence@@#2 && (First[#1] === First[sbranch[ntableau[[index-1]]][[Sequence@@#2]]]), sbranch[ntableau[[index-1]]][[Sequence@@#2]], #1]&, sbranch[#1]],
       notation[#1]})&, ntableau], Length[ntableau]];
     Map[(m =  sbranch[#]; AppendTo[edges, "Root" -> m[[1]]];
          Do[If[ii === Length[m] - 1,
             (*then*)AppendTo[edges, {m[[ii]] -> m[[ii + 1]], 
                        ToString[no[If[Head[First[m[[ii]]]] === Not, Last[First[m[[ii]]]], First[m[[ii]]]]] -> no[If[Head[First[m[[ii+1]]]] === Not, 
                          Last[First[m[[ii+1]]]], First[m[[ii+1]]]]]]}],
             (*else*)AppendTo[edges,m[[ii]] -> m[[ii + 1]]]], 
{ii, 1, Length[m] - 1}]) &, Sort[ntableau]]; (*We want a one-to-one correspondence between the unification of pairs of literals (kpairs) in the proofs of the NNF-calculus and 
the pairs of literals in the tableau sorted by the length of the branches.*)
     Print[TreePlot[DeleteDuplicates[edges], Automatic, "Root", DirectedEdges -> True, VertexLabeling -> True]]];

(*colorTableau prints the color diagram for tableaux.*)
colorTableau[mainbranch_,size_]:=Print[ArrayPlot[Map[Flatten[Apply[List,Prepend[purelit[#],Head[#]]]/.skfun_sk:>Cases[skfun,num_/;IntegerQ[num],Infinity]]&,sbranch[mainbranch/.xvar_x->sk[0,{}]]],ColorRules->{P->Red,
Faux0->LightBlue,Faux1A->LightMagenta,Faux2->Magenta,Faux3A->LightOrange,Faux4->Yellow,Faux5A->Cyan,Faux6->LightYellow,Faux7->Pink,Faux8A->Purple,Faux9->Orange,
Faux10A->Brown,Faux11->LightCyan,Faux12A->LightMagenta,FauxS0->Green,FauxS->Red,FauxR->LightYellow, FauxL->LightPink,Q01->LightPurple,Q02->LightBrown,Q03->LightGreen, 
P1->RGBColor[0.1,0.5,0.5],P2->RGBColor[0.9,0.5,0.5],P3->RGBColor[0.3,0.1,0.3],P4->RGBColor[0.1,0.5,0.9],P5->RGBColor[0.9,0.5,0.1],P6->RGBColor[0.5,0.5,0.1],P7->RGBColor[0.5,0.1,0.5],P8->
RGBColor[0.5,0.5,0.9],P9->RGBColor[0.5,0.9,0.5],P10->RGBColor[0.1,0.3,0.3],P11->RGBColor[0.3,0.3,0.1],P12->RGBColor[0.1,0.9,0.5],
H->Blue},ImageSize->size]];


(*SECTION 5: THE CORRESPONDING PROOF IN THE NNF-CALCULUS (for the case of STM)*)

(*We assume that we unify pairs of literals in a one-to-one correpsondence to the tableau. However, not every step in unifying a pair of literals corresponds to an &I-application (whereas every step of unifying a pair of literal in the tableau proof of Krom-Horn clauses corresponds to an expansion step).
It may well be that a literal is utilized that is already multiplied by a previous &I-multiplication of a \[ForAll]xvar\[Exists]y[num_1]...\[Exists]y[num_n](scope_And) expression.
We extract the corresponding NNF-proof by considering a one-to-one correspondence between y-variables and skolem-functions in the final proofs and by making use of our knowledge of the syntax of the initial FOLform (namely, that every disjuntion contains at least one skolem-function).*)

(*litQ returns True if the first Member of expr is a Boolean value. We can use this to identify literals due to our representation of literals in FOLform.*)
litQ[expr_]:=If[Length[expr]>1,First[expr]===True||First[expr]===False, False];
(*printMainBranch extracts pairs of literals from expr.*)
litPairs[expr_]:=Cases[expr,{lit1_/;litQ[lit1],lit2_/;litQ[lit2]},{0,Infinity}];

(*newAllExp1 multiplies universal expressions without existential quantifiers in their scope. They have to be multiplied if there is more than one literal with the same number in sklits (= literals with skolem-functions).*)
newAllExp1[expr_,sklits_]:=Module[{sklitsduplicates,sklitduplicate,allexp,vars,newallexp,newallexpr=expr}, 
sklitsduplicates = Cases[sklits,sklit_/;Length[Position[Map[Last,sklits],Last[sklit]]]>1];
While[sklitsduplicates=!={},
sklitduplicate=Cases[sklitsduplicates,sklit_/;Last[sklit]===Last[First[sklitsduplicates]]]; 
sklitsduplicates = Complement[sklitsduplicates,sklitduplicate]; 
allexp =Sort[Cases[expr,pexpr_forAll/;FreeQ[pexpr,And]&&Not[FreeQ[pexpr,lit_/;litQ[lit]&&Last[lit]===Last[First[sklitduplicate]]]]&&FreeQ[pexpr,{lit1_/;litQ[lit1],lit2_/;litQ[lit2]&&
Last[lit2]===Last[First[sklitduplicate]]}],{0,Infinity}],LeafCount[#1]<LeafCount[#2]&];
 allexp=Last[allexp];
vars = Flatten[Cases[allexp,{var_/;Head[var]===x||Head[var]===y},Infinity]]; 
newallexp = True;
Do[newallexp = newallexp && allexp/.Map[Rule[#,Append[#,ii]]&,vars],{ii,1,Length[sklitduplicate]}]; 
newallexpr = newallexpr/.allexp->newallexp]; 
newallexpr];

(*newAllExp2 replaces literals lit in expr by {lit,Most[sklit]} if lit and sklit have the same number. We do this for literals lit and sk-literal from sklits as well as the literals that are part of the same disjunction as lit is in expr. In this latter case we can infer the sk-literal from ukpairsindex for the sk-literal in sklits.
In the final newexpr we do not want to represent the initial number
of the literal in sklit (therefore we use Most). Instead, the number that is the last member in Most[sklit] identifies the number of the step that unifies the literals of the kpair and, thus, identifies the two literals of a kpair by the same last number in the final ulit that will replace Most[sklit]. So, lit and the final ulit will have a number as last member but those numbers have different meaning.
In the final newexpr, we want a pair {lit,ulit]}, where lit is a literal with x-variables and the number of the literal it steems from and ulit is the literal after unification + a number ii representing the step where the ii-th kpair is unified.
To achieve this, we will later replace skolem-functions in sklit by y-variables in sklit as soon as we a have a complete list of substitions for skolem functions \[Rule] y-variables.*)
newAllExp2[expr_,sklits_,sklitsnums_,ukpairsindexed_]:=Module[{lits,lit,sklit,skdlits=sklits,disj,lit2,sklit2num,sklit2,newexpr=expr,nsklitsnums=sklitsnums},
lits = DeleteCases[Cases[expr,lita_/;litQ[lita]&&FreeQ[lita,skfun_sk],Infinity],litb_/;Not[MemberQ[Map[Last,sklits],Last[litb]]]]; 
If[lits=!={}, 
Do[lit=lits[[ii]]; 
sklit=FirstCase[skdlits,sklit_/;Last[sklit]===Last[lit]]; 
skdlits = Cases[skdlits,Except[sklit]];
disj = Cases[newexpr,disjunction_Or/;Not[FreeQ[disjunction,lit]],Infinity];
If[disj==={}, (*lit corresponds to the initial state or the halting state.*)
newexpr = newexpr/.lit->{lit,Most[sklit]}; nsklitsnums=Append[nsklitsnums,sklit], 
disj=First[disj]; (*all other literals.*)  
If[FreeQ[disj,{lita_/;litQ[lita],litb_/;litQ[litb]}], 
If[FreeQ[First[disj],lit], 
lit2= First[Cases[First[disj],literal_/;litQ[literal],{0,Infinity}]]; sklit2num=sklit[[-2]]-1,
lit2= First[Cases[Last[disj],literal_/;litQ[literal],{0,Infinity}]]; sklit2num=sklit[[-2]]+1];
sklit2 = Cases[ukpairsindexed,skliteral_/;skliteral[[-2]]===sklit2num&&Last[skliteral]===Last[lit2],{2}];
If[sklit2=!={},  sklit2=First[sklit2];
newexpr = newexpr/.{lit->{lit,Most[sklit]},lit2->{lit2,Most[sklit2]}};
nsklitsnums=Join[nsklitsnums,{sklit,sklit2}],
(*in the sat-case, we have no sklit2 for the last literal.*)
newexpr= newexpr/.{lit->{lit,Most[sklit]},lit2->{lit2,sat}}; 
nsklitsnums=Append[nsklitsnums,sklit]]]],
{ii,1,Length[lits]}]];
{newexpr,nsklitsnums}];

(*If the outmost universal quantifier precedes more than on existential quantifier it may well be that its variable has to be substituted differently. In this case, more \[And]I-application have to be considers. newAllExprs computes these \[And]I-applications.*)
newAllExprs[newallexpr_,xvar_]:=Module[{yvarexpr,yvarscope,xvarlitpairs,sksublitpairs,xvarlitpair,pos,sksub,xsublitpairs,xvarlits,nallexpr,nallexprscope,vars,varindex=0,newallexprs=True},
(*Extract the part without xvar.*)
yvarexpr=DeleteCases[DeleteCases[newallexpr,disj_Or/;Not[FreeQ[disj,xvar]],Infinity],{lit1_/;litQ[lit1]&&MemberQ[lit1,xvar],lit2_/;litQ[lit2]&&Last[lit2]===1},Infinity];
If[Not[FreeQ[yvarexpr,lit_/;litQ[lit]]],yvarscope=Cases[wf[yvarexpr],exists[{yvar_y},scope_/;FreeQ[scope,{yvarr_y}]],{0,Infinity}][[1,2]],yvarscope=True]; 
xvarlitpairs=Cases[litPairs[newallexpr],{lit1_/;litQ[lit1]&&MemberQ[lit1,xvar],lit2_/;litQ[lit2]},Infinity];
sksublitpairs = {};
(*Extract the substituions of xvar*)
Do[xvarlitpair=xvarlitpairs[[ii]]; 
pos = First[Flatten[Position[First[xvarlitpair],xvar]]]; 
sksub=Last[xvarlitpair][[pos]];
sksublitpairs= Append[sksublitpairs,{sksub,xvarlitpair}],
{ii,1,Length[xvarlitpairs]}]; 
(*Generate the expression for each substitution of xvar.*)
While[sksublitpairs=!={},
xsublitpairs= Cases[sksublitpairs,sksublitpair_/;First[sksublitpair]===First[First[sksublitpairs]]]; 
sksublitpairs = Complement[sksublitpairs,xsublitpairs]; xvarlits=Map[First,Map[Last,xsublitpairs]]; 
nallexpr= wf[DeleteCases[DeleteCases[newallexpr,disj_Or/;FreeQ[disj,lit_/;litQ[lit]&& MemberQ[xvarlits,lit]],Infinity],{lit1_/;litQ[lit1]&&Not[MemberQ[xvarlits,lit1]],lit2_/;litQ[lit2]&&Last[lit2]===1},Infinity]]; 
vars = Flatten[Cases[nallexpr,{var_/;Head[var]===x||Head[var]===y},Infinity]]; 
nallexpr = nallexpr/.Map[Rule[#,ReplacePart[ #,-1->(Last[#]+varindex)]]&,vars]; varindex++; 
nallexprscope=Cases[nallexpr,exists[{yvar_y},scope_/;FreeQ[scope,exists]],Infinity][[1,2]];
nallexpr = wf[nallexpr/.nallexprscope:>(yvarscope&&nallexprscope)];
newallexprs=newallexprs&&nallexpr]; 
{newallexprs,Last[xvar]+varindex}];

(*newExpr generates a final expression with the whole NNF-proof encoded: it contains all the \[And]I-applications + the information about the unification of literals.*)
newExpr[FOLform_,clauselits_,ukpairsindexed_]:=Module[{newexpr=FOLform,sksublist={},sklitsnums={},sks,sksingles,sksingle,varindex=1,
nums,numsduplicates,numduplicates,num,sknums,sknum,allexpr,sklits,sklitnums,depths,sknumclause,newallexpr,newallexprs,nallexpr,vars,yvarlits,sublist},
(*sks are the skolem functions in ukpairsindexed. In generating newexpr we make use of our knowledge of literals steming from initial literals containing skolem-functions. The initial literals correspond to literals containing y-variables in FOLform. We know that all initial clauses with length 2 contain at least one such literal. This helps to identify universal expressions that have to be multiplied and to relate them to the corresponding literals in ukpairsindexed. Recall, that we cannot assume a one-to-one correspondence of universal variables in FOLform and initial clauses because applying pn-laws after skolemization in 
toClauseNormalForm allows to multiply universal quantifiers that cannot be multiplied by pn-laws applied to FOL-expressions. We can only presume a correspondence between and y-variable with index ii and all the skolem-functions with number ii in the initial clauses. Furthermore, we want to achieve a one-to-one correspondence between y-variables and skolem-functions
in the final newexpr and ukpairsindexed.*)
sks = Sort[DeleteDuplicates[Cases[ukpairsindexed,skfun_/;Head[skfun]===sk,Infinity]]]; 
(*nums are their numbers. It may well be that different skolem-functions have the same number. These will correspond to y-variables with the same
index on level 1 but different indices on level 2. These y-variable will occur in the scope of multiplied universal expressions.*)
nums = Map[First,sks]; 
(*numsduplicates are the numbers that occur more than once in nums. They will identify those universal expressions that have an existential quantifier in their scope and have to be multiplied. The multiplied expressions may contain more than one disjunction and, thus, not correspond to only one multiplied clause. This is the crucial difference to the KormHornSolver.
There is no one-to-one correspondence between expansion steps and &I-application but only a one-to-one correspondences between the unified pairs of literals. The multiplied expressions (clauses vs. universal expressions) are different. This affects the application of a Loop-Criterion that identifies loops in the inference steps multiplying expressions.*)
numsduplicates = DeleteCases[nums,num_/;Length[Position[nums,num]]===1];
numduplicates = numsduplicates;
(*sklitsnums selects the literals sklitnums from ukpairsindexed that are already considered in newexpr.*)
(*We first multiply universal expressions with an existential quantifier in the scope. From the translation process to FOLform we know that these expressions start with one universal quantifier left to a sequence of existential quantifiers followed by scope in form of a conjunction with conjuncts containing universal quantifies left to a disjunction with two disjuncts that may contain further universal quantifiers but no existential quantifiers and each conjunct containing y-variables of the sequence of the existential quantifiers preceeding the conjunction. 
Thus, each disjunction contains at least one disjunct with an y-variable.*)
(*STEP 1: Multiply \[ForAll]xvar\[Exists]y[num_1]...\[Exists]y[num_n](scope_And) expressions.*) 
While[numduplicates=!={}, 
num= First[numduplicates];
allexpr = First[Cases[newexpr,forAll[{xvar_x},scope_/;Not[FreeQ[scope,exists[{y[num]},scope2_]]]],{0,Infinity}]];
(*We know that there is no more than one universal quantifier left to existential quantifiers in FOLform. This is presumed in the following.
allexpr is an expression from FOLform with such a universal existential as head followed by existential quantifiers (there are more than one if there are more than one symbol on the initial tape).*)
nums= Map[First,Flatten[Cases[allexpr,{yvar_y},Infinity]]]; 
numduplicates=Complement[numduplicates,nums]; 
(*sklits are the literals in the initial clauses that contain the skolem function corresponding to the yvars in allexpr.*)
sklits= Cases[clauselits,sklit_/;Not[FreeQ[sklit,sk[number_/;MemberQ[nums,number],xvars_List]]]]; 
(*sknums are the skolem functions in ukpairs corresponding to multiplications of the y-variables yvars bounded by existential quantifiers in allexpr.*)
sknums = Cases[sks,skfun_/;MemberQ[nums,First[skfun]]];
numsduplicates = Union[numsduplicates,Map[First,sknums]]; (*This is needed because we do not want to have numbers of 
skolem-functions corresponding to yvars in the scope of a universal variable among numsduplicates in order to identify the sksingles below correctly and, thus, to identify sksublist correctly. This concerns
y-variables in the scope of universal variables  that only occur in one of the multiplied universal expressions, cf. y[5] in STM0.*)
depths = DeleteDuplicates[Map[LeafCount,sknums]]; 
(*We go through the skolem-functions from sknums with the same depth and generate sksublist and newexpr.
sksublist is a sublist that translates skolem functions to the corresponding y-variables.
newexpr is the expression we want to construct with all \[And]I applications contained.*)
nallexpr = True;
Do[sknum = Cases[sknums,skfun_/;LeafCount[skfun]===depths[[ii]]]; (*The skolem-functions of sknums with the same depth correspond to multiplied y-variables in the same scope of a multiplied universal expression.*) 
sksublist = Join[sksublist,Map[#->y[First[#],ii]&,sknum]]; 
(*sklitnums are literals in ukpairsindexed that stem from literals in the initial clauses that contain the initial skolem-function that sknum stem from.
Thus, we exclude literals from ukpairsindexed that contain members of sknum only due to substitutions of x-variables. We only want to consider literals from ukpairsindexed that correspond to literals in allexpr with an y-variable as member bound by an existential quantifier in allexpr.*)
sknumclause=DeleteDuplicates[Cases[sklits,skfun_sk/;MemberQ[Map[First,sknum],First[skfun]],Infinity]];
sklitnums = Sort[Cases[ukpairsindexed,sklit_/;Not[MemberQ[sklitsnums,sklit]]&&MemberQ[sklits, sklit2_/;Last[sklit]===Last[sklit2]&&
Intersection[Position[sklit,skfun_/;MemberQ[sknum,skfun]],Position[sklit2,skfun_/;MemberQ[sknumclause,skfun]]]=!={}],{2}],#1[[-2]]<#2[[-2]]&]; 
(*We delete all conjuncts in allexpr that do not contain a literal with the number of literal from sklits. These conjuncts do not correspond to any clause
utilized in the KromHornSolver proof.*)
newallexpr = wf[DeleteCases[allexpr,disj_Or/;FreeQ[disj,lit_/;litQ[lit]&& MemberQ[Map[Last,sklitnums],Last[lit]]],Infinity]];
vars = Flatten[Cases[newallexpr,{var_/;Head[var]===x||Head[var]===y},Infinity]]; 
newallexpr = newallexpr/.Map[Rule[#, Append[#,varindex]]&,vars]; varindex++;
(*We multiply universal expressions within newallexpr.*)  
newallexpr = newAllExp1[newallexpr,sklitnums]; 
(*We replace the literals lit with the same number as a literal sklit of sklits in newallexpr by a pair {lit,Most[sklit]}. We also do the same for all literals that occur in the same disjunction.*)
{newallexpr,sklitsnums} = newAllExp2[newallexpr,sklitnums,sklitsnums,ukpairsindexed];
(*It may well be that we have to replace the variable of the outmost universal quantifier preceding several (more than 1!) existential quantifiers differently. This is consider
by newAllExprs.*)
{newallexpr,varindex}=newAllExprs[newallexpr,newallexpr[[1,1]]];
(*We append newallexpr to nallexpr, i.e. the expression that that contains the multiplication of \[ForAll]xvar\[Exists]y[num](scope_And) and replaces allexpr in newexpr.*)
nallexpr = nallexpr && newallexpr,
{ii,1,Length[depths]}]; 
newexpr = newexpr/.allexpr->nallexpr];(*End of While loop: 
We have multiplied all \[ForAll]xvar\[Exists]y[num_1]...\[Exists]y[num_n](scope_And) expressions and replaced all literals within these expressions by a pair {lit,Most[sklit]}. We know that we have replaced all literals because we know that all conjuncts are disjuncts that contain at least one variable from the sequence of existential quantifiers. It remains to do the same for the remaining expressions, where y-variables occur in disjuncts that do not occur in the scope of a universal quantifier.*)
(*STEP 2: We go on to proceed likewise for skolem-functions that are not multiplied and that do not occur in the scope of universal quantifiers.*) 
sksingles = DeleteCases[sks,sk[num_/;MemberQ[numsduplicates,num],xvars_List]];
nums = Map[First,sksingles]; 
sklits= DeleteDuplicates[Cases[clauselits,sklit_/;Not[FreeQ[sklit,sk[number_/;MemberQ[nums,number],xvars_List]]]&&FreeQ[sklit,skfun_sk/;MemberQ[numsduplicates,First[skfun]]]]];  
sklitnums = Cases[ukpairsindexed,sklit_/;Not[MemberQ[sklitsnums,sklit]]&&MemberQ[sklits, sklit2_/;Last[sklit]===Last[sklit2]&&
Intersection[Position[sklit,skfun_sk/;MemberQ[sksingles ,skfun]],Position[sklit2,sk[number_/;MemberQ[nums,number],xvars_List]]]=!={}],{2}]; 
(*We multiply all universal expression containing y-variables corresponding to the skolem-function sksingles. This time this will only concern universal expressions with one disjunction in their scope. (We know that the expressions that correspond to the initial state and to the halting state, which do not contain a disjunction, are not multiplied.*)
newexpr = newAllExp1[newexpr,sklitnums]; 
(*We replace the literals lit with the same number as a literal sklit of sklits in newexpr by a pair {lit,Most[sklit]}. We also do the same for all literals that occur in the same disjunction.*)
{newexpr,sklitsnums} = newAllExp2[newexpr,sklitnums,sklitsnums,ukpairsindexed]; 
(*STEP 3: Replacing skolem-functions by y-variables in Most[sklits].*)
(*We add the substitions of the skolem functions sksingles by y-variables to sksublist. As a result sksublist is complete, i.e. it contains the substitutions of all skolem-functions by y-variables.*)
Do[sksingle  = sksingles[[ii]]; 
sksublist = Prepend[sksublist,sksingle->y[First[sksingle]]], 
{ii,1,Length[sksingles]}]; 
(*Since sksublist is complete now, we can replace skolem-functions by y-variables in the literals Most[sklit] that are correlated to the so far considered literals lit in newexpr.*)
newexpr = newexpr/.{lit1_/;litQ[lit1],lit2_/;litQ[lit2]}:>{lit1,lit2/.sksublist}; 
(*Standardize newexpr.*)
newexpr=varImp[inpn3[newexpr]]; 
newexpr=newexpr/.conj_And/;FreeQ[conj,And,{2,Infinity}]:>Sort[conj,uniStep[#1]<uniStep[#2]&]; 
{newexpr,sksublist}];

(*uniStep returns the number of last unified literal of expr.*)
uniStep[expr_]:=Last[Last[Last[litPairs[expr]]]];

(*printFinalExpr provides a convinient representation of the final expression.*)
printFinalExpr[expr_]:=Module[{newexpr,ii,conjs,con},
newexpr = expr/.{lit1_/;litQ[lit1],lit2_/;litQ[lit2]}:>{Last[lit1],Last[lit2]};
newexpr = newexpr //. {(quantor:(forAll|exists))[var_List/;(Length[var]>1||MemberQ[var,yvar_y]), scope_] /; freeAllQ[scope, var] :> scope,
(quantor:(forAll|exists))[var_]:>Sequence[]}; ii=1; 
While[If[Length[newexpr]>2,Head[First[newexpr]]===forAll]&&Length[newexpr]>2, 
Print["Splitting expression no: ", ii]; Print[TraditionalForm[First[newexpr]]];
ii++;newexpr=Rest[newexpr]];
conjs=Cases[newexpr,conj_Or]; 
If[conjs=!={},conjs=Apply[And,Sort[conjs,Last[Last[#1]]<Last[Last[#2]]&]];
Print["Non-splitting expresions: "]; Print[TraditionalForm[conjs]]]; 
con=Apply[And,Cases[newexpr,conj_List]];
Print["Initial and final expression: ",TraditionalForm[con]] ];

(*colorExpr prints the color diagram for the NNF-proof.*)
colorExpr[expr_,size_]:=Module[{array,singles},
array=Apply[List,DeleteCases[expr[[2]],disj_Or/;Not[FreeQ[disj,sat]],Infinity]]; 
array = wf[DeleteCases[array,{lit1_/;litQ[lit1]&&First[lit1]===True,lit2_/;litQ[lit2]&&First[lit2]===True},Infinity]];
array = Map[Apply[List,matrix[#]/.{lit1_/;litQ[lit1],lit2_/;litQ[lit2]}:>(Apply[List,Prepend[purelit[lit2],Head[lit2]]])/.yvar_y:>ToExpression[StringDelete[ToString[yvar],{"y","[","]",","," "}]]]&,array]; 
singles=Cases[array,conj_/;Not[MemberQ[conj,conj2_List]]]; 
array=Append[DeleteCases[array,single_/;MemberQ[singles,single]],singles]; 
Print[Map[ArrayPlot[#,ColorRules->{P->Red,
Faux0->LightBlue,Faux1A->LightMagenta,Faux2->Magenta,Faux3A->LightOrange,Faux4->Yellow,Faux5A->Cyan,Faux6->LightYellow,Faux7->Pink,Faux8A->Purple,Faux9->Orange,Faux10A->Brown,Faux11->LightCyan,Faux12A->LightMagenta,FauxS0->Green,FauxS->Red,FauxR->LightYellow, FauxL->LightPink,Q01->LightPurple,Q02->LightBrown,Q03->LightGreen, 
P1->RGBColor[0.1,0.5,0.5],P2->RGBColor[0.9,0.5,0.5],P3->RGBColor[0.3,0.1,0.3],P4->RGBColor[0.1,0.5,0.9],P5->RGBColor[0.9,0.5,0.1],P6->RGBColor[0.5,0.5,0.1],P7->RGBColor[0.5,0.1,0.5],P8->
RGBColor[0.5,0.5,0.9],P9->RGBColor[0.5,0.9,0.5],P10->RGBColor[0.1,0.3,0.3],P11->RGBColor[0.3,0.3,0.1],P12->RGBColor[0.1,0.9,0.5],
H->Blue},ImageSize->size]&,array]]];


(*SECTION 6: Checking the Loop-Criteria*)

(*This checks 2 loop-criteria: One for tableaux, one for the NNF-calculus. The one for tableaux can easily be refuted by some of our examples. 
The criterion for the NNF-calculus is not not refuted by our examples. Its does not suffice to ensure termination because of sequenceQ. 
It does not suffice to check for patterns according to our paper.
We stopped investigating the loop criteria further after recognizing that this is futile.*)

(*duplicateUKpairs returns a list of lists of numbered ukpairs that are identical up to depth 1.*)
duplicateUKpairs[ukpairsind_]:=Module[{rukpairs=ukpairsind,duplicates={},duplicate},
While[rukpairs=!={},
duplicate=Cases[rukpairs,ukpair_/;skolemReduce[First[ukpair]]===skolemReduce[First[First[rukpairs]]]];
If[Length[duplicate]>1,duplicates=Append[duplicates,duplicate]];
rukpairs=Complement[rukpairs,duplicate]];
duplicates];

(*duplicateConjs returns a list of lists with substitutions that are identitical up to depth 1.*)
duplicateConjs[conjs_]:=Module[{conjderivates,duplicates={},duplicateconj},
(*STEP 1: Ignoring indices of level > 1 in the literals*)
conjderivates=MapIndexed[{#1/.{lit1_/;litQ[lit1],lit2_/;litQ[lit2]}:>{firstIndex[lit1],firstIndex[Most[lit2]]},First[#2]}&,conjs];
(*STEP 2: Checking for duplicates up to index level 1: We only check whether one set of pairs of literals is a PART of another. In tableau and the non-splitting case this comes to the same as checking for identity because the sets have always length 2 but in the splitting case it may make a difference.*)
While[Length[conjderivates]>1,
duplicateconj=Cases[conjderivates,con_/;(Complement[conjderivates[[1,1]],First[con]]==={}||Complement[First[con],conjderivates[[1,1]]]==={})];  
If[Length[duplicateconj]>1,duplicates=Append[duplicates,conjs[[Map[Last,duplicateconj]]]]];
conjderivates=Complement[conjderivates,duplicateconj]]; 
duplicates];

(*loopIso returns a list of lists with isomorphic ukpairs / isomorphic substitutions in multiplied \[And]I expressions.*)
loopIsomo[duplicates_,reference_]:=Module[{nduplicates={},nduplicate,duplicate,ylits,poslits},
If[duplicates==={},Return[{}]];
(*STEP 1: Consider the position of sk-functions / y-variables in the substituted literals.*)
Do[duplicate=duplicates[[ii]];
(*tableau*)
If[reference==="tableau", poslits = MapIndexed[{#1/.lit_/;litQ[lit]:>(lit/.yvar_y:>Position[lit,yvar]),#2}&,Map[First,duplicate]],
(*"NNF"*) 
poslits =  MapIndexed[{#1/.lit_/;litQ[lit]:>(lit/.yvar_y:>Position[lit,yvar]),#2}&,Map[Last,duplicate,{2}]]];
(*STEP 2: Checking Isomorphy, - we only check whether one set of pairs of literals is a PART of another. In tableau and the non-splitting case this comes to the same as checking for identity because the sets have always length 2 but in the splitting case it may make a difference.*)
While[poslits=!={}, 
nduplicate=Cases[poslits,poslit_/;(Complement[Map[Most,First[poslit]],Map[Most,First[First[poslits]]]]==={}||Complement[Map[Most,First[First[poslits]]],Map[Most,First[poslit]]]==={})]; 
If[Length[nduplicate]>1, nduplicates = Append[nduplicates,duplicate[[Flatten[Map[Last,nduplicate]]]]]];  
 poslits = Complement[poslits,nduplicate]],
{ii,1,Length[duplicates]}];
nduplicates];
(*sequenceQ checks for IMMEDIATE repetitions in the inference steps (in tableau as well as in the NNF-calculus).
In the case, we have repetitions that are NOT IMMEDIATE repetitions, their distance >0.
The input is a list of pairs of form {{no1,no2,no3},no4} (tableau case) or {{no1a,no1b,no2a,no2b},no4} (NNF) 
sorted by no4 (= the number of a ukpair in ukpairsindexed, i.e. inference steps in tableau).*)
sequenceQ[pairs_,reference_]:=Module[{rpairs=Rest[pairs],rpair,seqs={},iseqs,seq={First[pairs]},sucseq,fseqs={},test,value=True},
(*We first generate a list seqs of sequences of immediately following ukpairs (no4s) that do not share any first member.*) 
While[rpairs=!={},
rpair= First[rpairs];
If[Last[rpair]===(Last[Last[seq]]+1)&&FreeQ[seq,First[rpair]],  seq=Append[seq,rpair], seqs = Append[seqs,seq]; seq = {rpair}];
rpairs = Rest[rpairs]]; seqs = Append[seqs,seq]; iseqs=seqs;
(*We now search for the immediately following sequence such that the first members of one sequence is a subpart of the first members of the other and the  first members of the last members are identical.*)
While[Length[seqs]>1,
seq=First[seqs]; seqs = Rest[seqs]; 
sucseq=First[seqs]; 
If[Last[Last[seq]]+1===Last[First[sucseq]]&&First[Last[seq]]===First[Last[sucseq]] &&
(SubsetQ[Map[First,sucseq],Map[First,seq]]||SubsetQ[Map[First,seq],Map[First,sucseq]]),  
(*fseqs is the final sequences of repeteating inference steps.*)
fseqs=Append[fseqs,Take[seq,{First[FirstPosition[seq,pair_/;First[pair]===sucseq[[1,1]],False,{1},Heads->False]],Length[seq]}]]; 
If[(*Length[seq[[1,1]]]===3*)reference===True,test=True,
(*In NNF-C. we have splitting expressions that contain more than one conjunct. 
Therefore, we have to test whether all parts of the isomorphic expressions are part of an immediate repeating sequence of unifications. This is relevant for STM11a.*)
test=Complement[DeleteDuplicates[Flatten[Map[Take[First[#],-2]&,Flatten[Complement[DeleteCases[iseqs,sucseq],fseqs],1]]]],DeleteDuplicates[Flatten[Map[Take[First[#],-2]&,Flatten[fseqs,1]]]]]==={}]; 
If[test,Print["Immediate repeating sequence found: ",Append[fseqs,sucseq]];  value= False;Break[]], 
If[fseqs=!={}, (*We can simplify seqs in the ase of NNF-C. if we already know that some part of isomorphic duplicates are not part of an immediate sequence of repeating unifications.*)seqs =  DeleteCases[seqs,seqspair_/;MemberQ[Map[Take[First[#],-2]&,fseqs],Take[First[seqspair]-2]]]; fseqs={}]]];
value];

(*loopTableau checks whether the Loop-Criterion applies for tableau.*)
loopTableau[ukpairsind_,sksublist_]:=Module[{duplicates,pairs={},duplicate,nentry},
(*STEP 1: Identifying isomorphic substitutions of pairs of unifiable literals (= kpairs).*)
(*Step 1.1: Identifying kpairs identical if all indices of level >1 are deleted.*)
duplicates = duplicateUKpairs[ukpairsind]; 
If[duplicates==={}, Print["No duplicates."]; Print["Loop Criterion Tableau not satisfied."], 
(*Step 1.2: Checking whether they are isomorphic.*)
duplicates = loopIsomo[duplicates/.sksublist,"tableau"];  
If[duplicates==={}, Print["No ismorphic ukpairs."]; Print["Loop Criterion Tableau not satisfied."], 
(*We generate a list of pairs {{no1,no2,no3},no4} with no1,no2 = numbers of the initial literal that a unified pair literals stems from, 
no3 = number of list of isomorphic pairs of literals in duplicates,
no4 = number ind of unified pair of literals in ukpairsind.*)
(*STEP 2: Checking wethere the isomorphic kpairs are immediately connected by expansion steps.*)
(*Step 2.1: Preparation. We only have to consider pairs of form {{no1,no2,no3},no4} with no1,no2 = number of the  initial literals that the unified literals stem from,
no3 = number of duplicates they stem from, no4 = number of inference step in tableau (= number ind of unified pair of literals in ukpairsind).*)
Do[duplicate=duplicates[[ii]];
nentry=Map[If[Last[#[[1,1]]]<Last[#[[1,2]]],{{Last[#[[1,1]]],Last[#[[1,2]]],ii},Last[Last[#]]},{{Last[#[[1,2]]],Last[#[[1,1]]],ii},Last[Last[#]]}]&,duplicate]; 
pairs =Join[pairs,nentry],
{ii,1,Length[duplicates]}];  
(*Step 2.2: Checking for a sequences immediately repeating of unification steps.*)
If[sequenceQ[Sort[pairs,Last[#1]<Last[#2]&],True],Print["No immediately repeating unification sequence."]; 
Print["Loop Criterion Tableau not satisfied."],Print["Immediately repeating unification sequence."]; Print["Loop Criterion Tableau satisfied."]]]]];

(*loopNNFAux prepares the application of sequenceQ in loopNNF. It generates a list of npairs {{no1a,no1b,no2a,no2b},no4} with no1a,no1b = numbers of the initial literal that a unified pair literals stems from, 
no2a,no2b = numbers of the list of isomorphic expressions in duplicates, no4 = number of inference step in tableau (=ind of unified pair of literals in ukpairsind).*)
loopNNFAux[duplicates_]:=Module[{pairs={},duplicate,npair,npairs={},value=True}, 
Do[duplicate=duplicates[[ii]]; 
If[Not[FreeQ[duplicate,List,{3}]], pairs = Join[pairs,Flatten[Map[{Last[First[#]],ii,Last[Last[#]]}&,duplicate,{2}],1]], pairs = Join[pairs,Map[{Last[First[#]],ii,Last[Last[#]]}&,duplicate]]],
{ii,1,Length[duplicates]}];
While[pairs=!={},
npair = Cases[pairs,pair_/;Last[pair]===Last[First[pairs]]]; 
If[Length[npair]===2,If[npair[[1,1]]<npair[[2,1]],npairs = Append[npairs, {{npair[[1,1]],npair[[2,1]],npair[[1,2]],npair[[2,2]]},Last[First[npair]]}],
npairs = Append[npairs, {{npair[[2,1]],npair[[1,1]],npair[[2,2]],npair[[1,2]]},Last[First[npair]]}]]];
pairs = Complement[pairs,npair]]; 
Sort[npairs,Last[#1]<Last[#2]&]];

(*loopNNF checks whether the Loop-Criterion applies for the NNF-calculus.*)
loopNNF[expr_]:=Module[{allexexprs,allexexprsrest,splitpairs,splitduplicates,splitrestduplicates,nonsplitduplicates,duplicates,pairs,value=True},
(*The crucial difference to tableau consists in multiplying \[ForAll]\[Exists]-expressions (I call them "splitting expressions"). 
We have to distinguish the \[And]I-multiplication of these expressions to the \[And]I-multiplication of \[ForAll]-expressions without \[Exists] in their scope ("non-splitting expressions".*)
(*SPLITTING CASE.*)  
allexexprs= Cases[expr,forAll[{xvar_x},exists[yvars_List,scope_]],{0,Infinity}];
splitpairs = Map[litPairs,allexexprs]; 
nonsplitduplicates=loopIsomo[duplicateConjs[Map[litPairs,Cases[DeleteCases[expr,forAll[{xvar_x},exists[yvars_List,scope_]],{0,Infinity}],disj_Or,{0,Infinity}]]],"NNF"]; 
(*splitduplicates identifies isomorphic splitting expressions. We identify them by the substitutions of their literals. We only claim that 
the substitution of the literals of one expression is isomorphic to a PART of the substitution of the literals of the other expression.
Otherwise, we could not decide non-halting cases that arising from nesting cells.*)
splitduplicates =loopIsomo[duplicateConjs[splitpairs],"NNF"]; 
If[splitduplicates==={}, Print["No splitting duplicates."],
(*We have to consider \[And]I-multiplication (i) in the non-splitting expressions (=nonsplitpairs) as well as (ii) within the splitting expressions that are not isomorphic (= splitrest) to check whether the isomorphic expressions are immediately connected via other isomorphic \[And]I-multiplications. *)
allexexprsrest = Cases[allexexprs,allexexpr_/;FreeQ[allexexpr,lit_/;litQ[lit]&&MemberQ[Flatten[splitduplicates],lit]]]; 
splitrestduplicates =  Flatten[Map[loopIsomo[duplicateConjs[#],"NNF"]&,Map[litPairs,Map[Cases[#,disj_Or,{0,Infinity}]&,allexexprsrest],{2}]],1];
(*splitrest=DeleteCases[splitpairs,splitpair_/;MemberQ[splitduplicates,splitpair,{2}]]; *)
duplicates =Union[splitduplicates,splitrestduplicates,nonsplitduplicates]; 
(*pairs prepares the check for an immediate sequence of \[And]I-multiplications involving splitting expressions.*)
pairs = loopNNFAux[duplicates];
If[pairs=!={},
value=sequenceQ[pairs,False];
If[value===True,  Print["No immediate sequence of isomorphic splitting expressions."],
Print["Immediately repeating sequence of splitting expressions."]; Print["Loop Criterion NNF satisfied."]], 
Print["No related isomorphic splitting expressions."]]];
(*NON-SPLITTING CASE.*)
(*We identify isomorphic non-splitting expressions.*)
If[value===True, 
splitduplicates = Flatten[Map[loopIsomo[duplicateConjs[#],"NNF"]&,Map[litPairs,Map[Cases[#,disj_Or,{0,Infinity}]&,allexexprs],{2}]],1];
 duplicates = Union[splitduplicates,nonsplitduplicates]; 
If[duplicates==={}, Print["No non-splitting duplicates."];  Print["Loop Criterion NNF not satisfied."],
(*Finally, we check whether they are immediately connected.*)
pairs = loopNNFAux[duplicates];
If[pairs=!={}, 
value=sequenceQ[pairs,True];
If[value===True,  Print["No immediate sequence of isomorphic non-splitting expressions."]; Print["Loop Criterion NNF not satisfied."], 
 Print["Immediately repeating sequence of non-splitting expressions."]; Print["Loop Criterion NNF satisfied."]],  
Print["No related isomorphic non-splitting expressions."]]]]];


(*SECTION 7: METAFUNCTIONS*)

(*iterate4 first generates the tableau for iclauses and the corresponding NNF-proof FOLfrom. Then it decides whether a Loop Criterion to tableau and the NNF-calculus applies.*)
iterate4[{iclauses_,FOLform_},upperbound_]:=Module[{clauses,tableau,ikpairs,lit, xvars={},output,ukpairs,ukpair,ukpairsindexed,expr=FOLform,value,sksublist},
(*GENERATING TABLEAU.*) 
    (*Initializing step.*)
	itscounter = 0;
	clauses = Sort[iclauses,negativeClauseQ[#]&]; (*Print["initial clauses: ", clauses]; *)
	Map[Map[(mpNoLit[Last[#]] = #)&, #]&, clauses];
	(*ikpairs is a set of pairs of numbers from unifiable literals in the initial clauses.*)
	ikpairs = Cases[Subsets[Map[#/.xvar_/;Head[xvar]===x:>Append[xvar,no[#]]&, Flatten[clauses]], {2}], {l1_, l2_}/;unify[l1, l2]=!=False:>{no[l1],no[l2]}];
	unifiableQ[l1_,l2_]= False;  
	Map[(unifiableQ[First[#],Last[#]]=True; unifiableQ[Last[#],First[#]]=True)&, ikpairs]; 
	Map[(lit=#; mpLitClauses[no[lit]] = Cases[clauses,c_/;Apply[Or,Map[(unify[#,lit/.(xvar_x:>Append[xvar,no[#]])]=!=False)&, c]]]) &, Flatten[clauses]];
	Map[(mpClauseXvars[#]=Union[Flatten[Map[Cases[#,x[num_],{0, Infinity}]&, #]]]; xvars = Join[xvars, mpClauseXvars[#]]) &, clauses];
	Map[(mpXvarIt[#]=0)&, xvars];  
	(*End of the initializing step.*)
	(*Start the iteration. F means that a branch is a failure, S that it is a success. We need only to consider negative clauses. See Handbook of automated Reasoning, vol 2, p. 2040. *)
         tableau={{First[clauses],"F"}};
	(* Call solve for each initial tableau. solve will be called recursively within it.*)
{value,tableau}=solve[tableau,clauses,1,upperbound]; 
Map[Clear, {mpLitClauses, unifiableQ, mpClauseXvars, mpNoLit, mpXvarIt}];
tableau = Join[{First[tableau]},MapIndexed[{Flatten[{Take[First[First[tableau]],Sequence@@#2],#1}],"S"}&, Rest[sbranch[Last[tableau]]]]]; 
If[value===True, 
  Print["Tableau proof found after ", itscounter, " steps. Main branch: "]; printTableau[{First[tableau]}], 
  Print["No tableau proof found after ", itscounter, " steps. Main branch:  "]; printTableau[{First[tableau]}]];
Print["The evolution of the main branch in tableau up to ", upperbound, " steps as color diagram: "]; colorTableau[First[tableau],50(*upperbound/20*)];
(*GENERATING THE CORRESPONDING PROOF IN THE NNF-CALCULUS*)
(*Preparating steps*)
(*In the sat-case (i.e. the case where no proof is reached after upperbound steps) an F-branch to expand is left. We delete it and consider whether the Loop-Criterion would apply so far. We also know that we have not reached the halting state. Therefore, we delete the corresponding expression in FOLform.*)
If[value===sat, tableau = DeleteCases[tableau,branch_/;Last[branch]==="F"]; 
expr =  wf[DeleteCases[FOLform,lit_/;litQ[lit]&&Last[lit]===Last[Last[Last[iclauses]]],Infinity]]];
(*ukpairs specifies the succession of inference steps to unify kpairs in the KromHornSolver.*) 
ukpairs = Map[Take[sbranch[#],-2]&,Sort[tableau,Length[First[#1]]<Length[First[#2]]&]]; 
(* We number the unified kpairs and insert the number left to the number of the literals in ukpairsindexed.*) 
ukpairsindexed=ukpairs;
 Do[ukpair= ukpairs[[ii]]; ukpairsindexed = ReplacePart[ukpairsindexed,ii->{Insert[First[ukpair],ii,-2],Insert[Last[ukpair],ii,-2]}],{ii,1,Length[ukpairs]}];
(*We generate an expression including all \[And]I-applications of the proof in the NNF calculus as well as all unification of pairs of literals corresponding to the ii-th unification by an ii-th expansion step in the tableau construction. The kpairs (pairs of literals) and their substitutions are identified by replacing each literal lit by {lit,ulit}, where ulit is the literal after unification. Like the indexed kpairs of ukpairsindexed ulit contains the number signifying the number of the inference step  to unify lit with its corresponding skolem-literal culit in ukpairsindexed.  culit contains the same number as last member as ulit. Thus, we can read off from newexpr the proof seach in the NNF-calculus that mimics the proof search in the KromHornSolver.*)
(*We first delete expressions relating to clauses not used in the KromHornSolver proof. Since the initial state and halting state are used and are the only clauses of length 1, we only have to search for disjunctions.*)
expr = wf[DeleteCases[expr,disj_Or/;FreeQ[disj,lit_/;litQ[lit]&& MemberQ[Map[Last,Flatten[ukpairs]],Last[lit]]],Infinity]];
(*The remaing steps are performed by newExpr: Multiplying expressions and identifying which literals are unified and how x variables have to be replaced by y variables for unification.*)
{expr,sksublist}=newExpr[expr,Flatten[clauses],ukpairsindexed];  expr=wf[DeleteCases[expr,disj_Or/;Not[FreeQ[disj,sat]],Infinity]];
Print["Final expression of the proof search in the NNF-calculus: ", tradi[expr]];
Print["The NNF-C. proof up to ", upperbound, " steps (splitting expressions + rest separated) as color diagram: "]; colorExpr[expr,50];
(*CHECKING THE LOOP-CRITERIA*)
loopTableau[MapIndexed[{#1,#2}&,ukpairs],sksublist];
loopNNF[expr]; 
(*Return the decision whether a proof was found up to upperbound steps in tableau.*)
If[value,  Return[False],If[itscounter===upperbound, Return["No decision up to upper bound."],Return[sat]]]; 
sat];

(*proofCheck (i) generates the tableau up to upperbound inference steps (at most, in the case a proof is found the tableau terminates with the proof), (ii) checks whether the LC for tableau applies, (iii) generates a formula corresponding to the tableau in the NNF-calculus, and (iv) checks whether the LC for the NNF-calculus applies.*)	
proofCheck[stm_,upperbound_]:=(Print[STM[stm,Floor[upperbound/4]]];iterate4[STM2Clauses[stm],upperbound]);

End[]
Protect[exists,forAll,A,B,x,y,xx,yy,uu,vv,zz,sat,oo,ii,jj,kk,and,or,
R,L,S,H,W,G,sk,P,
Q01,Q02,Q03,P1,P2,P3,P4,P5,P6,P7,P8,P9,P10,P11,P12,P13,
Faux0,FauxR,FauxL,Faux1A,Faux2,Faux3A,Faux4,Faux5A,Faux6,Faux7,
Faux8A,Faux9,Faux10A,Faux11,Faux12A,FauxS0,FauxS,
Rrule,Lrule,Wrule,Srule,STM,
tradiRules,tradi,untradiRules1,untradiRules2,untradi,normal,
freeAllQ,wf,indicesToSameLevel,varImp,varImpSort,
indicesToOriginalLevel,varExp,varExpSort,maxIndices,
qSeq,minIndices1,minIndices2,minIndices,matrix,
pn3,pn5,pn9,pn10,inpn3,inpn5,apn,pn,
CTM2Clauses,Clauses2FOL,STM2Clauses,folForm,
skolemize,maxIndicesForAll,toClauseNormalForm,prependBoolToLits,appendNoToLits,
negativeClauseQ,sbranch,notation,status,firstBranch,no,purelit,
unifyArgs,unifyLits,unify,singleUnification,
expansionStep,infExp,performInfStep,regularityQ,
firstIndex,skolemReduce,solve,printTableau,colorTableau,
litQ,litPairs,newAllExp1,newAllExp2,newAllExprs,newExpr,uniStep,printFinalExpr,colorExpr,
duplicateUKpairs,duplicateConjs,loopIsomo,sequenceQ,loopTableau,loopNNFAux,loopNNF,
iterate4,proofCheck]
EndPackage[]

