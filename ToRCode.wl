(* ::Package:: *)

(* version 2023-09-10.0*)


BeginPackage["ToRCode`",{"SymbolicC`","CCodeGenerator`"}];


RCodeFor::usage = "returns the code for an R function named name "<>
	" that computes the value of expression expr";
RSymbolic
RCompiled
polyroot


Begin["`Private`"];


UniqueLeaves[expr_]:=Union[Flatten[Apply[List,expr,{0,Infinity}]]];
FreeVariableQ[expr_]:=
	MatchQ[expr,_Symbol]\[And] (*it is a symbol, and*)
		\[Not]MemberQ[Attributes[expr],Protected](*does not come from Mathematica*);
FreeVariables[expr_]:=expr//UniqueLeaves//Select[FreeVariableQ];


ShiftToEnd[list_,toend_]:=Join[Complement[list,toend],Intersection[list,toend]]


UnRoot[expr_]:=Block[{roots,rules,rootless},
	roots=Cases[expr,_Root,Infinity]//DeleteDuplicates;
	rules=MapIndexed[#1->Symbol["r"<>ToString[#2[[1]]]]&,roots];
	rootless=expr/.rules;
	{rootless,rules/.(l_->r_):>(r->l)}
]


FunctionArguments[expr_,rootnames_]:=ShiftToEnd[expr//FreeVariables,rootnames];
FunctionArguments[func_CompiledFunction]:=Cases[func,_Function][[1,1]];


GetFunction[program_,name_]:=FirstCase[program,CFunction[_,name,__],2];


CompileWithoutRoots[expr_,name_]:=Block[{rootless,roots,arguments},
	{rootless,roots}=UnRoot[expr];
	arguments=FunctionArguments[rootless,First/@roots];
	{Compile[Evaluate[arguments],Evaluate[rootless]],roots}
];


constantPowerPattern=CBlock[{
	CDeclare["mint",CAssign["S0",exp_/;(NumberQ[exp]\[And]exp>0)]],
	CDeclare["mreal",CAssign["S1",base_]],
	CDeclare["mbool",CAssign["S2",s2_]],
	CIf[__],
	CAssign[result_,r0_?NumberQ],
	loop:CWhile["S0",__],
	CIf["S2",__]
}];
reciprocalSqrtPattern=CBlock[{
	CDeclare["mint", CAssign["S0",
		CCall["FP0",{
			CCast[CPointerType["void"], CAddress[result_String]],
			CCast[CPointerType["void"],CAddress[arg_String]],
			1,"UnitIncrements",4}]
	]],
	CComment["Internal`ReciprocalSqrt"],{CAssign["err",_],CIf["err",CGoto["error_label"]]}
}];


identSubstitutions={"\:2081"->"1","\:2082"->"2","\:2083"->"3","\:2084"->"4","\:2085"->"5","\:2086"->"6","\:2087"->"7","\:2088"->"8","\:2089"->"9","\[Tau]"->"tau"};


Options[RCodeFor]={RSymbolic->False, RCompiled->False};


RCodeFor[anExpr_, aName_String, OptionsPattern[]]:=Block[{
	expr=anExpr,
	name=aName,
	roots,
	args,argSubstitutions,numberedArgs,
	program,initialize, compute,
	varTest,vars,
	assignments,assignedVars,
	argumentHolders,argHolderSubstitutions,constantQ,constantSubstitutions,
	programOut,Rcode
	},
	
	{compiledP[name],roots}=CompileWithoutRoots[expr,name];
	csym[name]=SymbolicCGenerate[compiledP[name],name];
	
	args=StringReplace[SymbolName[#],identSubstitutions]&/@FunctionArguments[compiledP[name]];
	roots=Replace[roots,s_Symbol:>Symbol[StringReplace[SymbolName[s],identSubstitutions]],Infinity];
	argSubstitutions=MapIndexed["A"<>ToString[#2[[1]]]->#1&,args];
	numberedArgs=First/@argSubstitutions;
	
	program=csym[name];
	initialize=GetFunction[program,"Initialize_"<>name];compute=GetFunction[program,name];
	
	(* For constant propagation, get all symbols that are never assigned to within the computing function *)
	varTest=StringMatchQ[#,{"I0_*","R0_*"}]&;
	vars=compute//UniqueLeaves//Cases[_String?varTest];
	assignments=Cases[compute,CAssign[var_,val_]:>{var,MemberQ[numberedArgs,val]},Infinity]//Sort//Union;
	assignedVars=Cases[assignments,{var_,False}:>var];
	argumentHolders=Complement[Cases[assignments,{var_,True}:>var]//Sort//Union,assignedVars];
	argHolderSubstitutions=Thread[#1->#2&[argumentHolders,args]];
	(* Now generate a list of constant assignments *)
	constantQ=MemberQ[Complement[vars,assignedVars],#]&;
	constantSubstitutions=Cases[initialize,
		CAssign[var_?constantQ,CCast[_,value_]|value_]:>(var->ToExpression[value]),
		Infinity
	];
	
	compute=compute /.
		Join[constantSubstitutions,argHolderSubstitutions] /.
		{
			CDeclare[_,CAssign["err",_]]->Nothing,
			CDeclare[_,Except[_CAssign]]->Nothing,
			CCast["mreal",val_]:>val,
			CBlock[head_,tail__]:>CBlock[{head,tail}],
			_CReturn->Nothing,
			CAssign[_,var_String]/;MemberQ[numberedArgs,var]->Nothing,
			CCall[CPointerMember["funStructCompile",_],_]->Nothing,
			CLabel["error_label"]->Nothing
		} /.
		{} -> Nothing /.
		argSubstitutions /.
		{
			constantPowerPattern:>CAssign[result,CCall["ConstantPower",{exp,base,s2,r0}]],
			reciprocalSqrtPattern:>CAssign[result,COperator[Divide,{1,CCall["sqrt",{arg}]}]],
			CAssign[CDereference["Res"],result_]:>CReturn[result],
			{CLabel["error_label"],__}:>Nothing
		} /.
		CCall["ConstantPower",{exp_,base_,0,1}] :> CCall["pow",{base,exp}] /.
		(* evaluate constant ifs *)
		CIf[COperator[op_,{a_?NumberQ,b_?NumberQ}],iftrue_,iffalse_:Nothing] :>
			If[op[a,b],iftrue,iffalse] //.
		(* fold consecutive assignments to the same variable *)
		{pre___,CAssign[var_,val1_?NumberQ],CAssign[var_,val2_],post___} :> 
			{pre,CAssign[var,val2//.var->val1],post} /.
		CFunction[_,name_,{{_,"libData"},args__,{_,CDereference["Res"]}},body_] :>
			CFunction["double",name,{args}[[;;-Length[roots]-1]],body];
	
	rootAssignments = roots /.
		(r_->Root[poly_,n_]) :> CAssign[r,CCall["Re",CArray[
			CCall[polyroot,CCall["c",CExpression/@CoefficientList[#1[x],x]]],#2]]&
			[poly,Unevaluated[n]]] /.
		{
			Power[base_,2]:>HoldForm[base*base],
			Power[base_,exp_]:>pow[base,exp]
		};
	
	programOut = compute /.
		CFunction[stuff__,CBlock[{body__}]] :>
			CFunction[stuff,CBlock[{Splice[rootAssignments],body}]];
	
	Rcode = StringReplace[programOut//ToCCodeString, {
		Shortest["pow("~~base__~~","~~Longest[" "...]~~exp__~~")"] :> base<>"^"<>exp,
		"mreal" -> "",
		"double"~~" "..~~name:Except["("].. :> name<>" <- function",
		"return"~~" "..~~expr:Except[";"].. :> expr,
		";\n" -> "\n"
	}]<>"\n";
	Rcode=If[OptionValue[RCompiled],
		"library(compiler)\n" <> Rcode <> 
			"print(\"Now compiling "<>name<>"\")\n"<>
			name <> " <- cmpfun(" <> name <> ")\n\n",
		Rcode <> "\n"
	];
	If[OptionValue[RSymbolic], {Rcode, compute}, Rcode]
];


End[];


EndPackage[];
