(* ::Package:: *)

(* ::Subsection:: *)
(*Package Definition*)


BeginPackage["LabFis`labfis`"];

Lsqr::usage="Lsqr[...]";
Lsqr::fmt="Invalid input format, use {x1...xn}, {y1...xn}, e/{e1...en} or {{x1,y1}, ... , {xn,yn}}, e/{e1...en}";
Lsqr::dat="Invalid input data, xy mismatch or Null present";
Lsqr::len1="Length mismatch, x=`1` y=`2`";
Lsqr::len2="Length mismatch, n=`1` e=`2`";
Lsqr::amb="Ambiguous call, case 2x2";
Lsqr::mor="At least 2 points are required";
Lsqr::opt="Invalid option value";

LsqrSimple::usage="Lsqr[...]";

RoundUp::usage="RoundUp[num, options]";

JoinCols::usage="CJoin[lists]";
AppendCols::usage="CAppend[list,column]";

Propagate::usage="Propagate[expr,{vars}]";
StatError::usage="StatError[list]";
ErrorFormat::usage="ErrorForm[value,error]";
ErrorPair::usage="ErrorForm[value,error]";

ErrorRound::usage="ErrorRound[value,error] or ErrorRound[error]";

PSolve::usage="PSolve[expr,{{var,val,err},{const,val},...},options]";
PSolve::fmt="Invalid input format";
PSolve::opt="Invalid option value";

Nrt::usage="Nrt[e,val]";

Begin["`Private`"];


(* ::Subsection:: *)
(*Common*)


Nrt[e_,v_]:=v^(1/e)


RoundUp[a_] := If[FractionalPart[a]>=0.5,Ceiling[a],Floor[a]]


(* ::Subsection:: *)
(*List Manipulation*)


JoinCols[lists__]:=Transpose@{lists}


AppendCols[array_,columns__]:=ArrayFlatten@{Prepend[(List/@#&)/@{columns},array]}


(* ::Subsection:: *)
(*Error*)


ErrorForm/:Format[ErrorForm[s_,v_,e_,rv_,re_,exp_]]:=s
ErrorForm/:ErrorForm[s_,v_,e_,rv_,re_,exp_]["val"]:=v
ErrorForm/:ErrorForm[s_,v_,e_,rv_,re_,exp_]["err"]:=e
ErrorForm/:ErrorForm[s_,v_,e_,rv_,re_,exp_]["rval"]:=rv
ErrorForm/:ErrorForm[s_,v_,e_,rv_,re_,exp_]["rerr"]:=re
ErrorForm/:ErrorForm[s_,v_,e_,rv_,re_,exp_]["rexp"]:=exp
ErrorForm/:ErrorForm[s_,v_,e_,rv_,re_,exp_]["pair"]:={v,e}
ErrorForm/:ErrorForm[s_,v_,e_,rv_,re_,exp_]["rpair"]:={rv,re}


ErrorPair[v_,e_]:={ErrorRound[v,e],ErrorRound[e]}


ErrorRound[e_]:=Module[{mt,ex},
{mt,ex}=MantissaExponent[e];
RoundUp[10*mt]*10^(ex-1)
]


ErrorRound[n_,e_]:=Module[{mtn,exn,mte,exe,err},
err=ErrorRound[e];
{mtn,exn}=MantissaExponent[n];
{mte,exe}=MantissaExponent[err];
RoundUp[mtn*10^(exn-exe+1)]*10^(exe-1)
]


ErrorFormat[v_,e_]:=Module[{manv,expv,mane,expe,re,rv,expdiff,expm,ip,rem},

{manv,expv}=MantissaExponent[v];
{mane,expe}=MantissaExponent[e];

expdiff=expv-expe+1;

re=RoundUp[mane*10]/10.0;
rv=RoundUp[ manv*10^expdiff]/(10.0^expdiff);

expm=Floor[(expv+expe-1)/2];

rv=rv *10^(expv-expm);
re=re *10^(expe-expm);

ip=IntegerPart[expm/3];
rem=Sign[expm]Mod[Abs[expm],3];

ErrorForm@@{"("<>ToString[NumberForm[rv 10^rem,ExponentFunction->(Null&)]]<>" \[PlusMinus] "<>ToString[NumberForm[re 10^rem,ExponentFunction->(Null&)]]<>")"<>If[ip==0,"","\[Times]10e"<>ToString[3ip]],v,e,rv,re,3ip}
]


Propagate[f_,v_]:= Sqrt[Sum[(D[f,v[[i]]]*Symbol["\[Sigma]"<>SymbolName[v[[i]]]])^2, {i,1,Length[v]}]]


StatError[list_]:=StandardDeviation[list]/Sqrt[Length[list]]


PSolve[f_, params_List, OptionsPattern[]]:= Module[{rules, expr, vars, val, err},

rules = Flatten[Switch[Length[#],
1, {},
2, {#[[1]] -> #[[2]]},
3, {#[[1]] -> #[[2]], Symbol["\[Sigma]"<>SymbolName[#[[1]]]]->#[[3]]},
_, Message[PSolve::fmt]; Abort[]] & /@ params];

vars = Select[params, Length[#] == 3&][[All, 1]];

expr = Propagate[f, vars];
val = ReplaceAll[f, rules];
err = ReplaceAll[expr, rules];

Switch[OptionValue["ShowPropagation"],
True, {expr, val, err},
False, {val, err},
_, Message[PSolve::opt]; {}
]
]


(* ::Subsection:: *)
(*Least Squares*)


LsqrFit/:LsqrFit[a_,b_][x_]:=a x + b
LsqrFit/:Format[LsqrFit[a_,b_]]:="LsqrFit"[Panel[ToString[N[a "x" + b]],
FrameMargins->1]]


Lsqr[x_List, y_List, e_List]:= Module[{N,w,sw,swx,swy,swx2,swyx,delta,a,b,ea,eb},

N = Length[x];
If[N != Length[y], Message[Lsqr::len1, N, Length[y]]; Abort[]];
If[N != Length[e], Message[Lsqr::len2, N, Length[e]]; Abort[]];

w = 1/e^2;

sw = Total[w];
swx = Total[w*x];
swy = Total[w*y];
swx2 = Total[w*x*x];
swyx = Total[w*x*y];

delta = sw swx2 - swx^2;

a = (sw swyx - swx swy)/delta;
b = (swy swx2 - swyx swx)/delta;
ea = Sqrt[sw/delta];
eb = Sqrt[swx2/delta];

{{"N",N},{"Sw",sw},{"Swx",swx},{"Swy",swy},{"S2wx",swx^2},{"Swx2",swx2},
{"Swyx",swyx},{"Delta",delta},{"a",a},{"b",b},{"ea",ea},{"eb",eb},
{"a", ErrorFormat[a, ea]}, {"b", ErrorFormat[b, eb]},
{"f[x]", LsqrFit[a,b]}}
]


Lsqr[x_List, y_List, e_]:= Module[{N,sx,sy,sx2,syx,delta,a,b,ea,eb},

N = Length[x];
If[N != Length[y], Message[Lsqr::len1, N, Length[y]]; Abort[]];

sx = Total[x];
sy = Total[y];
sx2 = Total[x*x];
syx = Total[x*y];

delta = N sx2 - sx^2;

a = (N syx - sx sy)/delta;
b = (sy sx2 - syx sx)/delta;
ea = Sqrt[N e^2/delta];
eb = Sqrt[sx2 e^2/delta];

{{"N",N}, {"Sx",sx}, {"Sy",sy}, {"S2x",sx^2}, {"Sx2",sx2}, {"Syx",syx}, 
{"Delta",delta}, {"a",a}, {"b",b}, {"ea",ea}, {"eb",eb},
{"a", ErrorFormat[a, ea]}, {"b", ErrorFormat[b, eb]},
{"f[x]", LsqrFit[a,b]}}
]


Lsqr[data_, e_]:= Module[{d,x,y,err},

d = Dimensions[data];

If[Length[d != 2], Message[Lsqr::fmt]; Abort[]];
If[d[[1]] == 2 && d[[2]] == 2,Message[Lsqr::amb]; Abort[]];
If[d[[1]] < 2 || d[[2]] < 2,Message[Lsqr::mor]; Abort[]];

If[MatrixQ[data]==False, Message[Lsqr::dat]; Abort[]];

If[d[[1]] == 2, x = data[[1]]; y = data[[2]];];
If[d[[2]] == 2, x = data[[All,1]]; y = data[[All,2]];];

 Lsqr[x,y,e]
]


LsqrSimple[data_, e_]:= Lsqr[data,e][[-3;;-1]]


(* ::Subsection:: *)
(*Graphics*)


LsqrAndPlot[data_,errors_,scales_,units_]:=Module[{l,pd,d2,e2},

d2=scales*#&/@data;
e2=scales*#&/@errors;

l=Lsqr[data, errors[[All,2]]];
pd=Table[{d2[[i]],ErrorBar@@e2[[i]]},{i,1,Length[data]}];

Print[TableForm[N[l]]];

l=Lsqr[d2,e2[[All,2]]];

Show[
ErrorListPlot[pd,PlotRange->All],
Plot[l[[-1]][x],{x,Min[d2[[All,1]]],Max[d2[[All,1]]]},PlotRange->All],

RotateLabel->True,Frame->{{True,False},{True,False}},FrameLabel->units,
FrameStyle->Large,ImageSize->{1145,640},Axes->None,

AxesLabel->Append[units,Large],
LabelStyle->Large,
ImageSize->{1145,640}
]
]


(* ::Subsection:: *)
(*Package Definition*)


End[];

Options[RoundUp]={DigitPrecision->100};
Options[PSolve]={ShowPropagation->True};

SetAttributes[Propagate,{Locked,Protected}];
SetAttributes[CJoin,{Locked,Protected}];
SetAttributes[CAppend,{Locked,Protected}];
SetAttributes[ErrorPair,{Locked,Protected}];
SetAttributes[ErrorRound,{Locked,Protected}];
SetAttributes[ErrorForm,{Locked,Protected}];
SetAttributes[ErrorFormat,{Locked,Protected}];
SetAttributes[ErrorSolve,{Locked,Protected}];
SetAttributes[Nrt,{Locked,Listable,NumericFunction,Protected}];
SetAttributes[RoundUp,{Locked,Listable,Protected}];
SetAttributes[Lsqr,{Locked,Protected}];
SetAttributes[LsqrSimple,{Locked,Protected}];
SetAttributes[LsqrFit,{Locked,Protected}];
SetAttributes[DigitPrecision,{Locked,Protected,ReadProtected}];
SetAttributes[ShowPropagation,{Locked,Protected,ReadProtected}];

EndPackage[];
