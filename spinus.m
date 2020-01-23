(* ::Package:: *)

Import[StringJoin[NotebookDirectory[],"angular.m"]]


JState[j_]:={j,-1};


AddJ[jState_,addJ_]:=Module[
{jj=jState,summedJ={}},
If[jj[[2]]==-1,
jj[[2]]=addJ;
For[jn=Abs[jj[[1]]-addJ],jn<=jj[[1]]+addJ,jn++,
AppendTo[summedJ,{jn,-1}];
];
AppendTo[jj,summedJ]
,
summedJ=Map[AddJ[#,addJ]&,jj[[3]]];
jj[[3]]=summedJ;
];
Return[jj];
];


AddJs[addJs_]:=Module[
{jj={}},
jj=JState[addJs[[1]]];
For[i=2,i<=Dimensions[addJs][[1]],i++,
jj=AddJ[jj,addJs[[i]]];
];
Return[jj];
];


JJConf[jState_]:=Module[
{jj=jState,summedJ={},jjc={}},
If[jj[[2]]==-1,
jjc={{jj[[1]]}};
,
confs=Map[
Map[
Prepend[#,jj[[1]]]&,
JJConf[#]]&,
jj[[3]]];
For[i=1,i<=Dimensions[jj[[3]]][[1]],i++,
jjc=Join[jjc,confs[[i]]];
];
];
Return[jjc];
];





JJBasis[jjConf_]:=Module[
{basis={}},
basis=Map[
Table[Join[#,{m}],{m,#[[-1]],-#[[-1]],-1}]&,
jjConf];
Return[Flatten[basis,1]];
]


TensorOp[initJs_,addJs_,M_,koef_]:={initJs,addJs,M,koef};


rme[J_,K_]:=K! ((2J+K+1)!/((2^K) (2K)!(2J-K)! ))^(1/2);


PolarizationOp[i_,n_,K_,Q_,J_]:=SingleITO[i,n,K,Q,Sqrt[2K+1]/rme[J,K]];


DMOpJJ[i_,n_,basis_,initJ_]:=Module[
{pset,pmatrs,dm,J},
J=initJ[[i]];
pset=Table[{k,q,PolarizationOp[i,n,k,q,J]},{k,0,2 J},{q,-k,k}];(*PolarizOpSet[i,n,J];*)
pmatrs=Table[{opQ[[1]],opQ[[2]],TensorMatrix[opQ[[3]],basis,initJ]},{opK,pset},{opQ,opK}];

dm=Table[Sum[(-1)^(J-pmQ[[1]]+j2) Sqrt[2pmQ[[1]]+1]ThreeJSymbol[{J,j1},{pmQ[[1]],pmQ[[2]]},{J,-j2}] pmQ[[3]],{pmK,pmatrs},{pmQ,pmK}],{ j1,-J,J},{j2,-J,J}];

Return[dm];
];


ReducedME[initStateJs_,initTensJs_]:=Module[
{res=1},
For[j=1,j<=Dimensions[initStateJs][[1]],j++,
Switch[initTensJs[[j]],
0, res*=Sqrt[2initStateJs[[j]]+1],
1,res*=Sqrt[initStateJs[[j]](initStateJs[[j]]+1)(2 initStateJs[[j]]+1)],
2,res*=\[Sqrt]((2initStateJs[[j]]+3)(2initStateJs[[j]]+1)(initStateJs[[j]]+1)initStateJs[[j]] (2initStateJs[[j]]-1)/6),
_,res*=(-1)^initStateJs[[j]] (2initStateJs[[j]]+1) Sqrt[2 initTensJs[[j]] +1] ThreeJSymbol[{initStateJs[[j]],0},{initTensJs[[j]],0},{initStateJs[[j]],0}]
];
];
Return[res];
]





Avg[op_,wf_]:=Conjugate[wf].op.wf;


ss[s_]:=2s+1;


TensorMatrix[Tens_,Basis_,initJ_]:=Module[
{size=Dimensions[Basis][[1]],rme,confSize,Tk,Tq},

If[Dimensions[initJ][[1]]!= Dimensions[Tens[[1]]][[1]],
Print["Error: Tensor and init spin configuration have different sizes"];
Print[initJ];
Print[Tens[[1]]];
Return[0];
,
None
];

rme=ReducedME[initJ,Tens[[1]]];
confSize=Dimensions[initJ][[1]];
Tk=Tens[[2,-1]];
Tq=Tens[[3]];

ham=Tens[[4]]*Quiet[Table[
left=Basis[[i]];
right=Basis[[j]];
Sl=left[[-2]];
Sr=right[[-2]];
ml=left[[-1]];
mr=right[[-1]];
If[
Abs[Sr-Tk]<=Sl&&Sl<=Sr+Tk&&mr+Tq==ml,

(-1)^(2 Tk)/Sqrt[2Sl+1] ClebschGordan[{Sr,mr},{Tk,Tq},{Sl,ml}]*
rme*\!\(
\*UnderoverscriptBox[\(\[Product]\), \(k = 1\), \(confSize - 1\)]\(\[Sqrt]\((ss[Tens[\([2, k + 1]\)]] ss[left[\([k + 1]\)]] ss[right[\([k + 1]\)]])\)*\[IndentingNewLine]NineJSymbol[{Tens[\([2, k]\)], Tens[\([1, k + 1]\)], Tens[\([2, k + 1]\)]}, \[IndentingNewLine]{left[\([k]\)], initJ[\([k + 1]\)], left[\([k + 1]\)]}, \[IndentingNewLine]{right[\([k]\)], initJ[\([k + 1]\)], right[\([k + 1]\)]}]\)\),
0
]
,{i,1,size},{j,1,size}]];


Return[ham];
]



PairITO[i_,j_,n_,k1_,k2_,k_,q_,koef_]:=Module[
{initJ={},addJ={},ib=0,je=0},
ib=Min[i,j];
je=Max[i,j];

initJ=Table[
If[p==ib,k1,
If[p==je,k2,0]],
{p,1,n}];

addJ=Table[
If[p<ib,0,
If[p>=ib&&p<je,k1,
k]
]
,{p,1,n}];
Return[TensorOp[initJ,addJ,q,koef]];
];


SingleITO[i_,n_,k_,q_,koef_]:=Module[
{initJ={},addJ={}},

initJ=Table[
If[p==i,k,0],
{p,1,n}];

addJ=Table[
If[p<i,0,k]
,{p,1,n}];

Return[TensorOp[initJ,addJ,q,koef]];
]





SpinOp[i_,n_,axis_]:=Module[
{ops={}},
Switch[axis,
"z",ops={SingleITO[i,n,1,0,1]},
"x",ops={SingleITO[i,n,1,-1,1/Sqrt[2]],SingleITO[i,n,1,1,-(1/Sqrt[2])]},
"y",ops={SingleITO[i,n,1,-1,I/Sqrt[2]],SingleITO[i,n,1,1,I/Sqrt[2]]}];
Return[ops];
]


SpinOpsMatr[i_,n_,basis_,initJ_]:=Module[
{ops={}},
ops={
CalcMatrix[{SingleITO[i,n,1,-1,1./Sqrt[2.]],SingleITO[i,n,1,1,-(1./Sqrt[2.])]},basis,initJ],
CalcMatrix[{SingleITO[i,n,1,-1,I/Sqrt[2.]],SingleITO[i,n,1,1,I/Sqrt[2.]]},basis,initJ],
CalcMatrix[{SingleITO[i,n,1,0,1]},basis,initJ]
};
Return[ops];
]



HeisOp[i_,j_,n_,Jex_]:=Module[
{},
Return[{PairITO[i,j,n,1,1,0,0,Jex 2Sqrt[3]]}];
]


IonAnisOp[i_,n_,{D_,E_}]:=Module[
{ops={}},
If[D!=0||!NumberQ[D],
ops=Join[ops,{(*SingleITO[i,n,0,0,D (-1)/Sqrt[3]],*)SingleITO[i,n,2,0,D Sqrt[2/3]]}];
];
If[E!=0||!NumberQ[E],
ops=Join[ops,{SingleITO[i,n,2,2,E],SingleITO[i,n,2,-2,E]}];
];
Return[ops];
]


ZeemanOp[i_,n_,{Bx_,By_,Bz_}]:=Module[
{B0=Bz,B1=-1/Sqrt[2] (Bx+I By),Bm1=1/Sqrt[2] (Bx-I By),ops={}},
If[B0!=0||!NumberQ[B0],ops=Join[ops,{SingleITO[i,n,1,0,B0]}];];
If[B1!=0||!NumberQ[B1],ops=Join[ops,{SingleITO[i,n,1,1,B1]}];];
If[Bm1!=0||!NumberQ[Bm1],ops=Join[ops,{SingleITO[i,n,1,-1,Bm1]}];];
Return[ops];
]


ZeemanOpMatr[i_,n_,{Bx_,By_,Bz_},sops_]:=Module[
{ops={}},
ops = -2*5.8*0.01 * (sops[[1]]*Bx+sops[[2]]*By+sops[[3]]*Bz);
Return[ops];
]


SummHam[hams_]:=Module[
{joined={},i=0},
For[i=1,i<=Dimensions[hams][[1]],i++,
joined=Join[joined,hams[[i]]];
];
Return[joined];
]


CalcMatrix[hams_,basis_,initJ_]:=ParallelSum[
SparseArray[TensorMatrix[hams[[q]],basis,initJ]],
{q,1,Dimensions[hams][[1]]}];


CalcMatrixX[hams_,basis_,initJ_]:=CalcMatrix[SummHam[hams],basis,initJ]


SystemConfig[
initJ_,
HamITO_
]:=Module[
{n,
basis,
bsize,
Config,
HamMatrix,
Sops
},

Print["Construct basis..."];

n=Dimensions[initJ][[1]];
basis=JJBasis[JJConf[AddJs[initJ]]];
bsize=Dimensions[basis][[1]];

Print["Calculate Hamiltonian matrix..."];

HamMatrix=CalcMatrix[SummHam[HamITO],basis,initJ];

Print["Calculate spin operator matrices..."];

Sops=Table[
{
CalcMatrix[SpinOp[i,n,"x"],basis,initJ],
CalcMatrix[SpinOp[i,n,"y"],basis,initJ],
CalcMatrix[SpinOp[i,n,"z"],basis,initJ]
}
,{i,1,n}];

Config={
initJ,
n,
bsize,
basis,
HamMatrix,
Sops
};

Print["Done!"];

Return[Config];
]


SpinDynamic[
SysConfig_,
ParNames_,
ParValList_,
TimeUnits_,
DampConst_,
TimeStep_,
NumSteps_,
initNumState_:1
]:=Module[
{
NormTime=1,
PlanckPS=0.6582,
PlanckNorm=0.6582,
t,
\[Lambda],
initJ=SysConfig[[1]],
n=SysConfig[[2]],
bsize=SysConfig[[3]],
basis=SysConfig[[4]],
HamMatrix=SysConfig[[5]],
Sops=SysConfig[[6]]
},


If[TimeUnits=="FS",NormTime=1000];
PlanckNorm=PlanckPS*NormTime;




Conditions=MapThread[#1->#2&,{ParNames,ParValList[[1;;,1]]}];

Print["Solving eigensystem for initial state..."];

ES=Eigensystem[(HamMatrix/.Conditions)//N];
est=Transpose[ES];
ests=Map[
{#[[1]],Normalize[#[[2]] ]}
&,Sort[est,#1[[1]]<#2[[1]]&]];
(*Start wave func*)
S=ests[[initNumState,2]];
Sstart=S;

Print["Dynamic started..."];


(*Time step*)
dt=TimeStep*NormTime;

(*Damping constant*)
\[Lambda]=DampConst;


En={};
T={};
Sz={};
Sx={};
Sy={};
Bar={};

t=0;
Psi={};


Table[
t+=dt;
Conditions=MapThread[#1->#2&,{ParNames,ParValList[[1;;,i]]}];
Hnum=HamMatrix/.Conditions;

Sn=S+(dt/(I (1+\[Lambda]^2)PlanckNorm) (Hnum-I \[Lambda] (Hnum - IdentityMatrix[bsize] Conjugate[S].Hnum.S)).S);


AppendTo[Sx,Table[Conjugate[Sn].Sops[[i,1]].Sn//N,{i,1,n}]];
AppendTo[Sy,Table[Conjugate[Sn].Sops[[i,2]].Sn//N,{i,1,n}]];
AppendTo[Sz,Table[Conjugate[Sn].Sops[[i,3]].Sn//N,{i,1,n}]];

AppendTo[En,Conjugate[Sn].Hnum.Sn];
AppendTo[T,t];
AppendTo[Bar,ParValList[[1;;,i]]];

S=Sn;

S=S/Norm[S];

AppendTo[Psi,S];
,{i,1,NumSteps}];


Sall={Sx,Sy,Sz};

Send=S;
Stot=Transpose[Sqrt[Re[Sx]^2+Re[Sy]^2+Re[Sz]^2]];


Result={
T,
Bar,
Sall,
En,
ParNames,
TimeUnits,
n,
Psi
};



Print["Done!"];

Return[Result];

]


Commute[T1_,T2_]:=T1.T2-T2.T1;


SpinDynamicDM[
SysConfig_,
ParNames_,
ParValList_,
TimeUnits_,
DampConst_,
TimeStep_,
NumSteps_,
Temp_:0,
numStates_:2
]:=Module[
{
NormTime=1,
PlanckPS=0.6582,
PlanckNorm=0.6582,
t,
\[Lambda],
initJ=SysConfig[[1]],
n=SysConfig[[2]],
bsize=SysConfig[[3]],
basis=SysConfig[[4]],
HamMatrix=SysConfig[[5]],
Sops=SysConfig[[6]]
},

(*If[Temp==0,
Return[
SpinDynamic[
SysConfig,
ParNames,
ParValList,
TimeUnits,
DampConst,
TimeStep,
NumSteps,
1]
],
None]
*)
If[TimeUnits=="FS",NormTime=1000];
PlanckNorm=PlanckPS*NormTime;




Conditions=MapThread[#1->#2&,{ParNames,ParValList[[1;;,1]]}];

Print["Solving eigensystem for initial state..."];

ES=Eigensystem[HamMatrix/.Conditions];
est=Transpose[ES];
ests=Map[
{#[[1]],Normalize[#[[2]] ]}
&,Sort[est,#1[[1]]<#2[[1]]&]];

Print["init density matrix"];

(*Start density matrix*)
relEn=Table[en-ests[[1,1]],{en,ests[[1;;numStates,1]]}];
occup=Table[Exp[-en/Temp]//Re,{en, relEn}]//N;
Zsum=Sum[occ,{occ,occup}];

dm=1/Zsum * Sum[occup[[i]] KroneckerProduct[Conjugate[ests[[i,2]]],ests[[i,2]]],{i,1,Dimensions[occup][[1]]}];


Print[occup];
Print[dm];

Print["Dynamic started..."];


(*Time step*)
dt=TimeStep*NormTime;

(*Damping constant*)
\[Lambda]=DampConst;


En={};
T={};
Sz={};
Sx={};
Sy={};
Bar={};

t=0;
Psi={};


Table[
t+=dt;
Conditions=MapThread[#1->#2&,{ParNames,ParValList[[1;;,i]]}];
Hnum=HamMatrix/.Conditions;

comm=Commute[dm,Hnum];

dmn=dm+dt/( (1+\[Lambda]^2)PlanckNorm) (I comm-\[Lambda] Commute[dm,comm]);


AppendTo[Sx,Table[Tr[dmn.Sops[[i,1]]]//Re,{i,1,n}]];
AppendTo[Sy,Table[Tr[dmn.Sops[[i,2]]]//Re,{i,1,n}]];
AppendTo[Sz,Table[Tr[dmn.Sops[[i,3]]]//Re,{i,1,n}]];

AppendTo[En,Tr[dmn.Hnum]];
AppendTo[T,t];
AppendTo[Bar,ParValList[[1;;,i]]];

dm=dmn;

dm=dm/Tr[dm];
(*S=S/Norm[S];*)

AppendTo[Psi,dm];
,{i,1,NumSteps}];


Sall={Sx,Sy,Sz};

Send=S;
Stot=Transpose[Sqrt[Re[Sx]^2+Re[Sy]^2+Re[Sz]^2]];


Result={
T,
Bar,
Sall,
En,
ParNames,
TimeUnits,
n,
Psi
};



Print["Done!"];

Return[Result];

]


GetDynamicEq[
SysConfig_,
DampConst_
]:=Module[
{
NormTime=1,
PlanckPS=0.6582,
PlanckNorm=0.6582,
TimeArr,
\[Lambda],
eq,
sys,
En,
Sall,
WF,
Nsteps,
Parameters,

initJ=SysConfig[[1]],
n=SysConfig[[2]],
bsize=SysConfig[[3]],
basis=SysConfig[[4]],
HamMatrix=SysConfig[[5]],
Sops=SysConfig[[6]]
},

Clear[t];
Clear[SWFC];
Clear[Conditions];

(*Damping constant*)
\[Lambda]=DampConst;

SpinWF[t_]:=Table[Subscript[SWFC, i][t],{i,1,bsize}];

eq=D[SpinWF[t],t]==1/(I (1+\[Lambda]^2)) (HamMatrix-I \[Lambda] (HamMatrix - IdentityMatrix[bsize] Conjugate[SpinWF[t]].HamMatrix.SpinWF[t])).SpinWF[t];

Result={
eq,
SpinWF[#]&
};


Return[Result];
]


SpinDynamicEx[
SysConfig_,
ParNames_,
ParValList_,
TimeUnits_,
DampConst_,
MaxTime_,
initNumState_:1
]:=Module[
{
NormTime=1,
PlanckPS=0.6582,
PlanckNorm=0.6582,
TimeArr,
\[Lambda],
eq,
sys,
En,
Sall,
WF,
Nsteps,
Parameters,

initJ=SysConfig[[1]],
n=SysConfig[[2]],
bsize=SysConfig[[3]],
basis=SysConfig[[4]],
HamMatrix=SysConfig[[5]],
Sops=SysConfig[[6]]
},
Clear[t];
Clear[SWFC];
Clear[Conditions];
If[TimeUnits=="FS",NormTime=1000];
PlanckNorm=PlanckPS*NormTime;


Print["Prepare..."];

SpinWF[t_]:=Table[Subscript[SWFC, i][t],{i,1,bsize}];

Nsteps=Dimensions[ParValList[[1]]][[1]];
dt=MaxTime/(Nsteps-1);
TimeArr=Table[it,{it,0,MaxTime,dt}];
Print["1"];
Parameters=Map[Interpolation[Transpose[{TimeArr,#}]]&,ParValList];
Print["2"];
Conditions[t_]:=MapThread[#1->#2[t]&,{ParNames,Parameters}];
Print["3"];
Print[Conditions[t]];

Hnumf[t_]:=HamMatrix/.Conditions[t];


Print["Solving eigensystem for initial state..."];

ES=Eigensystem[Hnumf[0]];
est=Transpose[ES];
ests=Map[
{#[[1]],Normalize[#[[2]] ]}
&,Sort[est,#1[[1]]<#2[[1]]&]];
(*Start wave func*)
S=ests[[initNumState,2]];
Sstart=S;

Print[ests[[1;;2]]];


Print["Dynamic started..."];
(*Damping constant*)
\[Lambda]=DampConst;

eq=D[SpinWF[t],t]==1/(I (1+\[Lambda]^2)) (HamMatrix-I \[Lambda] (HamMatrix - IdentityMatrix[bsize] Conjugate[SpinWF[t]].HamMatrix.SpinWF[t])).SpinWF[t];

sys=eq/.Conditions[t];(*SpinWF'[t]==1/(I (1+\[Lambda]^2)PlanckNorm)(Hnumf[t]-I \[Lambda] (Hnumf[t] - IdentityMatrix[bsize] Conjugate[SpinWF[t]].Hnumf[t].SpinWF[t])).SpinWF[t];*)


slv=NDSolve[
{sys,SpinWF[0]==Sstart},
SpinWF[t],
{t,0,MaxTime},
MaxSteps->10^6,
Method->{"EquationSimplification"->"Solve"}
];


WF=Table[(SpinWF[t]/.slv)[[1]],{t,0,MaxTime,dt}];

En=MapThread[Conjugate[#1].Hnumf[#2].#1&,{WF,TimeArr}];

Sx=Map[Table[Conjugate[#].Sops[[i,1]].#//N,{i,1,n}]&,WF];
Sy=Map[Table[Conjugate[#].Sops[[i,2]].#//N,{i,1,n}]&,WF];
Sz=Map[Table[Conjugate[#].Sops[[i,3]].#//N,{i,1,n}]&,WF];
Sall={Sx,Sy,Sz};


Stot=Transpose[Sqrt[Re[Sx]^2+Re[Sy]^2+Re[Sz]^2]];


Result={
TimeArr,
Transpose[ParValList],
Sall,
En,
ParNames,
TimeUnits,
n,
eq,
SpinWF[#]&,
WF
};

Print["Done!"];

Return[Result];

]


ParametricArray[t_?NumericQ,arr_]:=(arr[[Floor[t]]]);


DrawSDResults[SDResult_]:=
Module[
{T=SDResult[[1]],
Bar=SDResult[[2]],
Sall=SDResult[[3]],
En=SDResult[[4]],
ParNames=SDResult[[5]],
TimeUnits=SDResult[[6]],
n=SDResult[[7]],
Sallt,
ranges,
maxDif,
newRanges,
Ns
},

Sallt=Table[
Transpose[Re[Sall[[1;;,1;;,i]]]]
,{i,1,n}];

Clear[t];
draw3D=Map[ParametricArray[t,#]&,Sallt];

ranges=Map[{Min[#],Max[#]}&,Re[Sall]];

maxDif=Max[ranges[[1;;,2]]-ranges[[1;;,1]]];


newRanges=Map[{(#[[1]]+#[[2]]-maxDif)/2,(#[[1]]+#[[2]]+maxDif)/2}&,ranges];

Ns=Dimensions[T][[1]];
Return[
{
MapThread[
ListLinePlot[
Join[Transpose[{T}],Transpose[{#1}],2],
PlotRange->All,
FrameLabel->{StringJoin["time, ",TimeUnits],ToString[#2]},
Frame->True]
 &,{Transpose[Bar],ParNames} ],

MapThread[
ListLinePlot[
Map[Re[Join[Transpose[{T}],Transpose[{#}],2]]&,Transpose[#1]],
PlotRange->All,
FrameLabel->{StringJoin["time, ",TimeUnits],StringJoin["<",#2,"> average spin"]},
Frame->True]
&,{Sall,{"Sx","Sy","Sz"}}],

{
ListLinePlot[
Sallt[[1;;,1;;,1;;2]],
FrameLabel->{"Sx","Sy"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],
ListLinePlot[
Sallt[[1;;,1;;,2;;3]],
FrameLabel->{"Sy","Sz"},
Frame->True,
PlotRange->{newRanges[[2]],newRanges[[3]]},
AspectRatio->1],
ListLinePlot[
Sallt[[1;;,1;;,{1,3}]],
FrameLabel->{"Sx","Sz"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[3]]},
AspectRatio->1]
},

{ListLinePlot[Re[Join[Transpose[{T}],Transpose[{En}],2]],
PlotRange->All,
FrameLabel->{StringJoin["time, ",TimeUnits],"<Energy> "},
Frame->True],

(*
ListPointPlot3D[
Sallt,
BoxRatios->{1,1,1},PlotRange->{{minRange,maxRange},{minRange,maxRange},{minRange,maxRange}},
AxesLabel->{"Sx","Sy","Sz"}],
*)

ParametricPlot3D[draw3D,{t,1,Ns},
PlotPoints->1000,
BoxRatios->{1,1,1},PlotRange->{newRanges[[1]],newRanges[[2]],newRanges[[3]]},
AxesLabel->{"Sx","Sy","Sz"}]
}
}
]

]





DrawSDComponents[SDResult_]:=
Module[
{T=SDResult[[1]],
Sall=SDResult[[3]],
TimeUnits=SDResult[[6]],
n=SDResult[[7]],
Sallt,
ranges,
maxDif,
newRanges,
Ns
},

ranges=Map[{Min[#],Max[#]}&,Re[Sall]];
Return[



MapThread[

Table[

ListLinePlot[
Re[Transpose[{T,pl}]],
PlotRange->{#3[[1]]*1.1,#3[[2]]*1.1},
FrameLabel->{StringJoin["time, ",TimeUnits],StringJoin["<",#2,"> average spin"]},
Frame->True]

,{pl,Transpose[#1]}]

&,{Sall,{"Sx","Sy","Sz"},ranges}]
]


]





DrawBaseParametersX[SDResult_]:=
Module[
{T="Time"/.SDResult,
Bar="Parameters"/.SDResult,
ParNames="ParamNames"/.SDResult,
TimeUnits="TimeUnits"/.SDResult,
n="NumSpins"/.SDResult,
En="Energy"/.SDResult
},

Return[
{
MapThread[
ListLinePlot[
Join[Transpose[{T}],Transpose[{#1}],2],
PlotRange->All,
FrameLabel->{StringJoin["time, ",TimeUnits],ToString[#2]},
Frame->True]
 &,{Transpose[Bar],ParNames} ],

{
ListLinePlot[Re[Join[Transpose[{T}],Transpose[{En}],2]],
PlotRange->All,
FrameLabel->{StringJoin["time, ",TimeUnits],"<Energy> "},
Frame->True]
}
}
];

]



GetSpinComponentsX[SDResult_]:=
Module[
{T="Time"/.SDResult,
Psi="WaveFunction"/.SDResult,
TimeUnits="TimeUnits"/.SDResult,
n="NumSpins"/.SDResult,
Sops="SpinOps"/.SDResult,
Sall,
ranges,
maxDif,
newRanges,
Ns},

Sall=Table[
Parallelize[
Table[
Conjugate[Psi[[k]]].Sops[[j,i]].Psi[[k]]
,{k,1,Dimensions[Psi][[1]]}]
]
,{i,1,3},{j,1,n}]//Re;

Return[
{
"Time"->T,
"SpinComponents"->Sall,
"TimeUnits"->TimeUnits,
"NumSpins"->n
}
];

]


CalcObservablesX[SDResult_,operators_]:=
Module[
{T="Time"/.SDResult,
Psi="WaveFunction"/.SDResult,
TimeUnits="TimeUnits"/.SDResult,
n="NumSpins"/.SDResult,
avgs
},

avgs=Table[
Parallelize[
Table[
Conjugate[Psi[[i]]].op.Psi[[i]]
,{i,1,Dimensions[Psi][[1]]}]
]
,{op,operators}]//Re;

Return
[
{
"Time"->T,
"Observables"->avgs,
"TimeUnits"->TimeUnits,
"NumSpins"->n
}
];

]


DrawSpinComponentsX[spincomp_]:=
Module[
{T="Time"/.spincomp,
Sall="SpinComponents"/.spincomp,
TimeUnits="TimeUnits"/.spincomp,
n="NumSpins"/.spincomp,
ranges,
maxDif,
newRanges,
Ns,
Sallt,
t
},

Sallt=MapThread[
Transpose[{#1,#2,#3}]
&,Sall];

Clear[t];
draw3D=Map[ParametricArray[t,#]&,Sallt];

ranges=Map[{Min[#],Max[#]}&,Re[Sall]];

maxDif=Max[ranges[[1;;,2]]-ranges[[1;;,1]]];


newRanges=Map[{(#[[1]]+#[[2]]-maxDif)/2,(#[[1]]+#[[2]]+maxDif)/2}&,ranges];

Return[

Join[
{
MapThread[
ListLinePlot[
Map[Re[Transpose[{T,#}]]&,#1],
PlotRange->All,
FrameLabel->{StringJoin["time, ",TimeUnits],StringJoin["<",#2,"> average spin"]},
Frame->True]
&,{Sall,{"Sx","Sy","Sz"}}]
},

{{
ListLinePlot[
Sallt[[1;;,1;;,1;;2]],
FrameLabel->{"Sx","Sy"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Sallt[[1;;,1;;,2;;3]],
FrameLabel->{"Sy","Sz"},
Frame->True,
PlotRange->{newRanges[[2]],newRanges[[3]]},
AspectRatio->1],

ListLinePlot[
Sallt[[1;;,1;;,{1,3}]],
FrameLabel->{"Sx","Sz"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[3]]},
AspectRatio->1]
}},

MapThread[
Table[
ListLinePlot[
Re[Transpose[{T,pl}]],
PlotRange->{#3[[1]]*1.1,#3[[2]]*1.1},
FrameLabel->{StringJoin["time, ",TimeUnits],StringJoin["<",#2,"> average spin"]},
Frame->True]
,{pl,#1}]
&,{Sall,{"Sx","Sy","Sz"},ranges}]

]

]

]



DrawObservablesX[spincomp_]:=
Module[
{T="Time"/.spincomp,
Observables="Observables"/.spincomp,
TimeUnits="TimeUnits"/.spincomp,
n="NumSpins"/.spincomp,
ranges,
maxDif,
newRanges,
Ns,
Sallt,
t
},

Return[
{
{
ListLinePlot[
Table[ Transpose[{T,aob}],{aob,Observables}],
PlotRange->All,
FrameLabel->{StringJoin["time, ",TimeUnits],"Observables"},
Frame->True
]
},

Table[

ListLinePlot[
Transpose[{T,pl}],
PlotRange->All,
FrameLabel->{StringJoin["time, ",TimeUnits],"Observables"},
Frame->True]
,{pl,Observables}]

}
]

]


DrawSDResultsEx[SDResult_]:=
Module[
{T=SDResult[[1]],
Bar=SDResult[[2]],
Sall=SDResult[[3]],
En=SDResult[[4]],
ParNames=SDResult[[5]],
TimeUnits=SDResult[[6]],
n=SDResult[[7]],
Sallt,
ranges,
maxDif,
newRanges,
Ns
},

Sallt=Table[
Transpose[Re[Sall[[1;;,1;;,i]]]]
,{i,1,n}];

Sabs=Table[Map[Norm[#]&,Sallt[[i]]],{i,1,n}];
Stot=Sum[Sallt[[i]],{i,1,n}];
SabsTot=Map[Norm[#]&,Stot];

Clear[t];
draw3D=Map[ParametricArray[t,#]&,Sallt];

ranges=Map[{Min[#],Max[#]}&,Re[Sall]];

maxDif=Max[ranges[[1;;,2]]-ranges[[1;;,1]]];


newRanges=Map[{(#[[1]]+#[[2]]-maxDif)/2,(#[[1]]+#[[2]]+maxDif)/2}&,ranges];

Ns=Dimensions[T][[1]];
ip={{60,5},{60,5}};
Return[
{
(*Parameters*)
MapThread[
ListLinePlot[
Join[Transpose[{T}],Transpose[{#1}],2],
PlotRange->All,
ImageSize->300,
ImagePadding->ip,
FrameLabel->{StringJoin["time, ",TimeUnits],ToString[#2]},
Frame->True,BaseStyle->{FontSize->15,FontFamily->"Calibri"}]
 &,{Transpose[Bar],ParNames} ],

(*Av Spin components for all spins*)
MapThread[
ListLinePlot[
Map[Re[Join[Transpose[{T}],Transpose[{#}],2]]&,Transpose[#1]],
PlotRange->All,
ImageSize->300,
ImagePadding->ip,
FrameLabel->{StringJoin["time, ",TimeUnits],StringJoin["<",#2,"> average spin"]},
Frame->True,BaseStyle->{FontSize->15,FontFamily->"Calibri"}]
&,{Sall,{"Sx","Sy","Sz"}}],

(*abs value of all spins*)
MapThread[
ListLinePlot[
Re[Join[Transpose[{T}],Transpose[{#1}],2]],
PlotRange->All,
ImageSize->300,
ImagePadding->ip,
FrameLabel->{StringJoin["time, ",TimeUnits],StringJoin["<",#2,"> Abs val of average spin"]},
Frame->True,BaseStyle->{FontSize->15,FontFamily->"Calibri"}]
&,{Sabs,Table[StringJoin["S",ToString[i]],{i,1,n}]}],

{
ListLinePlot[
Re[Join[Transpose[{T}],Transpose[{SabsTot}],2]],
PlotRange->All,
ImageSize->300,
ImagePadding->ip,
FrameLabel->{StringJoin["time, ",TimeUnits]," Total abs val of average spin"},
Frame->True,BaseStyle->{FontSize->15,FontFamily->"Calibri"}]
},


{
ListLinePlot[
Sallt[[1;;,1;;,1;;2]],
FrameLabel->{"Sx","Sy"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1,BaseStyle->{FontSize->15,FontFamily->"Calibri"}],
ListLinePlot[
Sallt[[1;;,1;;,2;;3]],
FrameLabel->{"Sy","Sz"},
Frame->True,
PlotRange->{newRanges[[2]],newRanges[[3]]},
AspectRatio->1,BaseStyle->{FontSize->15,FontFamily->"Calibri"}],
ListLinePlot[
Sallt[[1;;,1;;,{1,3}]],
FrameLabel->{"Sx","Sz"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[3]]},
AspectRatio->1,BaseStyle->{FontSize->15,FontFamily->"Calibri"}]
},

{
ListLinePlot[
Stot[[1;;,1;;2]],
FrameLabel->{"Sx","Sy"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1,BaseStyle->{FontSize->15,FontFamily->"Calibri"}],
ListLinePlot[
Stot[[1;;,2;;3]],
FrameLabel->{"Sy","Sz"},
Frame->True,
PlotRange->{newRanges[[2]],newRanges[[3]]},
AspectRatio->1,BaseStyle->{FontSize->15,FontFamily->"Calibri"}],
ListLinePlot[
Stot[[1;;,{1,3}]],
FrameLabel->{"Sx","Sz"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[3]]},
AspectRatio->1,BaseStyle->{FontSize->15,FontFamily->"Calibri"}]
},

{ListLinePlot[Re[Join[Transpose[{T}],Transpose[{En}],2]],
PlotRange->All,
ImageSize->300,
ImagePadding->ip,
FrameLabel->{StringJoin["time, ",TimeUnits],"<Energy> "},
Frame->True,BaseStyle->{FontSize->15,FontFamily->"Calibri"}],

(*
ListPointPlot3D[
Sallt,
BoxRatios->{1,1,1},PlotRange->{{minRange,maxRange},{minRange,maxRange},{minRange,maxRange}},
AxesLabel->{"Sx","Sy","Sz"}],
*)

ParametricPlot3D[draw3D,{t,1,Ns},
PlotPoints->1000,
BoxRatios->{1,1,1},PlotRange->{newRanges[[1]],newRanges[[2]],newRanges[[3]]},
AxesLabel->{"Sx","Sy","Sz"},BaseStyle->{FontSize->15,FontFamily->"Calibri"}]
}
}
]

]


MovieSpins[SDResult_]:=
Module[
{T=SDResult[[1]],
Bar=SDResult[[2]],
Sall=SDResult[[3]],
En=SDResult[[4]],
ParNames=SDResult[[5]],
TimeUnits=SDResult[[6]],
n=SDResult[[7]],
Sallt,
ranges,
maxDif,
newRanges,
Ns
},

Sallt=Table[
Transpose[Re[Sall[[1;;,1;;,i]]]]
,{i,1,n}];

Sabs=Table[Map[Norm[#]&,Sallt[[i]]],{i,1,n}];
Stot=Sum[Sallt[[i]],{i,1,n}];
SabsTot=Map[Norm[#]&,Stot];

Clear[t];
draw3D=Map[ParametricArray[t,#]&,Sallt];

ranges=Map[{Min[#],Max[#]}&,Re[Sall]];

maxDif=Max[ranges[[1;;,2]]-ranges[[1;;,1]]];


newRanges=Map[{(#[[1]]+#[[2]]-maxDif)/2,(#[[1]]+#[[2]]+maxDif)/2}&,ranges];

Ns=Dimensions[T][[1]];
pNum=100;
Manipulate[

{
{
Show[
ListPlot[
Sallt[[1;;,tp;;tp,1;;2]],
PlotMarkers->{Automatic,15},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Sallt[[1;;,If[tp>pNum,tp-pNum,1];;tp,1;;2]],
FrameLabel->{"Sx","Sy"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1]
]
,

Show[
ListPlot[
Sallt[[1;;,tp;;tp,2;;3]],
PlotMarkers->{Automatic,15},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Sallt[[1;;,If[tp>pNum,tp-pNum,1];;tp,2;;3]],
FrameLabel->{"Sy","Sz"},
Frame->True,
PlotRange->{newRanges[[2]],newRanges[[3]]},
AspectRatio->1]
],

Show[
ListPlot[
Sallt[[1;;,tp;;tp,{1,3}]],
PlotMarkers->{Automatic,15},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Sallt[[1;;,If[tp>pNum,tp-pNum,1];;tp,{1,3}]],
FrameLabel->{"Sx","Sz"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[3]]},
AspectRatio->1]
]
},
{
Show[
ListPlot[
Stot[[tp;;tp,1;;2]],
PlotMarkers->{Automatic,15},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Stot[[If[tp>pNum,tp-pNum,1];;tp,1;;2]],
FrameLabel->{"Sx","Sy"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1]
]
,

Show[
ListPlot[
Stot[[tp;;tp,2;;3]],
PlotMarkers->{Automatic,15},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Stot[[If[tp>pNum,tp-pNum,1];;tp,2;;3]],
FrameLabel->{"Sy","Sz"},
Frame->True,
PlotRange->{newRanges[[2]],newRanges[[3]]},
AspectRatio->1]
],

Show[
ListPlot[
Stot[[tp;;tp,{1,3}]],
PlotMarkers->{Automatic,15},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Stot[[If[tp>pNum,tp-pNum,1];;tp,{1,3}]],
FrameLabel->{"Sx","Sz"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[3]]},
AspectRatio->1]
]
}
}
,
{tp,2,Ns,1}]


]


MovieTotSpin[SDResult_]:=
Module[
{T=SDResult[[1]],
Bar=SDResult[[2]],
Sall=SDResult[[3]],
En=SDResult[[4]],
ParNames=SDResult[[5]],
TimeUnits=SDResult[[6]],
n=SDResult[[7]],
Sallt,
ranges,
maxDif,
newRanges,
Ns
},

Sallt=Table[
Transpose[Re[Sall[[1;;,1;;,i]]]]
,{i,1,n}];

Sabs=Table[Map[Norm[#]&,Sallt[[i]]],{i,1,n}];
Stot=Sum[Sallt[[i]],{i,1,n}];
SabsTot=Map[Norm[#]&,Stot];

Clear[t];
draw3D=Map[ParametricArray[t,#]&,Sallt];

ranges=Map[{Min[#],Max[#]}&,Re[Sall]];

maxDif=Max[ranges[[1;;,2]]-ranges[[1;;,1]]];


newRanges=Map[{(#[[1]]+#[[2]]-maxDif)/2,(#[[1]]+#[[2]]+maxDif)/2}&,ranges];

Ns=Dimensions[T][[1]];
pNum=100;
Manipulate[

{
Show[
ListPlot[
Stot[[tp;;tp,1;;2]],
PlotMarkers->{Automatic,15},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Stot[[If[tp>pNum,tp-pNum,1];;tp,1;;2]],
FrameLabel->{"Sx","Sy"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1]
]
,

Show[
ListPlot[
Stot[[tp;;tp,2;;3]],
PlotMarkers->{Automatic,15},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Stot[[If[tp>pNum,tp-pNum,1];;tp,2;;3]],
FrameLabel->{"Sy","Sz"},
Frame->True,
PlotRange->{newRanges[[2]],newRanges[[3]]},
AspectRatio->1]
],

Show[
ListPlot[
Stot[[tp;;tp,{1,3}]],
PlotMarkers->{Automatic,15},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[2]]},
AspectRatio->1],

ListLinePlot[
Stot[[If[tp>pNum,tp-pNum,1];;tp,{1,3}]],
FrameLabel->{"Sx","Sz"},
Frame->True,
PlotRange->{newRanges[[1]],newRanges[[3]]},
AspectRatio->1]
]
}
,
{tp,2,Ns,1}]

]


Spectrum[conf_,opts_]:=
Module[
{},

Sops=conf[[6]];
Ham=conf[[5]]/.opts;
es=Eigensystem[Ham];
evl=es[[1]];
evc=es[[2]];

TotSOP=Sum[sop,{sop,Sops}];
TotSqSOp=Sum[comp.comp,{comp,TotSOP}];

est=Transpose[es];

ests=Map[
{#[[1]],Normalize[#[[2]] ]}
&,Sort[est,Re[#1[[1]]]<Re[#2[[1]]]&]];

EnTotSpin=
Map[
 {Conjugate[#[[2]]].TotSqSOp.#[[2]]//Re,#[[1]]}
&,ests];

EnSpins=Table[
Table[
Map[
 {Conjugate[#[[2]]].Sops[[i,j]].#[[2]]//Re,#[[1]]}
&,ests],
{i,1,n}],
{j,1,3}];


Return[
{
ests,
EnTotSpin,
EnSpins
}
];

]





GetStateLS[spin_,conf_]:=
(
states = Table[Table[If[j== conf[[i]],1,0],{j,spin[[i]],-spin[[i]],-1}],{i,1,Dimensions[spin][[1]]}];
mergedstates={1};
For[i=1,i<= Dimensions[states][[1]],i++,
mergedstates=KroneckerProduct[mergedstates,states[[i]]];
];
Return[
Flatten[
mergedstates
]
];
);


SpectrumLS[conf_,numStates_]:=
Module[
{},

Sops=conf[[4]];
Ham=conf[[3]];

es=Eigensystem[
-Ham,
numStates,Method->{"Arnoldi","Criteria"->"RealPart"}];

evl=es[[1]];
evc=es[[2]];

TotSOP=Sum[sop,{sop,Sops}];
TotSqSOp=Sum[comp.comp,{comp,TotSOP}];

est=Transpose[{-evl,evc}];

ests=Map[
{#[[1]],Normalize[#[[2]] ]}
&,Sort[est,Re[#1[[1]]]<Re[#2[[1]]]&]];

EnTotSpin=
Map[
 {Conjugate[#[[2]]].TotSqSOp.#[[2]]//Re,#[[1]]}
&,ests];

EnSpins=Table[
Table[
Map[
 {Conjugate[#[[2]]].Sops[[i,j]].#[[2]]//Re,#[[1]]}
&,ests],
{i,1,n}],
{j,1,3}];


Return[
{
ests,
EnTotSpin,
EnSpins
}
];

]





SpectrumLSX[conf_,numStates_]:=
Module[
{},

Sops=conf[[4]];
Ham=conf[[3]];

es=Eigensystem[
-Ham,
numStates,Method->{"Arnoldi","Criteria"->"RealPart","MaxIterations"->1000000,"Tolerance"->10^-8}];

evl=es[[1]];
evc=Orthogonalize[es[[2]]];

TotSOP=Sum[sop,{sop,Sops}];
TotSqSOp=Sum[comp.comp,{comp,TotSOP}];

est=Transpose[{-evl,evc}];

ests=Map[
{#[[1]],Normalize[#[[2]] ]}
&,Sort[est,Re[#1[[1]]]<Re[#2[[1]]]&]];

EnTotSpin=
Map[
 {Conjugate[#[[2]]].TotSqSOp.#[[2]]//Re,#[[1]]}
&,ests];

EnSpins=Table[
Table[
Map[
 {Conjugate[#[[2]]].Sops[[i,j]].#[[2]]//Re,#[[1]]}
&,ests],
{i,1,n}],
{j,1,3}];


Return[
{
"Eigenvals"->ests[[1;;,1]],
"Eigenvecs"->ests[[1;;,2]],
"TotSpin"->EnTotSpin,
"Spins"->EnSpins
}
];

]





Sop[{S_,comp_}]:=
( 
Return[
SparseArray[
Switch[comp,
1,
1/2Table[
(KroneckerDelta[i,j+1]+KroneckerDelta[i+1,j])Sqrt[(S+1)(i+j-1)-i j],
{i,2 S+1},{j,2 S+1}],
2,
I 1/2Table[
(KroneckerDelta[i,j+1]-KroneckerDelta[i+1,j])Sqrt[(S+1)(i+j-1)-i j],
{i,2 S+1},{j,2 S+1}],
3,
DiagonalMatrix[Table[(S+1-i),{i,2 S+1}]]
]
]

]
);


Ident[S_]:=SparseArray[IdentityMatrix[2 S +1]];





KroneckerProductEx[listm_]:=
Module[
{mat},
mat=SparseArray[listm[[1]]];
If[Dimensions[listm][[1]]>1,
Table[mat=KroneckerProduct[mat,m],{m,listm[[2;;]]}];
];
Return[mat];
]


KroneckerProductU[m1_,m2_,Operation_]:=
Module[
{d1,d2,supermat},

d1=Dimensions[m1];
d2=Dimensions[m2];

supermat=Table[0,{d1[[1]]*d2[[1]]},{d1[[2]]*d2[[2]]}];

Table[
supermat[[ (i-1)* d2[[1]]+k, (j-1)*d2[[2]]+l ]]=Operation[m1[[i,j]],m2[[k,l]]];,
{i,d1[[1]]},{j,d1[[2]]},{k,d2[[1]]},{l,d2[[2]]}];

Return[supermat];
]


KroneckerProductUEx[listm_,Operation_]:=
Module[
{mat},
mat=SparseArray[listm[[1]]];
If[Dimensions[listm][[1]]>1,
Table[mat=KroneckerProductU[mat,m,Operation],{m,listm[[2;;]]}];
];
Return[mat];
]


ReducedSingleDMLS[spin_,num_]:=
Module[
{m1,m2,dim,mat},

dim=2 spin[[num]]+1;
mat=Table[
KroneckerProductEx[
Table[
If[
i==num,
ProjecOp[{spin[[i]],m1,m2}],
IdentityMatrix[2 spin[[i]]+1]
],
{i,1,Dimensions[spin][[1]]}]
]
,{m1,1,dim},{m2,1,dim}];

Return[mat];
]


ReducedMixDMLS[singleDMs_]:=
Module[
{},
Return[
KroneckerProductUEx[singleDMs,Dot]
];
]


CalcDMLS[dm_,wf_]:=
Module[
{},
Return[Table[Conjugate[wf].comp.wf,{rc1,dm},{comp,rc1}]];
]


CalcDMLSTemp[dm_,wfs_,eigvals_,Temp_]:=
Module[
{sz=Dimensions[wfs][[1]],
bolz,
Z,rho},

bolz=Table[Exp[-(en-eigvals[[1]])/Temp],{en,eigvals}];
Z=Sum[p,{p,bolz}];

rho=Sum[bolz[[i]]/Z * CalcDMLS[dm,wfs[[i]]],{i,1,Dimensions[wfs][[1]]}];

Return[rho];
]


VonNeumanEntropy[calcdm_]:=
Module[
{eval,ent},

eval=Eigenvalues[calcdm];

ent=-Sum[
eval[[i]]* Log[2,eval[[i]]+0.000000000001]
,{i,Dimensions[eval][[1]]}];

Return[ent];
]


ProjecOp[{S_,i_,j_}]:=
Module[
{mat},
mat=SparseArray[Table[0,{2 S+1},{2S+1}]];
mat[[i,j]]=1;
Return[mat];
]


ProdOp[slist_,oplist_,symbol_]:=Module[
{
opm={1},
ops={}
},
(*Fill array of operators qnumbers*)
ops=Table[{0,0},{Dimensions[slist][[1]]}];
Map[
ops[[#[[1]]]]={slist[[#[[1]] ]],#[[2]]};
&,oplist];

(*Build operator*)
For[i=1,i<=Dimensions[ops][[1]],i++,
If[ops[[i,1]]!=0,
opm=KroneckerProduct[opm,If[symbol==True, Sop[ops[[i]]], Sop[ops[[i]]]//N ]];
,
opm=KroneckerProduct[opm,Ident [slist[[i]]]];
]
];
Return[opm];
];


SpinOpLS[slist_,sn_]:=Table[ProdOp[slist,{{sn,i}},False],{i,3}];


SpinOpLSSym[slist_,sn_]:=Table[ProdOp[slist,{{sn,i}},True],{i,3}];


HeisLS[slist_,{s1_,s2_},Jc_]:=
( 
-2 Jc (ProdOp[slist,{{s1,3},{s2,3}},False]+ProdOp[slist,{{s1,2},{s2,2}},False]+ProdOp[slist,{{s1,1},{s2,1}},False])
)


HeisLSSym[slist_,{s1_,s2_},Jc_]:=
( 
-2 Jc (ProdOp[slist,{{s1,3},{s2,3}},True]+ProdOp[slist,{{s1,2},{s2,2}},True]+ProdOp[slist,{{s1,1},{s2,1}},True])
)


ZeemanLS[slist_,sn_,{Bx_,By_,Bz_}]:=
Module[
{sop},
sop=SpinOpLS[slist,sn];
Return[
-2*5.8*0.01*(sop[[1]]*Bx+sop[[2]]*By+sop[[3]]*Bz)
];
]


AnisLS[slist_,sn_,{Dc_,Ec_}]:=
( 
sop=SpinOpLS[slist,sn];
Return[Dc (sop[[3]].sop[[3]]) + Ec (sop[[1]].sop[[1]] - sop[[2]].sop[[2]])];
)





MatrixCross[s1_,s2_]:={s1[[2]].s2[[3]]-s1[[3]].s2[[2]], 
s1[[3]].s2[[1]]-s1[[1]].s2[[3]],
s1[[1]].s2[[2]]-s1[[2]].s2[[1]]};


DzMorLS[slist_,{s1_,s2_},D_]:=
(
s1q=SpinOpLS[slist,s1];
s2q=SpinOpLS[slist,s2];
svq=MatrixCross[s1q,s2q];
Return[Sum[D[[i]]*svq[[i]],{i,1,3}]];
)


GetHam[ham_,par_]:=
ham[[1]]+Sum[par[[i-1]]*ham[[i]],{i,2,Dimensions[ham][[1]]}]


RHS[eigv_,ham_,a_,b_]:=
(
en=Conjugate[eigv].ham.eigv//Re;
Return[a ham.eigv+en b eigv];
)


RungeKuttaStep[eigv_,ham_,step_,a_,b_]:=Module[{k1,k2,k3,k4},
k1=RHS[eigv,ham,a,b]; 
k2=RHS[eigv+k1 *step/2.0,ham,a,b];
k3=RHS[eigv+k2 *step/2.0,ham,a,b];
k4=RHS[eigv+k3 *step,ham,a,b];
Return[1./6.(k1+2.0 * k2+2.0 * k3 + k4)];
]


RungeKuttaStepT[eigv_,HAM_,t_,step_,a_,b_]:=Module[{k1,k2,k3,k4},
k1=RHS[eigv,HAM[t],a,b]; 
k2=RHS[eigv+k1 *step*0.5,HAM[t+0.5*step],a,b];
k3=RHS[eigv+k2 *step*0.5,HAM[t+0.5*step],a,b];
k4=RHS[eigv+k3 *step,HAM[t+step],a,b];
Return[1./6.(k1+2.0 * k2+2.0 * k3 + k4)];
]


RungeKuttaStepImplEu[eigv_,ham_,step_,a_,b_,ord_]:=Module[{tmp,i,res,rhs},

rhs=RHS[eigv,ham,a,b];
res = eigv + step*rhs;

For[i=1,i<=ord,i++,
res = eigv +0.5 * step * (rhs + RHS[res,ham,a,b]);
];

Return[res];
]


progressBar[dyn_,total_]:=Print@Row[
{ProgressIndicator[dyn,{0,total}]," ", Dynamic@NumberForm[ dyn , {\[Infinity], 2}]
    , "% "}]



SpinDynamicLS[
SysConfig_,
ParNames_,
ParValList_,
TimeUnits_,
DampConst_,
TimeStep_,
MaxTime_,
outEveryPS_,
initNumState_:1
]:=Module[
{
NumSteps=MaxTime/TimeStep,
NormTime=1,
PlanckPS=0.6582,
PlanckNorm=0.6582,
t,
\[Lambda],
initJ=SysConfig[[1]],
n=SysConfig[[2]],
ham=SysConfig[[3]],
Sops=SysConfig[[4]],
bsize = Dimensions[SysConfig[[3,1]]][[1]],
en=0,
done=0
},

progressBar[Dynamic[done],100]
SetSystemOptions["CatchMachineUnderflow" -> False];

If[TimeUnits=="FS",NormTime=1000];
PlanckNorm=PlanckPS*NormTime;



Print["Solving eigensystem for initial state..."];

ES=Eigensystem[
GetHam[-ham,ParValList[[1;;,1]]],
initNumState,Method->{"Arnoldi","Criteria"->"RealPart"}];


(*Start wave func*)
S=ES[[2,initNumState]];
Sstart=S;

Print[S];


(*Time step*)
dt=TimeStep*NormTime;

(*Damping constant*)
\[Lambda]=DampConst;


En={};
T={};
Sz={};
Sx={};
Sy={};
Bar={};

t=0;
Psi={};

done=0;
doneEvery=IntegerPart[NumSteps/100];
doneCount=0;

saveCount=0;
saveEvery=IntegerPart[outEveryPS/dt];
If[saveEvery<1,saveEvery=1];

Print["Dynamic started..."];



For[i=1,i<=NumSteps,i++,

t+=dt;

Hnum=GetHam[ham,N[ParValList[[1;;,i]]]];



Sn=S+dt * RungeKuttaStep[
S,
Hnum,
dt,
N[(-I-\[Lambda])/(PlanckNorm(1.+\[Lambda]^2))],N[(\[Lambda])/(PlanckNorm(1.+\[Lambda]^2))]
]; 


S=Sn;

S=S;(*/Norm[S]*)

If[saveCount==saveEvery,
saveCount=0;
en=Re[Conjugate[S].Hnum.S];

AppendTo[Sx,Table[Conjugate[Sn].Sops[[j,1]].Sn//N,{j,1,n}]];
AppendTo[Sy,Table[Conjugate[Sn].Sops[[j,2]].Sn//N,{j,1,n}]];
AppendTo[Sz,Table[Conjugate[Sn].Sops[[j,3]].Sn//N,{j,1,n}]];

AppendTo[En,en];
AppendTo[T,t];
AppendTo[Bar,ParValList[[1;;,i]]];
]
saveCount++;

If[doneCount== doneEvery,
 (*Print[done," % done "];*)
done++;
donereal=done/100.;
doneCount=0;
]
doneCount++;

];


Sall={Sx,Sy,Sz};

Send=S;
Stot=Transpose[Sqrt[Re[Sx]^2+Re[Sy]^2+Re[Sz]^2]];


Result={
T,
Bar,
Sall,
En,
ParNames,
TimeUnits,
n,
Psi
};



Print["Done!"];

Return[Result];

]


SpinDynamicLSX[
SysConfig_,
ParNames_,
ParValList_,
TimeUnits_,
DampConst_,
TimeStep_,
MaxTime_,
outEveryPS_,
initNumState_:1,
tol_:0.01
]:=Module[
{
NumSteps=MaxTime/TimeStep,
NormTime=1,
PlanckPS=0.6582,
PlanckNorm=0.6582,
t,
\[Lambda],
initJ=SysConfig[[1]],
n=Dimensions[SysConfig[[1]]][[1]],
ham=SysConfig[[2]],
Sops=SysConfig[[3]],
bsize = Dimensions[SysConfig[[2,1]]][[1]],
en=0,
done=0,
adtol=0,
TimeArr,
Parameters
},
adtol=tol/bsize//N;

progressBar[Dynamic[done],100]
SetSystemOptions["CatchMachineUnderflow" -> False];

If[TimeUnits=="FS",NormTime=1000];
PlanckNorm=PlanckPS*NormTime;

(*Prepare*)
Clear[lt];
pdt=MaxTime/(Dimensions[ParValList][[2]]-1);
TimeArr=Table[pdt*(it-1),{it,1,Dimensions[ParValList][[2]]}];
Parameters=Map[Interpolation[Transpose[{TimeArr,#}]]&,ParValList];
ParamsF[lt_]:=Map[#[lt]&,Parameters];
HAM[lt_]:=GetHam[ham,ParamsF[lt]];

Print["Solving eigensystem for initial state..."];

ES=Eigensystem[
GetHam[-ham,ParValList[[1;;,1]]],
initNumState,Method->{"Arnoldi","Criteria"->"RealPart","MaxIterations"->1000000,"Tolerance"->10^-8}];


(*Start wave func*)
Sstart=ES[[2,initNumState]];



(*Time step*)
dt=TimeStep*NormTime;

(*Damping constant*)
\[Lambda]=DampConst;

Reset[]:=
(
S=Sstart;

En={};
T={};
Sz={};
Sx={};
Sy={};
Bar={};
AddObservables={};
Psi={};

t=0;

dtpp=MaxTime/100.;

done=0;
doneEvery=IntegerPart[NumSteps/100];
doneCount=0;

saveCount=0;
saveEvery=IntegerPart[outEveryPS/dt];
If[saveEvery<1,saveEvery=1];
);


Reset[];
Print["Dynamic started..."];

(*////////////////////////////////////////////////////////////////////////*)
calcPassed=False;

i=1;
While[t<MaxTime-dt,

(*en=Conjugate[S].Hnum.S//Re; *)

While[calcPassed==False,

Sn=S+dt * RungeKuttaStepT[
S,
HAM,
t,
dt,
N[(-I-\[Lambda])/(PlanckNorm(1.+\[Lambda]^2))],
N[(\[Lambda])/(PlanckNorm(1.+\[Lambda]^2))]
]; 


norm=Norm[Sn];

If[Abs[norm-1.] < 0.0001,
calcPassed=True;
,
dt*=0.9;
Print["WARNING! Norm of wave function is not 1: ",norm,"! Decreasing step to: ",dt,"; Time: ",t];
calcPassed=False;
];
];

If[Abs[norm-1.]>0.00001,
S=Sn/norm;
,
S=Sn;
];

calcPassed=False;
(*
S = RungeKuttaStepImplEu[
S,
Hnum,
dt,
N[(-I-\[Lambda])/(PlanckNorm(1.+\[Lambda]^2))],N[(\[Lambda])/(PlanckNorm(1.+\[Lambda]^2))],
5
];

*)

t+=dt;

(*If[t<10,S=S/Norm[S]];*)

If[saveCount>=outEveryPS,
saveCount=0;

en=Re[Conjugate[S].HAM[t].S];

AppendTo[En,en];
AppendTo[T,t];
AppendTo[Bar,ParamsF[t]];

AppendTo[Psi,SparseArray[clean[S,adtol]]];
];

saveCount+=dt;

If[doneCount >= dtpp,
 (*Print[done," % done "];*)
done = t/MaxTime * 100;
doneCount=doneCount-dtpp;
];
doneCount+=dt;


i++;
];

(*
Sall={Transpose[Sx],Transpose[Sy],Transpose[Sz]};
Stot=Transpose[Sqrt[Re[Sx]^2+Re[Sy]^2+Re[Sz]^2]];
*)
Send=S;



Result={
"Time"-> T,
"Parameters"-> Bar,
(*"SpinComponents"-> Sall,
"AddObservables"->Transpose[AddObservables],*)
"Energy"-> En,
"ParamNames"-> ParNames,
"TimeUnits"-> TimeUnits,
"NumSpins"-> n,
"WaveFunction" -> Psi,
"SpinOps"->Sops
};



Print["Done!"];

Return[Result];

]


SpinDynamicLSX2[
SysConfig_,
ParNames_,
ParValList_,
TimeUnits_,
DampConst_,
TimeStep_,
MaxTime_,
outEveryPS_,
initNumState_:1,
tol:0.1
]:=Module[
{
NumSteps=20,
DT,
NormTime=1,
PlanckPS=0.6582,
PlanckNorm=0.6582,
t,
\[Lambda],
initJ=SysConfig[[1]],
n=Dimensions[SysConfig[[1]]][[1]],
ham=SysConfig[[2]],
Sops=SysConfig[[3]],
bsize = Dimensions[SysConfig[[2,1]]][[1]],
en=0,
done=0,
adtol=0,
eq,
TimeArr,
Parameters
},
adtol=tol/bsize//N;
DT=MaxTime/NumSteps;

progressBar[Dynamic[done],100]
SetSystemOptions["CatchMachineUnderflow" -> False];

If[TimeUnits=="FS",NormTime=1000];
PlanckNorm=PlanckPS*NormTime;



Print["Solving eigensystem for initial state..."];

ES=Eigensystem[
GetHam[-ham,ParValList[[1;;,1]]],
initNumState,Method->{"Arnoldi","Criteria"->"RealPart"}];

(*Start wave func*)
S=ES[[2,initNumState]];
Sstart=S;


(*Time step*)
dt=TimeStep*NormTime;

(*Damping constant*)
\[Lambda]=DampConst;
TimeArr=Table[dt*(it-1),{it,1,Dimensions[ParValList][[2]]}];

Clear[lt];
Parameters=Map[Interpolation[Transpose[{TimeArr,#}]]&,ParValList];
ParamsF[lt_]:=Map[#[lt]&,Parameters];

Clear[SWFC];
SpinWF[lt_]:=Table[Subscript[SWFC, i][lt],{i,1,bsize}];
Energy[lt_]:=Conjugate[SpinWF[lt]].Hnum.SpinWF[lt];
HnumF[lt_]:=GetHam[ham,ParamsF[lt]];
eq=D[SpinWF[lt],lt]==RHS[SpinWF[lt],HnumF[lt],N[(-I-\[Lambda])/(PlanckNorm(1.+\[Lambda]^2))],N[\[Lambda]/(PlanckNorm(1.+\[Lambda]^2))]];


Print[dt];
Print[DT];
Print[Dimensions[TimeArr]];

En={};
T={};
Sz={};
Sx={};
Sy={};
Bar={};
AddObservables={};
Psi={};

t=0;

dtpp=NumSteps/100.;
done=0;
donereal=0;

saveDT=0;
rest=0;
saveNum=0;
lastSaveT=0;
curSaveT=0;
Ssave={};



Print["Dynamic started..."];

(*////////////////////////////////////////////////////////////////////////*)
For[i=1,i<=NumSteps-1,i++,


(*Hnum=GetHam[ham,N[ParValList[[1;;,i]]]];*)

slv=NDSolve[
{eq, SpinWF[t]==S},
SpinWF[lt],
{lt,t,t+DT},
Method -> {"EquationSimplification"->"Solve"}
];

t+=DT;

S=(SpinWF[lt]/.slv)[[1]]/.{lt->t};

donereal+=DT;
If[donereal>=dtpp,
done+=donereal/dtpp;
donereal=0;
]

(*S=S/Norm[S];*)
(*
saveDT+=DT;
If[saveDT>=outEveryPS,
saveT=rest+saveDT;
saveNum=Quotient[saveT,outEveryPS];
rest=Mod[saveT,outEveryPS];

For[i=1;i<=saveNum,i++,
Ssave=(SpinWF[lt]/.slv)[[1]]/.{lt->curSaveT};
en= Conjugate[Ssave].Hnum.Ssave;
AppendTo[En,en];
AppendTo[T,t];
AppendTo[Bar,ParValList[[1;;,i]]];
AppendTo[Psi,SparseArray[clean[Ssave,adtol]]];
curSaveT+=outEveryPS;
];

saveDT=0;
]
*)
];

(*
Sall={Transpose[Sx],Transpose[Sy],Transpose[Sz]};
Stot=Transpose[Sqrt[Re[Sx]^2+Re[Sy]^2+Re[Sz]^2]];
*)
Send=S;



Result={
"Time"-> T,
"Parameters"-> Bar,
(*"SpinComponents"-> Sall,
"AddObservables"->Transpose[AddObservables],*)
"Energy"-> En,
"ParamNames"-> ParNames,
"TimeUnits"-> TimeUnits,
"NumSpins"-> n,
"WaveFunction" -> Psi,
"SpinOps"->Sops
};



Print["Done!"];

Return[Result];

]


clean[ar_,tol_]:=Map[If[Abs[#]<tol,0,#]&,ar]


RHSDM[dm_,Hnum_,a_,b_]:=
Module[
{comm},
comm=Commute[dm,Hnum];
Return[a(I comm-b Commute[dm,comm])];
];


RungeKuttaStepDM[dm_,Hnum_,a_,b_,step_]:=
Module[{k1,k2,k3,k4},
k1=RHSDM[dm,Hnum,a,b];
k2=RHSDM[dm+k1 *step/2.,Hnum,a,b];
k3=RHSDM[dm+k2 *step/2.,Hnum,a,b];
k4=RHSDM[dm+k3 *step,Hnum,a,b];
Return[1./6.(k1+2.0 k2+2.0 k3 + k4)];
]


SpinDynamicLSDM[
SysConfig_,
ParNames_,
ParValList_,
TimeUnits_,
DampConst_,
TimeStep_,
MaxTime_,
outEveryPS_,
Temp_:0,
numStates_:2,
tol_:0.05,
outtol_:0.1
]:=Module[
{
NumSteps=MaxTime/TimeStep,
NormTime=1,
PlanckPS=0.6582,
PlanckNorm=0.6582,
t,
\[Lambda],
initJ=SysConfig[[1]],
n=SysConfig[[2]],
ham=SysConfig[[3]],
Sops=SysConfig[[4]],
bsize = Dimensions[SysConfig[[3,1]]][[1]],
en=0,
adtol=0,
outadtol,
done
},

adtol=tol/Sqrt[bsize];
outadtol=outtol/Sqrt[bsize];
(*If[Temp==0,
Return[
SpinDynamic[
SysConfig,
ParNames,
ParValList,
TimeUnits,
DampConst,
TimeStep,
NumSteps,
1]
],
None]
*)
If[TimeUnits=="FS",NormTime=1000];
PlanckNorm=PlanckPS*NormTime;


progressBar[Dynamic[done],100]
SetSystemOptions["CatchMachineUnderflow" -> False];

Print["Solving eigensystem for initial state..."];

ES=Eigensystem[
GetHam[-ham,ParValList[[1;;,1]]],
numStates,Method->{"Arnoldi","Criteria"->"RealPart"}];

ests = -ES[[1]];
evec=ES[[2]];


Print["init density matrix"];

(*Start density matrix*)
relEn=Table[en-ests[[1]],{en,ests[[1;;numStates]]}];
occup=Table[Exp[-en/Temp]//Re,{en, relEn}]//N;
Zsum=Sum[occ,{occ,occup}];

dm=1/Zsum * Sum[
occup[[i]] KroneckerProduct[
Conjugate[SparseArray[clean[evec[[i]],adtol]]],
SparseArray[clean[evec[[i]],adtol]]
]
,{i,1,numStates}];

trace=Tr[dm];
dm=dm/trace;

Print["Occupation numbers: ",occup];




(*Time step*)
dt=TimeStep*NormTime;

(*Damping constant*)
\[Lambda]=DampConst;


En={};
T={};
Sz={};
Sx={};
Sy={};
Bar={};

t=0;
Psi={};

done=0;
doneEvery=IntegerPart[NumSteps/100]+1;
doneCount=0;

saveCount=0;
saveEvery=IntegerPart[outEveryPS/dt];
If[saveEvery<1,saveEvery=1];

Print["Dynamic started..."];

Table[

t+=dt;

Hnum=GetHam[ham,ParValList[[1;;,i]]];


dmn=dm+dt * RungeKuttaStepDM[dm,Hnum,1./((1.+\[Lambda]^2)PlanckNorm),\[Lambda],TimeStep];(*/( (1.+\[Lambda]^2)PlanckNorm) (I comm-\[Lambda] Commute[dm,comm]);*)

dm=dmn;


If[saveCount==saveEvery,
saveCount=0;

AppendTo[En,en];
AppendTo[T,t];
AppendTo[Bar,ParValList[[1;;,i]]];

AppendTo[Psi,SparseArray[clean[Sn,adtol]]];
]

saveCount++;

If[doneCount== doneEvery,
 (*Print[done," % done "];*)
done++;
donereal=done/100.;
doneCount=0;
]
doneCount++;


,{i,1,NumSteps}];


Sall={Sx,Sy,Sz};

Send=S;
Stot=Transpose[Sqrt[Re[Sx]^2+Re[Sy]^2+Re[Sz]^2]];


Result={
T,
Bar,
Sall,
En,
ParNames,
TimeUnits,
n,
Psi
};



Print["Done!"];

Return[Result];

]
