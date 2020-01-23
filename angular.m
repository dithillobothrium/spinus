(* angular.m                     *)
(* Andrei Derevianko July, 1997  *)
(* www.nd.edu/~andrei            *)
(* andrei@atomic2.phys.nd.edu    *)

(* Angular stuff collection *)

Parity[l_?NumberQ] := Abs[Mod[l,2] - 1]

(* Reduced matrix element of tensor C_k *)
CRed[{ja_, la_},k_,{jb_,lb_}] := 
	(-1)^(ja+1/2) Sqrt[ (2ja+1)(2jb+1)] * 
	ThreeJSymbol[{ja,-1/2},{jb,1/2},{k,0}] * Parity[ la+k+lb] //Simplify

CRedRelativistic[ja_,k_,jb_] := 
	(-1)^(ja+1/2) Sqrt[ (2ja+1)(2jb+1)] * 
	ThreeJSymbol[{ja,-1/2},{jb,1/2},{k,0}] * Parity[ l[ja]+k+l[jb]] //Simplify

	
CRed[la_,k_,lb_] := 
	(-1)^la Sqrt[ (2la+1)(2lb+1)] * 
	ThreeJSymbol[{la,0},{k,0},{lb,0}]



NineJSymbol[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:=
Module[{xLo,xUp},
  xLo = Max[ Abs[a-j],Abs[b-f], Abs[d-h]];
  xUp = Min[ a+j,b+f,d+h];
  
  Sum[ (-1)^(2x) (2x+1) *
       SixJSymbol[{a,b,c},{f,j,x}]*
       SixJSymbol[{d,e,f},{b,x,h}]*
	   SixJSymbol[{g,h,j},{x,a,d}], {x,xLo,xUp}]
]

(* Matrix elements of finite rotations *)
(* By Edmonds' book (1960), p.57 *)
(* Andrei Derevianko, October 1995 *)
(*---- d-functions ------ *)
dFunc[j_,mp_,m_,b_]:= Sqrt[ ((j+mp)! (j-mp)!)/( (j+m)! (j-m)! )]  *
	Sum[ (-1)^(j-mp-s) Binomial[j+m,j-mp-s] Binomial[j-m,s] *
	 Cos[b/2]^(2s+mp+m)* Sin[b/2]^(2j-2s-mp-m)	,
	{s,0,j-m}]
