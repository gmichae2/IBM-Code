(* ::Package:: *)

<<Documents/mathematica/ibm.m

(*** Interacting boson model with s, d and g bosons ***)
(** Definition of acb coefficients in sdg-IBM *)
(* U(15) -> SU(3) -> SO(3) in sdg-IBM *)
acb[{0,2,4},obL,1,2,2]=Sqrt[10];
acb[{0,2,4},obL,1,3,3]=Sqrt[60];
acb[{0,2,4},obQa,2,1,2]=2*Sqrt[14/15];
acb[{0,2,4},obQa,2,2,1]=2*Sqrt[14/15];
acb[{0,2,4},obQa,2,2,2]=11*Sqrt[1/21];
acb[{0,2,4},obQa,2,2,3]=6*Sqrt[6/35];
acb[{0,2,4},obQa,2,3,2]=6*Sqrt[6/35];
acb[{0,2,4},obQa,2,3,3]=Sqrt[66/7];

(* U(15) -> SU(5) -> SO(5) -> SO(3) in sdg-IBM *)
acb[{0,2,4},obL,1,2,2]=Sqrt[10];
acb[{0,2,4},obL,1,3,3]=Sqrt[60];
acb[{0,2,4},obQb,2,1,2]=Sqrt[1/5];
acb[{0,2,4},obQb,2,2,1]=Sqrt[1/5];
acb[{0,2,4},obQb,2,2,2]=-3/14;
acb[{0,2,4},obQb,2,2,3]=6/7*Sqrt[1/5];
acb[{0,2,4},obQb,2,3,2]=6/7*Sqrt[1/5];
acb[{0,2,4},obQb,2,3,3]=3/14*Sqrt[22];
acb[{0,2,4},obO,3,2,2]=4/7;
acb[{0,2,4},obO,3,2,3]=-3/14*Sqrt[10];
acb[{0,2,4},obO,3,3,2]=-3/14*Sqrt[10];
acb[{0,2,4},obO,3,3,3]=-3/14*Sqrt[11];
acb[{0,2,4},obH,4,1,3]=Sqrt[1/5];
acb[{0,2,4},obH,4,3,1]=Sqrt[1/5];
acb[{0,2,4},obH,4,2,2]=2/7;
acb[{0,2,4},obH,4,2,3]=1/14*Sqrt[110];
acb[{0,2,4},obH,4,3,2]=1/14*Sqrt[110];
acb[{0,2,4},obH,4,3,3]=1/14*Sqrt[143/5];

(* a2 Q2.Q2 + a4 H4.H4 in sdg-IBM *)
(*
acb[{0,2,4},1,1,2,2]=Sqrt[10];
acb[{0,2,4},1,1,3,3]=Sqrt[60];
acb[{0,2,4},2,1,1,2]=1;
acb[{0,2,4},2,1,2,1]=1;
acb[{0,2,4},2,1,2,2]=qdd;
acb[{0,2,4},2,1,2,3]=qdg;
acb[{0,2,4},2,1,3,2]=qdg;
acb[{0,2,4},2,1,3,3]=qgg;
acb[{0,2,4},4,1,1,3]=1;
acb[{0,2,4},4,1,3,1]=1;
acb[{0,2,4},4,1,2,2]=hdd;
acb[{0,2,4},4,1,2,3]=hdg;
acb[{0,2,4},4,1,3,2]=hdg;
acb[{0,2,4},4,1,3,3]=hgg;
*)
(** Casimir operators in sdg-IBM *)
(* U(15) -> SU(3) -> SO(3) in sdg-IBM *)
c2su3sdg[{0,2,4},bra_,ket_]:=0/;
bra[[1,1]]+bra[[2,1]]+bra[[3,1]]!=ket[[1,1]]+ket[[2,1]]+ket[[3,1]] || bra[[3,5]]!=ket[[3,5]];
c2su3sdg[{0,2,4},bra_,ket_]:=
redsqrtrat[(3*Sqrt[5]/2*rmeTb[{0,2,4},{obQa,obQa},{2,2},{2,0},bra,ket]-
            3*Sqrt[3]/4*rmeTb[{0,2,4},{obL,obL},{1,1},{1,0},bra,ket])/Sqrt[2*bra[[3,5]]+1]];           
c2so3sdg[{0,2,4},bra_,ket_]:=delta[bra,ket]*bra[[3,5]]*(bra[[3,5]]+1);

(* U(15) -> SU(5) -> SO(5) -> SO(3) in sdg-IBM *)
c2su5sdg[{0,2,4},bra_,ket_]:=0/;
bra[[1,1]]+bra[[2,1]]+bra[[3,1]]!=ket[[1,1]]+ket[[2,1]]+ket[[3,1]] || bra[[3,5]]!=ket[[3,5]];
c2su5sdg[{0,2,4},bra_,ket_]:=
redsqrtrat[(30*rmeTb[{0,2,4},{obH,obH},{4,4},{4,0},bra,ket]-
            10*Sqrt[7]*rmeTb[{0,2,4},{obO,obO},{3,3},{3,0},bra,ket]+
            10*Sqrt[5]*rmeTb[{0,2,4},{obQb,obQb},{2,2},{2,0},bra,ket]-
            Sqrt[3]/4*rmeTb[{0,2,4},{obL,obL},{1,1},{1,0},bra,ket])/Sqrt[2*bra[[3,5]]+1]];
c2so5sdg[{0,2,4},bra_,ket_]:=0/;
bra[[1,1]]+bra[[2,1]]+bra[[3,1]]!=ket[[1,1]]+ket[[2,1]]+ket[[3,1]] || bra[[3,5]]!=ket[[3,5]];
c2so5sdg[{0,2,4},bra_,ket_]:=
redsqrtrat[-(8*Sqrt[7]*rmeTb[{0,2,4},{obO,obO},{3,3},{3,0},bra,ket]+
             Sqrt[3]/5*rmeTb[{0,2,4},{obL,obL},{1,1},{1,0},bra,ket])/Sqrt[2*bra[[3,5]]+1]];
c2so3sdg[{0,2,4},bra_,ket_]:=delta[bra,ket]*bra[[3,5]]*(bra[[3,5]]+1);

(* The order of the scalar operators in the generators must be declared *)
order[o_]:=1/; o==c1u15sdg || o==c1u6sdg || o==c1u5sdg || o==c1u9sdg;
order[o_]:=2/; o==c2u15sdg || o==c2su3sdg || o==c2su5sdg || o==c2so5sdg || o==c2so3sdg;


(** Analytic expressions in some limits of sdg-IBM **)
(* The spectrum of a*c2su3+b*c2so3 *)
specsu3sdg[Nb_,J_]:=
Block[{u15u3,u3,u3so3},
u15u3=pletuu[15,3,{Nb},{4}];
Flatten[Table[u3=u15u3[[i,2]];
              u3so3=bruo3[3,u3];
              Table[If[eq0[1,u3so3[[j,2]]]=={2*J},
                    Table[a*e2su3[eq3[3,u3]]+b*J*(J+1),
                          {k,1,u15u3[[i,1]]*u3so3[[j,1]]}],{}],
                    {j,1,Length[u3so3]}],
              {i,1,Length[u15u3]}]]];

(* The spectrum of a*c2su5+b*c2so5+c*c2so3 *)
specsu5sdg[Nb_,J_]:=
Block[{u15u5,u5,u5so5,so5,so5so3},
u15u5=pletuu[15,5,{Nb},{2}];
Flatten[Table[u5=u15u5[[i,2]];
              u5so5=bruo[5,u5];
              Table[so5=u5so5[[j]];
                    so5so3=broo3[5,so5];
                    Table[If[eq0[1,so5so3[[k,2]]]=={2*J},
                             Table[a*e2su5[eq3[5,u5]]+b*e2o[5,so5]+c*J*(J+1),
                                   {l,1,u15u5[[i,1]]*so5so3[[k,1]]}],{}],
                          {k,1,Length[so5so3]}],
                    {j,1,Length[u5so5]}],
              {i,1,Length[u15u5]}]]];
