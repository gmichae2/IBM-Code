(* ::Package:: *)

<<Documents/mathematica/ibm.m

(*** Interacting boson model with s and d bosons ***)
(** Definition of the acb coefficients in sd-IBM **)
acb[{0,2},obL,1,2,2]=Sqrt[10];
acb[{0,2},obM1,1,2,2]=Sqrt[10]*gb;
acb[{0,2},obQ,2,1,2]=1;
acb[{0,2},obQ,2,2,1]=1;
acb[{0,2},obQ,2,2,2]=chi;
acb[{0,2},obE2,2,1,2]=eb;
acb[{0,2},obE2,2,2,1]=eb;
acb[{0,2},obE2,2,2,2]=eb*chi;
acb[{0,2},obO,3,2,2]=1;
acb[{0,2},obH,4,2,2]=1;

(** Casimir operators in sd-IBM **)
(* The coefficient acb[{0,2},obQ,2,2,2] must be \[PlusMinus]Sqrt[7/4] to recover the limits *)
c1u6sd[{0,2},bra_,ket_]:=delta[bra,ket]*(bra[[1,1]]+bra[[2,1]]);
c1u5sd[{0,2},bra_,ket_]:=delta[bra,ket]*bra[[2,1]];
c1u6u5sd[{0,2},bra_,ket_]:=delta[bra,ket]*(bra[[1,1]]+bra[[2,1]])*bra[[2,1]];
c2u6sd[{0,2},bra_,ket_]:=delta[bra,ket]*(bra[[1,1]]+bra[[2,1]])*(bra[[1,1]]+bra[[2,1]]+5);
c2u5sd[{0,2},bra_,ket_]:=delta[bra,ket]*bra[[2,1]]*(bra[[2,1]]+4);
c2su3sd[{0,2},bra_,ket_]:=0/; bra[[1,1]]+bra[[2,1]]!=ket[[1,1]]+ket[[2,1]] || bra[[2,5]]!=ket[[2,5]];
c2su3sd[{0,2},bra_,ket_]:=
redsqrtrat[(2*Sqrt[5]*rmeTb[{0,2},{obQ,obQ},{2,2},{2,0},bra,ket]-
            3*Sqrt[3]/4*rmeTb[{0,2},{obL,obL},{1,1},{1,0},bra,ket])/Sqrt[2*bra[[2,5]]+1]];
c3su3sd[{0,2},bra_,ket_]:=0/; bra[[1,1]]+bra[[2,1]]!=ket[[1,1]]+ket[[2,1]] || bra[[2,5]]!=ket[[2,5]];
c3su3sd[{0,2},bra_,ket_]:=
redsqrtrat[(-4*Sqrt[35]*rmeTb[{0,2},{obQ,obQ,obQ},{2,2,2},{2,2,0},bra,ket]-
            9*Sqrt[15]/2*rmeTb[{0,2},{obL,obQ,obL},{1,2,1},{1,1,0},bra,ket])/Sqrt[2*bra[[2,5]]+1]];
(* Check on the square of c2su3 *)
c22su3sda[{0,2},bra_,ket_]:=0/; bra[[1,1]]+bra[[2,1]]!=ket[[1,1]]+ket[[2,1]] || bra[[2,5]]!=ket[[2,5]];
c22su3sda[{0,2},bra_,ket_]:=
redsqrtrat[(20*rmeTb[{0,2},{obQ,obQ,obQ,obQ},{2,2,2,2},{2,0,2,0},bra,ket]-
            3*Sqrt[15]/2*rmeTb[{0,2},{obQ,obQ,obL,obL},{2,2,1,1},{2,0,1,0},bra,ket]-
            3*Sqrt[15]/2*rmeTb[{0,2},{obL,obL,obQ,obQ},{1,1,2,2},{1,0,2,0},bra,ket]+
            27/16*rmeTb[{0,2},{obL,obL,obL,obL},{1,1,1,1},{1,0,1,0},bra,ket])/Sqrt[2*bra[[2,5]]+1]];
(*Omega[{0,2},bra_,ket_]:=0/; bra[[1,1]]+bra[[2,1]]!=ket[[1,1]]+ket[[2,1]] || bra[[2,5]]!=ket[[2,5]];
Omega[{0,2},bra_,ket_]:=
redsqrtrat[-3*Sqrt[5/2]*rmeLQ[-Sqrt[7]/2,{1,2,1},{1,1,0},bra,ket]/Sqrt[2*bra[[2,5]]+1]];*)
c2so6sd[{0,2},bra_,ket_]:=0/;
bra[[1,1]]+bra[[2,1]]!=ket[[1,1]]+ket[[2,1]] ||
bra[[2,2]]!=ket[[2,2]] || bra[[2,3]]!=ket[[2,3]] || bra[[2,5]]!=ket[[2,5]];
c2so6sd[{0,2},bra_,ket_]:=
Block[{Nb,ndb,ndk,v,L},
Nb=bra[[1,1]]+bra[[2,1]]; ndb=bra[[2,1]]; ndk=ket[[2,1]]; v=bra[[2,2]]; L=bra[[2,4]];
Which[ndb==ndk,Nb*(Nb+4)-(Nb-ndb)*(Nb-ndb-1)-(ndb-v)*(ndb+v+3),
      ndb+2==ndk,Sqrt[(Nb-ndb)*(Nb-ndb-1)*(ndb-v+2)*(ndb+v+5)],
      ndb==ndk+2,Sqrt[(Nb-ndk)*(Nb-ndk-1)*(ndk-v+2)*(ndk+v+5)],
      True,0]];
c2so5sd[{0,2},bra_,ket_]:=delta[bra,ket]*bra[[2,2]]*(bra[[2,2]]+3);
c2so3sd[{0,2},bra_,ket_]:=delta[bra,ket]*bra[[2,5]]*(bra[[2,5]]+1);
(* The order of the scalar operators in the generators must be declared *)
order[o_]:=1/; o==c1u6sd || o==c1u5sd;
order[o_]:=2/; o==c1u6u5sd || o==c2u6sd || o==c2u5sd || o==c2su3sd || o==c2so6sd ||
               o==c2so5sd || o==c2so3sd || o==obPPsd;
order[o_]:=3/; o==c3su3sd || o==obP0nsP0sd || o==obP0ndP0sd || o==obG3G3sd || o==obddd3sd;
order[o_]:=4/; o==c22su3sd || o==c22su3sda ;

(**  Definition of the pairing operator in sd-IBM **)
obPPsd[{0,2},bra_,ket_]:=
(hmeb[{0,2},{{{2,0,1,0,0},{0,0,1,0,0}},{{2,0,1,0,0},{0,0,1,0,0}}},bra,ket]
+5*hmeb[{0,2},{{{0,0,1,0,0},{2,0,1,0,0}},{{0,0,1,0,0},{2,0,1,0,0}}},bra,ket]
-Sqrt[5]*hmeb[{0,2},{{{2,0,1,0,0},{0,0,1,0,0}},{{0,0,1,0,0},{2,0,1,0,0}}},bra,ket]
-Sqrt[5]*hmeb[{0,2},{{{0,0,1,0,0},{2,0,1,0,0}},{{2,0,1,0,0},{0,0,1,0,0}}},bra,ket])/2;

(**  Definition of some normal-ordered three-body operators in sd-IBM.
     See PRC93 (2016) 051302 *)
obP0nsP0sd[{0,2},bra_,ket_]:=
(10*hmeb[{0,2},{{{1,1,1,0,0},{2,0,1,0,0}},{{1,1,1,0,0},{2,0,1,0,0}}},bra,ket]
+24*hmeb[{0,2},{{{3,1,1,0,0},{0,0,1,0,0}},{{3,1,1,0,0},{0,0,1,0,0}}},bra,ket]
-4*Sqrt[15]*hmeb[{0,2},{{{1,1,1,0,0},{2,0,1,0,0}},{{3,1,1,0,0},{0,0,1,0,0}}},bra,ket]
-4*Sqrt[15]*hmeb[{0,2},{{{3,1,1,0,0},{0,0,1,0,0}},{{1,1,1,0,0},{2,0,1,0,0}}},bra,ket]);
obP0ndP0sd[{0,2},bra_,ket_]:=
(14*hmeb[{0,2},{{{0,0,1,0,0},{3,1,1,2,2}},{{0,0,1,0,0},{3,1,1,2,2}}},bra,ket]
+8*hmeb[{0,2},{{{2,0,1,0,0},{1,1,1,2,2}},{{2,0,1,0,0},{1,1,1,2,2}}},bra,ket]
-4*Sqrt[7]*hmeb[{0,2},{{{0,0,1,0,0},{3,1,1,2,2}},{{2,0,1,0,0},{1,1,1,2,2}}},bra,ket]
-4*Sqrt[7]*hmeb[{0,2},{{{2,0,1,0,0},{1,1,1,2,2}},{{0,0,1,0,0},{3,1,1,2,2}}},bra,ket]);
obG3G3sd[{0,2},bra_,ket_]:=
30*hmeb[{0,2},{{{0,0,1,0,0},{3,3,1,3,3}},{{0,0,1,0,0},{3,3,1,3,3}}},bra,ket];
obddd3sd[{0,2},bra_,ket_]:=obG3G3sd[{0,2},bra,ket]/30;

(** Spectrum of a common Hamiltonian in sd-IBM **)
(* hops contains the 11 parameters {es,ed,ls,ld,k0,k1,k2,chi,k3,k4,v3} with
   {{es,obn1},{ed,obn2},
    {ls,obn1n1},{ld,obn2n2},{k0,obPPsd},{k1,obLL},{k2,obQQ},{k3,obOO},{k4,obHH},
    {v3,obddd3sd}};
   chi is declared as a separate argument *)
(* n eigenstates for the angular momenta in Js.
   c=1: prints n eigenvalues relative to the J=0 ground state
   c=2: + eigenvector of yrast states
   c=3: + n eigenvectors
   c=4: outputs n eigenvalues and eigenvectors *)
specsd[Nb_,Js_,n_,hops_,chin_,c_]:=
Block[{ors,ormax,tab,J,ham1,ham2,ham3,sub,ham,eig,egs,dim,nd},
ors=Map[order,hops[[All,2]]]; ormax=Max[ors];
egs=0;
tab=Table[J=Js[[i]];
          ham1=hamb[{0,2},1,Nb,J];
          ham2=hamb[{0,2},2,Nb,J];
          If[ormax==3,ham3=hamb[{0,2},3,Nb,J]];
          sub=multonorb[{0,2},hops];
          ham=sqh[Which[ormax==2,(ham1+ham2),ormax==3,(ham1+ham2+ham3)]/.sub/.chi->chin];
          dim=Length[ham]; nd=Min[n,dim];
          If[dim==0,{},
             eig=Map[Take[#,nd]&,eigensystem[ham]];
             If[J==0,egs=eig[[1,1]]; Print["Ground-state energy: ",egs]];
             If[c==1||c==2||c==3,Print["J=",J," (dim=",dim,") Energies: ",
                                      Round[Take[eig[[1]]-egs,nd],0.001]]];
             If[c==2,Print["Eigenvector yrast state: ",eig[[2,1]]]];
             If[c==3,Do[Print["Eigenvector state ",j,": ",eig[[2,j]]],{j,1,nd}]];
             If[c==4,Print["J=",J," (dim=",dim,") Energies: ",Round[Take[eig[[1]],nd],0.001]]];
             eig],
          {i,1,Length[Js]}];
If[c==4,tab]];

(* Electromagnetic transitions *)
(* Calculates transitions from Ji(1 to ni) to Jf(1 to nf)
   c=1: reduced transition matrix elements
   c=2: B(E or M) values
   c=3: outputs reduced matrix elements *)
emtrsd[Nb_,Ji_,ni_,Jf_,nf_,hops_,chihn_,top_,chitn_,c_]:=
Block[{eigi,eigf,tmat,tem},
eigi=specsd[Nb,{Ji},ni,hops,chihn,4][[1]];
eigf=specsd[Nb,{Jf},nf,hops,chihn,4][[1]];
tmat=topb[{0,2},Nb,Ji,Nb,Jf,top]/.chi->chitn;
tem=Chop[Simplify[eigf[[2]] . tmat . Transpose[eigi[[2]]]]];
Which[
c==1,Do[Print["<",Jf,"(",if,")||",top,"||",Ji,"(",ii,")>=",tem[[if,ii]]],
       {if,1,nf},{ii,1,ni}],
c==2,Do[Print["B[",top,";",Ji,"(",ii,")->",Jf,"(",if,")]=",tem[[if,ii]]^2/(2*Ji+1)],
       {if,1,nf},{ii,1,ni}],
c==3,tem]];

(* Electromagnetic moments *)
(* Calculates the moments of J(1 to n)
   c=1: reduced matrix elements
   c=2: moments
   c=3: outputs reduced matrix elements *)
emmosd[Nb_,J_,n_,hops_,chihn_,top_,chitn_,c_]:=
Block[{eig,tmat,tem},
eig=specsd[Nb,{J},n,hops,chihn,4][[1]];
tmat=topb[{0,2},Nb,J,Nb,J,top]/.chi->chitn;
tem=Chop[Simplify[eig[[2]] . tmat . Transpose[eig[[2]]]]];
Which[
c==1,Do[Print["<",J,"(",i,")||",top,"||",J,"(",i,")>=",tem[[i,i]]],{i,1,n}],
c==2 && top===obM1,Do[Print["\[Mu][",J,"(",i,")]=",Sqrt[4*Pi/3]*wigner[J,1,J,-J,0,J]*tem[[i,i]]],{i,1,n}],
c==2 && top===obE2,Do[Print["Q[",J,"(",i,")]=",Sqrt[16*Pi/5]*wigner[J,2,J,-J,0,J]*tem[[i,i]]],{i,1,n}],
c==3,tem]];

(** A triaxial minimum at (b,g) with a free parameter a0 in sd-IBM **)
(*
triaxsd[bra_,ket_]:=
Block[{beta,gamma,a0},
beta=0.5; gamma=29*Pi/180; a0=0;
(beta^6*hme[{0,2},{{{3,1,1,0,0},{0,0,1,0,0}},{{3,1,1,0,0},{0,0,1,0,0}}},bra,ket]
+a0^2*beta^2*hme[{0,2},{{{1,1,1,0,0},{2,0,1,0,0}},{{1,1,1,0,0},{2,0,1,0,0}}},bra,ket]
+35/2*(1+Sqrt[3/5]*a0)^2/Cos[3*gamma]^2*
hme[{0,2},{{{0,0,1,0,0},{3,3,1,3,3}},{{0,0,1,0,0},{3,3,1,3,3}}},bra,ket]
+a0*beta^4*hme[{0,2},{{{3,1,1,0,0},{0,0,1,0,0}},{{1,1,1,0,0},{2,0,1,0,0}}},bra,ket]
+a0*beta^4*hme[{0,2},{{{1,1,1,0,0},{2,0,1,0,0}},{{3,1,1,0,0},{0,0,1,0,0}}},bra,ket]
+beta^3*Sqrt[35/2]*(1+Sqrt[3/5]*a0)/Cos[3*gamma]*
hme[{0,2},{{{3,1,1,0,0},{0,0,1,0,0}},{{0,0,1,0,0},{3,3,1,3,3}}},bra,ket]
+beta^3*Sqrt[35/2]*(1+Sqrt[3/5]*a0)/Cos[3*gamma]*
hme[{0,2},{{{0,0,1,0,0},{3,3,1,3,3}},{{3,1,1,0,0},{0,0,1,0,0}}},bra,ket]
+a0*beta*Sqrt[35/2]*(1+Sqrt[3/5]*a0)/Cos[3*gamma]*
hme[{0,2},{{{1,1,1,0,0},{2,0,1,0,0}},{{0,0,1,0,0},{3,3,1,3,3}}},bra,ket]
+a0*beta*Sqrt[35/2]*(1+Sqrt[3/5]*a0)/Cos[3*gamma]*
hme[{0,2},{{{0,0,1,0,0},{3,3,1,3,3}},{{1,1,1,0,0},{2,0,1,0,0}}},bra,ket])];
*)

(** Analytic expressions in the limits of sd-IBM **)
(* The spectrum of a1*c1u5+a2*c2u5+b*c2so5+c*c2so3 *)
specu5sd[Nb_,J_]:=
Block[{u6u5,u5,u5so5,so5,so5so3},
u6u5=bruuu2[5,1,{Nb}][[All,1]];
Flatten[Table[u5=u6u5[[i]];
              u5so5=bruo[5,u5];
              Table[so5=u5so5[[j]];
                    so5so3=broo3[5,so5];
                    Table[If[eq0[1,so5so3[[k,2]]]=={2*J},
                             Table[a1*e1u[5,u5]+a2*e2u[5,u5]+b*e2o[5,so5]+c*J*(J+1),
                                   {l,1,so5so3[[k,1]]}],{}],
                          {k,1,Length[so5so3]}],
                    {j,1,Length[u5so5]}],
              {i,1,Length[u6u5]}]]];

(* The spectrum of a2*c2su3+a3*c3su3+a22*c22su3+c*c2so3 *)
specsu3sd[Nb_,J_]:=
Block[{u6u3,u3,u3so3},
u6u3=pletuu[6,3,{Nb},{2}];
Flatten[Table[u3=u6u3[[i,2]];
              u3so3=bruo3[3,u3];
              Table[If[eq0[1,u3so3[[j,2]]]=={2*J},
                    Table[a2*e2su3[eq3[3,u3]]+a3*e3su3[eq3[3,u3]]+
                          (*a22*e2su3[eq3[3,u3]]^2+*)c*J*(J+1),
                    (*Table[-a1*e2su3[eq3[3,u3]]/(2*Nb)+a2*e3su3[eq3[3,u3]]/(9*2*Nb^2)+
                          a3*e2su3[eq3[3,u3]]^2/(2*Nb^3)+t3*J*(J+1),*)
                          {k,1,u6u3[[i,1]]*u3so3[[j,1]]}],{}],
                    {j,1,Length[u3so3]}],
              {i,1,Length[u6u3]}]]];

(* The spectrum of a*c2so6+b*c2so5+c*c2so3 *)
specso6sdg[Nb_,J_]:=
Block[{u6so6,so6,so6so5,so5,so5so3},
u6so6=bruo[6,{Nb}];
Flatten[Table[so6=eq0[1,u6so6[[i]]];
              so6so5=Join[Table[{i},{i,so6[[1]],1,-1}],{{}}];
              Table[so5=so6so5[[j]];
                    so5so3=broo3[5,so5];
                    Table[If[eq0[1,so5so3[[k,2]]]=={2*J},
                             Table[a*e2o[6,so6]+b*e2o[5,so5]+c*J*(J+1),
                                   {l,1,so5so3[[k,1]]}],{}],
                          {k,1,Length[so5so3]}],
                    {j,1,Length[so6so5]}],
              {i,1,Length[u6so6]}]]];
