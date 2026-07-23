(* ::Package:: *)

(*** Partitions of a positive integer n in p positive integers ***)
(* n is the integer.
   p is the number of partitions.
   omi is an array with p minimum values.
   oma is an array with p maximum values.
 *)
parts[n_,p_]:=Flatten[Table[Map[(Join[#,{i}])&,parts[n-i,p-1]],{i,0,n}],1];
parts[n_,p_]:={Table[0,{i,1,p}]}/; n==0 ;
parts[n_,p_]:={{n}}/; p==1;

(* args contains {parts[n,p],o} *)
selparts[args_,k_]:={Select[args[[1]],(#[[k]]<=args[[2,k]])&],args[[2]]};
parts[n_,p_,oma_]:=Fold[selparts,{parts[n,p],oma},Table[i,{i,1,p}]][[1]];

parts[n_,p_,omi_,oma_]:=Map[(#+omi)&,parts[n-Apply[Plus,omi],p,oma-omi]];

(*** Young tableaux ***)
(* y stands for a Young tableau in the notation {t1,t2,...} *)
(* ti positive & t1 =< t2 =< ...: True if allowed, false if not *)
young0[y_]:=Apply[And,Table[y[[i]]>=0,{i,1,Length[y]}]];
young1[y_]:=True/; Length[y]=1;
young1[y_]:=Apply[And,Table[y[[i]]>=y[[i+1]],{i,1,Length[y]-1}]];
(* It is assumed that t1 =< t2 =< ... *)
(* Zeros can be suppressed *)
(* l stands for a list of young tableaux {y1,y2,...} *)

(** Dimension of the Young tableau y={t1,t2,...} of U(n), SO(n) or Sp(n) **)
(* u refers to U(n);
   o refers to SO(n);
   s refers to Sp(n) with n even;
   os refers to SO(n) when n is odd and Sp(n) when n is even. *)
du[n_,y_]:=
Block[{yl},
      yl=Join[y,Table[0,{i,Length[y]+1,n}]];
      Product[(yl[[i]]-yl[[j]]-i+j)/(-i+j),{i,1,n},{j,i+1,n}]];
do[n_,y_]:=
Block[{yl},
      yl=Join[y,Table[0,{i,Length[y]+1,n/2}]];
      2^(n/2-1)*If[yl[[n/2]]==0,1,2]*
      Product[(yl[[i]]-yl[[j]]-i+j)*(n+yl[[i]]+yl[[j]]-i-j),{i,1,n/2},{j,i+1,n/2}]/
      Product[(n-2*i)!,{i,1,n/2}]]/; EvenQ[n];
do[n_,y_]:=
Block[{yl},
      yl=Join[y,Table[0,{i,Length[y]+1,(n-1)/2}]];
      Product[(yl[[i]]-yl[[j]]-i+j)*(n+yl[[i]]+yl[[j]]-i-j),{i,1,(n-1)/2},{j,i+1,(n-1)/2}]*
      Product[(2*yl[[i]]+n-2*i),{i,1,(n-1)/2}]/
      Product[(n-2*i)!,{i,1,(n-1)/2}]]/; OddQ[n];
ds[n_,y_]:=
Block[{yl},
      yl=Join[y,Table[0,{i,Length[y]+1,n/2}]];
      Product[(yl[[i]]-yl[[j]]-i+j)*(n+yl[[i]]+yl[[j]]-i-j+2)/(-i+j)/(n-i-j+2),{i,1,n/2},{j,i+1,n/2}]*
      Product[(n/2+yl[[i]]-i+1)/(n/2-i+1),{i,1,n/2}]]/; EvenQ[n];
dos[n_,y_]:=Which[OddQ[n],do[n,y],EvenQ[n],ds[n,y]];

(** Energy eigenvalues of Casimir operators **)
e1u[n_,y_]:=wei[y];
e2u[n_,y_]:=Sum[y[[i]]*(y[[i]]+n-2*(i-1/2)),{i,1,Length[y]}];
e2o[n_,y_]:=Sum[y[[i]]*(y[[i]]+n-2*i),{i,1,Length[y]}];
e2s[n_,y_]:=Sum[y[[i]]*(y[[i]]+n-2*(i-1)),{i,1,Length[y]}];
e2os[n_,y_]:=Which[OddQ[n],e2o[n,y],EvenQ[n],e2s[n,y]];
e2su3[lm_]:=lm[[1]]^2+lm[[2]]^2+3*lm[[1]]+3*lm[[2]]+lm[[1]]*lm[[2]];
e3su3[lm_]:=(lm[[1]]-lm[[2]])*(2*lm[[1]]+lm[[2]]+3)*(lm[[1]]+2*lm[[2]]+3);
e2su5[lm_]:=2*lm[[1]]^2+3*lm[[2]]^2+3*lm[[3]]^2+2*lm[[4]]^2+10*lm[[1]]+15*lm[[2]]+15*lm[[3]]+10*lm[[4]]+
4*lm[[2]]*lm[[3]]+3*lm[[1]]*lm[[2]]+3*lm[[3]]*lm[[4]]+2*lm[[1]]*lm[[3]]+2*lm[[2]]*lm[[4]]+lm[[1]]*lm[[4]];


(** Conversion between different representations of Young tableaux **)
(* Remove 0s from y *)
chop[y_]:=Select[y,(#!=0)&];
wei[y_]:=Apply[Plus,y];
(* Conversion from a Young tableau to a single number *)
yton[y_]:=
Block[{yt,rt},
      yt=chop[y];
      rt=Length[yt];
      If[Length[y]==0,y,Sum[yt[[i]]*10^(rt-i),{i,1,rt}]]];
(* Conversion from Frobenius to Young notation *)
(* f stands for a Young tableau in the Frobenius notation {{a1,b1},{a2,b2},...} *)
(* It is assumed that a1 < a2 < ... and b1 < b2 < ... *)
ftoy[f_]:=
Block[{r,as,bs,bbs},
      r=Length[f];
      as=Table[f[[i,1]]+i,{i,1,r}];
      bbs=Join[{f[[r,2]]},Table[f[[i,2]]-f[[i+1,2]]-1,{i,r-1,1,-1}]];
      bs=Flatten[Table[i,{i,r,1,-1},{j,1,bbs[[r-i+1]]}],1];
      Join[as,bs]];
rank[y_]:=Length[Select[y-Table[i,{i,1,Length[y]}],(#>=0)&]];

(** Outer multiplication of Young tableaux (S functions) **)
(* If y1 or y2 is empty *)
omy[y1_,y2_]:={y1}/; chop[y2]=={};
omy[y1_,y2_]:={y2}/; chop[y1]=={};
(* If y1 has one row *)
omy[y1_,y2_]:=omy1[y1,y2]/; Length[chop[y1]]==1;
omy1[y1_,y2_]:=(*omy1[y1,y2]=*)
Block[{ya,o,ym},
      ya=Append[chop[y2],0];
      o=Prepend[Drop[ya-Append[Drop[ya,1],0],-1],y1[[1]]];
      ym=Map[(ya+#)&,parts[y1[[1]],Length[ya],o]];
      Map[chop,ym]];
(* If y2 has one row *)
omy[y1_,y2_]:=omy2[y1,y2]/; Length[chop[y2]]==1;
omy2[y1_,y2_]:=(*omy2[y1,y2]=*)
Block[{ya,o,ym},
      ya=Append[chop[y1],0];
      o=Prepend[Drop[ya-Append[Drop[ya,1],0],-1],y2[[1]]];
      ym=Map[(ya+#)&,parts[y2[[1]],Length[ya],o]];
      Map[chop,ym]];
(* General y1 and y2 *)
omy[y1_,y2_]:=(*omy[y1,y2]=*)
Block[{y1t,y2t,y2a,y2b,m2,m3},
      y1t=chop[y1];
      y2t=chop[y2];
      y2a=Drop[y2t,-1];
      y2b=Take[y2t,-1];
      m2=Flatten[Map[omy[y1t,#]&,Select[omy[y2a,y2b],(#!=y2t)&]],1];
      m3=Flatten[Map[omy[#,y2b]&,omy[y1t,y2a]],1];
      complement[m3,m2]];
(* Multiplicity of Young tableau y in the outer multiplication y1 x y2 *)
gam[y1_,y2_,y_]:=0/; wei[y1]+wei[y2]!=wei[y];
gam[y1_,y2_,y_]:=1/; chop[y2]=={} && y1==y;
gam[y1_,y2_,y_]:=0/; chop[y2]=={} && y1!=y;
gam[y1_,y2_,y_]:=1/; chop[y1]=={} && y2==y;
gam[y1_,y2_,y_]:=0/; chop[y1]=={} && y2!=y;
gam[y1_,y2_,y_]:=gam[y1,y2,y]=Count[omy[y1,y2],y];

(* Outer multiplication of lists of Young tableaux *)
(* yn is a list {y1,y2,...}
   ym is a list {m,{y1,y2,...}} where m is the multiplicity
   yml is a list {m,{{m1,y1},{m2,y2},...}} where m, mi are multiplicities
   yl is a list {{m1,y1},{m2,y2},...} where mi are multiplicities *)
(* tf0 transforms {y1,y2,..} into {{1,y1},{1,y2},...}}
   tf1 transforms {m,{y1,y2,..}} into {{m,y1},{m,y2},...}}
   tf2 transforms {{m1,y},...,{m2,y},...} into {{m1+m2...,y},...}
   tf3 transforms {m{{m1,y1},...,{m2,y2},...}} into {{m*m1,y1},{m*m2,y2},...}
   tf4 transforms {y1,y2,..} into {{m1,y1},{m2,y2},...}}*)
tf0[yn_]:=tf1[{1,yn}];
tf1[ym_]:=Map[({ym[[1]],#})&,ym[[2]]];
tf2[yl_]:=
Block[{lk},
      lk=Union[yl[[All,2]]];
      Table[{wei[Select[yl,(#[[2]]==lk[[i]])&][[All,1]]],lk[[i]]},{i,1,Length[lk]}]];
tf3[yml_]:=Map[({yml[[1]]*#[[1]],#[[2]]})&,yml[[2]]];
tf4[yn_]:=tf2[tf0[yn]];
omyl[yl1_,yl2_]:=
Block[{yl12},
      yl12=Table[{yl1[[i1,1]]*yl2[[i2,1]],omy[yl1[[i1,2]],yl2[[i2,2]]]},
                 {i1,1,Length[yl1]},{i2,1,Length[yl2]}];
      tf2[Flatten[Map[tf1,Flatten[yl12,1]],1]]];

(** List of Young tableaux in l1 and not in l2 **)
(* It is assumed that all Young tableaux of l2 are in l1 *)
complement[l1_,l2_]:=
Block[{l1u,t1,t2,t12},
      l1u=Union[l1];
      t1=Table[Count[l1,l1u[[i]]],{i,1,Length[l1u]}];
      t2=Table[Count[l2,l1u[[i]]],{i,1,Length[l1u]}];
      t12=t1-t2;
      Flatten[Table[l1u[[i]],{i,1,Length[t12]},{j,1,t12[[i]]}],1]];

(** Representations of unitary, orthogonal and symplectic algebras **)
(* u is a representation of a unitary algebra U(n);
   o is a representation of an orthogonal algebra SO(n);
   s is a representation of a symplectic algebra Sp(n) with n even *)

(* Define equivalent U(n) representation with lower weight *)
(* Add zeros *)
eq0[n_,u_]:=Join[u,Table[0,{i,1,n-Length[u]}]];
(* {t1,t2,...,tn} \[Rule] {t1-tn,t2-tn,...,0} *)
eq1[n_,u_]:=
Block[{ua},
      ua=Join[u,Table[0,{i,1,n-Length[u]}]];
      Drop[ua-ua[[-1]],-1]];
(* {t1,t2,...,tn} \[Rule] {t1-tn,t1-tn-1,...,t1-t2,0} *)
eq2[n_,u_]:=
Block[{ua,u1,u2,p1,p2},
      ua=Join[u,Table[0,{i,1,n-Length[u]}]];
      u1=ua-ua[[-1]];
      p1=wei[u1];
      u2=ua[[1]]-Table[ua[[i]],{i,Length[ua],1,-1}];
      p2=wei[u2];
      Select[If[p1<=p2,u1,u2],(#!=0)&]];
(* {t1,t2,...,tn} \[Rule] {t1-t2,t2-t3,...} *)
eq3[n_,u_]:=
Block[{ua},
      ua=Join[u,Table[0,{i,1,n-Length[u]}]];
      Table[ua[[i]]-ua[[i+1]],{i,1,n-1}]];

(* Outer multiplication of (lists of) U(n) representations *)
(* u stands for a Young tableau in U(n) *)
(* ul is a list {{m1,u1},{m2,u2},...} where mi is the multiplicity *)
omu0[n_,u1_,u2_]:=omu0[n,u1,u2]=Select[omy[u1,u2],(Length[#]<=n)&];
omu1[n_,u1_,u2_]:=omu1[n,u1,u2]=
Map[eq1[n,#]&,Select[omy[eq1[n,u1],eq1[n,u2]],(Length[#]<=n)&]];
(*omul[n_,ul1_,ul2_]:=Select[omyl[ul1,ul2],(Length[#[[2]]]<=n)&];*)
omul[n_,ul1_,ul2_]:=
Block[{ul12},
      ul12=Table[{ul1[[i1,1]]*ul2[[i2,1]],omu1[n,ul1[[i1,2]],ul2[[i2,2]]]},
                 {i1,1,Length[ul1]},{i2,1,Length[ul2]}];
      tf2[Flatten[Map[tf1,Flatten[ul12,1]],1]]];

(* Outer multiplication of (lists of) U(na) x U(nb) representations *)
(* uu stands for the double Young tableau {{a1,a2,...},{b1,b2,...}} *)
(* uul is a list {{m1,uu1},{m2,uu2},...} where mi is the multiplicity *)
omu[na_,nb_,uu1_,uu2_]:=
Block[{la,lb},
      la=omu0[na,uu1[[1]],uu2[[1]]];
      lb=omu0[nb,uu1[[2]],uu2[[2]]];
      Flatten[Table[{la[[i]],lb[[j]]},{i,1,Length[la]},{j,1,Length[lb]}],1]];
omul[na_,nb_,yl1_,yl2_]:=
Block[{yl12},
      yl12=Table[{yl1[[i1,1]]*yl2[[i2,1]],omu[na,nb,yl1[[i1,2]],yl2[[i2,2]]]},
                 {i1,1,Length[yl1]},{i2,1,Length[yl2]}];
      tf2[Flatten[Map[tf1,Flatten[yl12,1]],1]]];

(* Outer multiplication of SO(n) representations *)
omo[n_,o1_,o2_]:=
Block[{p,su1,su2,su,pu,pup,pum,psp,psm},
      p=wei[o1]+wei[o2];
      su1=otoy[o1];
      su2=otoy[o2];
      su=Flatten[Table[{su1[[i]],su2[[j]]},{i,1,Length[su1]},{j,1,Length[su2]}],1];
      pu=Flatten[Map[omu0[n,#[[1]],#[[2]]]&,su],1];
      pup=Select[pu,(EvenQ[(p-wei[#])/2])&];
      pum=Select[pu,(OddQ[(p-wei[#])/2])&];
      psp=Flatten[Map[bruo[n,#]&,pup],1];
      psm=Flatten[Map[bruo[n,#]&,pum],1];
      complement[psp,psm]];

(* Orthogonal representations in terms of S functions or Young tableaux; Eq (64)  *)
(* otoy outputs a list of Young tableaux {y1,y2,...}
   phase follows from weight difference between o and yi *)
otoy[o_]:=
Block[{p,r,sg,sy,gy},
      p=wei[o];
      r=Length[chop[o]];
      sg=Select[Join[{{}},sgam[p]],(Length[#]<=r)&];
      sy=Table[syou[r,p-wei[sg[[i]]]],{i,1,Length[sg]}];
      gy=Table[gam[sg[[i]],sy[[i,j]],o],{i,1,Length[sg]},{j,1,Length[sy[[i]]]}];
      Flatten[Table[sy[[i,j]],{i,1,Length[sg]},{j,1,Length[sy[[i]]]},{k,1,gy[[i,j]]}],2]];

(* Outer multiplication of Sp(n) representations (n even) *)
oms[n_,s1_,s2_]:=
Block[{p,su1,su2,su,pu,pup,pum,psp,psm},
      p=wei[s1]+wei[s2];
      su1=stoy[s1];
      su2=stoy[s2];
      su=Flatten[Table[{su1[[i]],su2[[j]]},{i,1,Length[su1]},{j,1,Length[su2]}],1];
      pu=Flatten[Map[omu0[n,#[[1]],#[[2]]]&,su],1];
      pup=Select[pu,(EvenQ[(p-wei[#])/2])&];
      pum=Select[pu,(OddQ[(p-wei[#])/2])&];
      psp=Flatten[Map[brus[n,#]&,pup],1];
      psm=Flatten[Map[brus[n,#]&,pum],1];
      complement[psp,psm]];

(* Symplectic representations in terms of S functions or Young tableaux; Eq (74)  *)
(* stoy outputs a list of Young tableaux {y1,y2,...}
   phase follows from weight difference between s and yi *)
stoy[s_]:=
Block[{p,r,sa,sy,gy},
      p=wei[s];
      r=Length[chop[s]];
      sa=Select[Join[{{}},salp[p]],(Length[#]<=r)&];
      sy=Table[syou[r,p-wei[sa[[i]]]],{i,1,Length[sa]}];
      gy=Table[gam[sa[[i]],sy[[i,j]],s],{i,1,Length[sa]},{j,1,Length[sy[[i]]]}];
      Flatten[Table[sy[[i,j]],{i,1,Length[sa]},{j,1,Length[sy[[i]]]},{k,1,gy[[i,j]]}],2]];

(* Outer multiplication of SO(n) or Sp(n) representations *)
omos[n_,os1_,os2_]:=Which[OddQ[n],omo[n,os1,os2],EvenQ[n],oms[n,os1,os2]];


(*** Branching rules ***)
(** Branching rule from U(n) to SO(n) **)
bruo[n_,u_]:=
Block[{um,pm,rm,sd,wd,sy,my,ty,cy,dy,ey,fy,uy,vy},
      um=eq2[n,u];
      pm=wei[um];
      rm=Length[chop[um]];
      sd=Select[Join[{{}},sdel[pm]],(Length[#]<=rm)&];
      sy=Table[wd=wei[sd[[i]]];
               Select[syou[n,pm-wd],(Length[#]<=rm)&],
               {i,1,Length[sd]}];
      my=Table[gam[sd[[i]],sy[[i,j]],um],{i,1,Length[sd]},{j,1,Length[sy[[i]]]}];
      ty=Flatten[Table[sy[[i,j]],{i,1,Length[sd]},{j,1,Length[sy[[i]]]},{k,1,my[[i,j]]}],2];
      cy=Map[cho[n,#]&,ty];
      ey=cy[[All,1]];
      fy=cy[[All,2]];
      dy=Map[Take[#,Min[Length[#],Floor[n/2]]]&,ey*fy];
      uy=Select[dy,(#=={} || wei[#]>0)&];
      vy=-Select[dy,(wei[#]<0)&];
      complement[uy,vy]];
(* Check whether Young diagram y is allowed in SO(n) (Theorems IA & IB are incorrect) *)
(* 0 means not allowed; +1 or -1 gives phase *)
(*cho[n_,y_]:=
Block[{(*y2,p2,r2*)},
      y2=Select[Drop[Join[y,Table[0,{i,1,n-Length[y]}]],Floor[n/2]],(#!=0)&];
      p2=wei[y2];
      r2=rank[y2];
      Which[p2==0,+1,
            EvenQ[n] && OddQ[p2],0,
            EvenQ[n] && MemberQ[sgam[p2],y2],(-1)^(p2/2),
            EvenQ[n] && FreeQ[sgam[p2],y2],0,
            OddQ[n] && MemberQ[seta[p2],y2],(-1)^((p2-r2)/2),
            OddQ[n] && FreeQ[seta[p2],y2],0]];*)
(* Check whether Young diagram y is allowed in SO(n) (Murnaghan, p 282-285) *)
(* Gives {phase,ym} where ym is modified Young tableau and phase=0 means not allowed *)
(* +1 or -1 gives phase of modified Young tableau *)
(* Valid up to n=6 if y has no more than n-1 rows; elements are proper *)
cho[n_,y_]:=
Block[{k,j},
      k=Floor[n/2];
      j=Length[chop[y]];
      Which[j<=k,{+1,y},
            OddQ[n],Which[j==k+1 && y[[j]]==1,{+1,Drop[y,-1]},
                          j==k+1,{0,y},
                          j==k+2 && y[[j-1]]==2 && y[[j]]==2,{-1,Drop[y,-2]},
                          j==k+2 && y[[j-1]]==2 && y[[j]]==1,{-1,Drop[y,-2]},
                          j==k+2 && y[[j-2]]==1 && y[[j-1]]==1 && y[[j]]==1,{+1,Drop[y,-3]},
                          j==k+2,{0,y}],
            EvenQ[n],Which[j==k+1 && y[[j]]==2,{-1,Drop[y,-1]},
                           j==k+1 && y[[j-1]]==1 && y[[j]]==1,{+1,Drop[y,-2]},
                           j==k+1,{0,y},
                           j==k+2 && y[[j-1]]==3 && y[[j]]==3,{-1,Drop[y,-2]},
                           j==k+2 && y[[j-1]]==3 && y[[j]]==1,{+1,Drop[y,-2]},
                           j==k+2 && y[[j-2]]==2 && y[[j-1]]==2 && y[[j]]==2,{-1,Drop[y,-3]},
                           j==k+2 && y[[j-2]]==2 && y[[j-1]]==2 && y[[j]]==1,{-1,Drop[y,{-3,-2}]},
                           j==k+2 && y[[j-2]]==2 && y[[j-1]]==1 && y[[j]]==1,{-1,Drop[y,-3]},
                           j==k+2 && y[[j-3]]==1 && y[[j-2]]==1 && y[[j-1]]==1 && y[[j]]==1,{+1,Drop[y,-4]},
                           j==k+2,{0,y}]]];

(** Branching rule from U(n) to Sp(n) (n even) **)
brus[n_,u_]:=
Block[{um,pm,rm,sb,wb,sy,my,ty,cy,dy,uy,vy},
      um=eq2[n,u];
      pm=wei[um];
      rm=Length[chop[um]];
      sb=Select[Join[{{}},sbet[pm]],(Length[#]<=rm)&];
      sy=Table[wb=wei[sb[[i]]];
               Select[syou[n,pm-wb],(Length[#]<=rm)&],
               {i,1,Length[sb]}];
      my=Table[gam[sb[[i]],sy[[i,j]],um],{i,1,Length[sb]},{j,1,Length[sy[[i]]]}];
      ty=Flatten[Table[sy[[i,j]],{i,1,Length[sb]},{j,1,Length[sy[[i]]]},{k,1,my[[i,j]]}],2];
      cy=Map[chs[n,#]&,ty];
      dy=Map[Take[#,Min[Length[#],n/2]]&,cy*ty];
      uy=Select[dy,(#=={} || wei[#]>0)&];
      vy=-Select[dy,(wei[#]<0)&];
      complement[uy,vy]];
(* Check whether Young diagram y is allowed in Sp(n) (Theorem IC) *)
(* 0 means not allowed; +1 or -1 gives phase *)
chs[n_,y_]:=
Block[{y2,p2},
      y2=Select[Drop[Join[y,Table[0,{i,1,n-Length[y]}]],n/2],(#!=0)&];
      p2=wei[y2];
      Which[p2==0,+1,
            OddQ[p2],0,
            MemberQ[salp[p2],y2],(-1)^(p2/2),
            FreeQ[salp[p2],y2],0]];

(** Branching rule from U(n) to SO(n) if n is odd and from U(n) to Sp(n) if n is even **)
bruos[n_,u_]:=Which[OddQ[n],bruo[n,u],EvenQ[n],brus[n,u]];

(** Branching rule from U(n) or SO(n) or Sp(n) to SO(3)~GL(2) **)
bruo3[n_,u_]:=plethys[{n-1},u];
broo3[n_,o_]:=
Block[{p,sy,sp,sh,si},
      p=wei[o];
      sy=otoy[o];
      sp=Map[((-1)^((p-wei[#])/2))&,sy];
      sh=Flatten[Table[Map[multip[sp[[i]],#]&,ytoh[sy[[i]]]],{i,1,Length[sy]}],1];
      si=Flatten[Table[Map[multip[sh[[i,1]],#]&,pleth[{n-1},sh[[i,2]]]],{i,1,Length[sh]}],1];
      Select[tf2[Map[({#[[1]],eq2[2,#[[2]]]})&,si]],(#[[1]]!=0)&]];
brso3[n_,s_]:=
Block[{p,sy,sp,sh,si},
      p=wei[s];
      sy=stoy[s];
      sp=Map[((-1)^((p-wei[#])/2))&,sy];
      sh=Flatten[Table[Map[multip[sp[[i]],#]&,ytoh[sy[[i]]]],{i,1,Length[sy]}],1];
      si=Flatten[Table[Map[multip[sh[[i,1]],#]&,pleth[{n-1},sh[[i,2]]]],{i,1,Length[sh]}],1];
      Select[tf2[Map[({#[[1]],eq2[2,#[[2]]]})&,si]],(#[[1]]!=0)&]];

(** Branching rule from SO(n) if n is odd and from Sp(n) if n is even to SO(3)~GL(2) **)
broso3[n_,os_]:=Which[OddQ[n],broo3[n,os],EvenQ[n],brso3[n,os]];

(** Expansion of S functions (denoted as Young diagrams)
    as a sum of products of symmetric functions h1*h2*... 
    where hi is the symmetric function {ri} **)
(* hx is an auxiliary function not to be used anywhere else *)
hx[0]=1;
hx[r_]:=0/; r<0;
(* ytoh outputs a list {{c1,{h11,h12,...}},{c2,{h21,h22,...}},...} *)
ytoh[y_]:={{1,{}}} /; Length[Select[y,(#!=0)&]]==0;
ytoh[y_]:={{1,{y}}} /; Length[Select[y,(#!=0)&]]==1;
ytoh[y_]:=
Block[{r,p,sh,hl,cl,yll},
      r=Length[chop[y]];
      p=wei[y];
	  sh=Det[Table[hx[y[[i]]-i+j],{i,1,r},{j,1,r}]];
      hl=Table[sh[[i]],{i,1,Length[sh]}];
      cl=hl/.hx[x_]->1;
      hl=hl/cl;
      yll=Map[hxtoyl[p,#]&,hl];
      If[r==1,{{1,{y}}},Table[{cl[[i]],yll[[i]]},{i,1,Length[hl]}]]];
(* Converts an expression hx[r]^er*...*hx[1]^e1... into {{er},...,{e1}} *)
hxtoyl[p_,hxp_]:=Flatten[Table[{i},{i,p,1,-1},{k,1,Exponent[hxp,hx[i]]}],1];

(** Plethysm for GL(n) -> GL(2) **)
(* k is a one-rowed representation of SO(3)
   and corresponds to the angular momentum content of the fundamental GL(n) representation;
   y is a representation of GL(n) *)
(* plethys[m,y] outputs a list {{m1,{k1}},{m2,{k2}},...}
   where mi is the multiplicity of the SO(3) representation {ki}
         ki a single number to be identified with twice the angular momentum *)
(* If y has one row; Eq (137) *)
plethys[k_,y_]:=plet[chop[k],chop[y]];
plet[k_,y_]:=nonsens/; Length[k]>1;
plet[k_,y_]:={{1,{}}}/; k=={} || y=={};
plet[k_,y_]:={{1,k}}/; y=={1};
plet[k_,y_]:={{1,y}}/; k=={1};
plet[k_,y_]:=
Block[{p1,p2,p3,p3p,p3m},
      p1=plet[chop[{k[[1]]-2}],y];
      p2=plet[k,chop[{y[[1]]-2}]];
      p3=plet[{k[[1]]-1},{y[[1]]-1}];
      p3p=Map[({#[[1]],eq2[2,#[[2]]]})&,omyl[{{1,{k[[1]]+y[[1]]-1}}},p3]];
      p3m=Map[({-#[[1]],eq2[2,#[[2]]]})&,omyl[{{1,{k[[1]]+y[[1]]-3}}},p3]];
      Select[tf2[Join[p1,p2,p3p,p3m]],(#[[1]]!=0)&]]/; Length[y]==1;

(* Auxiliary function multip[p,{py,y}]={p*py,y} *)
multip[p_,my_]:={p*my[[1]],my[[2]]};
(* General y *)
plet[k_,y_]:=
Block[{sh,si},
      sh=ytoh[y];
      si=Flatten[Table[Map[multip[sh[[i,1]],#]&,pleth[k,sh[[i,2]]]],{i,1,Length[sh]}],1];
      Select[tf2[Map[({#[[1]],eq2[2,#[[2]]]})&,si]],(#[[1]]!=0)&]];
(* In pleth the argument h is {h1,h2,...} where hi is the symmetric function {ri}; page 143 *)
pleth[m_,h_]:=Fold[omul[2,#1,#2]&,{{1,{}}},Table[plethys[m,h[[i]]],{i,1,Length[h]}]];

(** Plethysm for U(n1) \[Rule] U(n2) **)
(* u is a representation of U(n1)
   f is the fundamental representation of U(n2) i.e.
   [1] in U(n1) reduces to f=[f1,f2,...] in U(n2) *)

pletuu[n1_,n2_,u_,f_]:={{1,f}}/; u=={1};
pletuu[n1_,n2_,u_,f_]:=pletuu1b[n1,n2,u,f]/; Length[u]==1;

(* If u has one row by application of Littlewood's rule *)
pletuu1a[n1_,n2_,u_,f_]:=pletuu1a[n1,n2,u,f]=
Block[{su1,sf1,sup,sufr,sufl,sufll,x,uns,eqs,eqd,sol},
      su1=syo1[u];
      sf1=tf1[{1,syo1[f]}];
      sup=tf2[Flatten[Table[pletuu[n1,n2,su1[[i]],f],{i,1,Length[su1]}],1]];
      sufr=omul[n2,sup,sf1];
      sufll=Map[({#,syo1[#]})&,syou[n2,wei[u]*wei[f]]];
      sufl=Select[sufll,(Complement[#[[2]],sufr[[All,2]]]=={})&];
      uns=Table[x[sufl[[i,1]]],{i,1,Length[sufl]}];
      eqs=Table[sufr[[i,1]]==Sum[uns[[j]]*Count[sufl[[j,2]],sufr[[i,2]]],{j,1,Length[uns]}],
                {i,1,Length[sufr]}];
      eqd={Sum[du[n2,sufl[[i,1]]]*uns[[i]],{i,1,Length[uns]}]==du[n1,u]};
      sol=Solve[Join[eqs,eqd],uns];
      Select[Table[{uns[[i]]/.sol[[1]],sufl[[i,1]]},{i,1,Length[uns]}],(#[[1]]!=0)&]];

(* If u has one row and f has one row *)
pletuu1b[n1_,n2_,u_,f_]:=(*pletuu1b[n1,n2,u,f]=*)
Block[{orbits,weight1,weight2,list},
orbits=-Sort[-parts[f[[1]],n2]];
weight1=parts[u[[1]],n1];
weight2=Map[Apply[Plus,orbits*#]&,weight1];
list=-Sort[-Select[Union[weight2],young1]];
Select[Map[{levdim[n2,#,weight2],chop[#]}&,list],(#[[1]]>0)&]];

pletuu1c[n1_,n2_,u_,f_]:=(*pletuu1c[n1,n2,u,f]=*)
Map[{#[[1]],eq1[n2,#[[2]]]}&,pletuu1b[n1,n2,u,f]];

(* Level dimensionality of the irrep y of U(m) in the weights w of U(m) *)
levdim[m_,y_,w_]:=
Block[{mat,shift},
mat=Table[If[j==k,1,0]*(i-j),{i,1,m},{j,1,m},{k,1,m}];
shift=conver[mat];
Sum[phase[m,i]*Count[w,y+shift[[i]]],{i,1,Length[shift]}]];
conver[mat_]:={mat[[1,1]]}/;Length[mat]==1;
conver[mat_]:=
Flatten[Table[Map[(#+mat[[1,i]])&,conver[Drop[mat,{1},{i}]]],{i,1,Length[mat]}],1];
phase[m_,i_]:=+1/; m==1 && i==1;
phase[m_,i_]:=phase[m,i]=
phase[m-1,Mod[i-1,(m-1)!]+1]*If[EvenQ[IntegerPart[(i-1)/((m-1)!)]],1,-1];

(* General u *)
pletuu[n1_,n2_,u_,f_]:=pletuu[n1,n2,u,f]=
Block[{sh,si},
      sh=ytoh[u];
      si=Flatten[Table[Map[multip[sh[[i,1]],#]&,pletuuh[n1,n2,sh[[i,2]],f]],{i,1,Length[sh]}],1];
      Select[tf2[si],(#[[1]]!=0)&]];
(* In pletuuh the argument h is {h1,h2,...} where hi is the symmetric function {ri} *)
pletuuh[n1_,n2_,h_,f_]:=pletuuh[n1,n2,h,f]=
Fold[omul[n2,#1,#2]&,{{1,{}}},Table[pletuu[n1,n2,h[[i]],f],{i,1,Length[h]}]];

(* Check of branching rules for all Young tableaux with weight p *)
check[n_,p_]:=
Block[{sy,dimu,dimos},
      sy=syou[n,p];
      dimu=Map[du[n,#]&,sy];
      dimos=Map[wei[Map[dos[n,#]&,#]]&,Map[bruos[n,#]&,sy]];
      Print[dimu];
      Print[dimos];];


(** Definition of a variety of series **)
(* Series of Young tableaux of a certain weight (with at most n rows) *)
syou[p_]:=Map[chop,-Sort[-Union[-Map[Sort[-#]&,parts[p,p]]]]];
syou[n_,p_]:=Map[chop,-Sort[-Union[-Map[Sort[-#]&,parts[p,n]]]]];
(* Series of Young tableaux with one box less than y *)
syo1[y_]:=
Block[{yt,sy},
      yt=Join[chop[y],{0}];
      sy=Table[Table[yt[[i]]-If[i==j && yt[[i]]>yt[[i+1]],1,0],
                     {i,1,Length[yt]-1}],
               {j,1,Length[yt]-1}];
      Map[chop,Select[sy,(#!=y)&]]];

(* Alpha series as defined in Eq (75) up to a maximum weight *)
(* Does not include the empty Young tableau {} *)
salp[maxp_]:=salp[maxp]=
Block[{p,fm,sa,sb},
      p=Floor[maxp/2];
      fm=Table[{i,i+1},{i,p,0,-1}];
      sa=Map[(#*fm)&,Union[Map[Map[If[#!=0,1,0]&,#]&,parts[p+1,p+1]]]];
      sb=Map[Select[#,(#!={0,0})&]&,sa];
      Select[Map[ftoy,sb],(wei[#]<=maxp)&]];

(* Beta series as defined in Eq (81) up to a maximum weight *)
(* Does not include the empty Young tableau {} *)
sbet[maxp_]:=sbet[maxp]=
Block[{s1},
      s1=Flatten[Table[syou[w],{w,1,Floor[maxp/2]}],1];
      Map[Flatten[#,1]&,Map[Map[({#,#})&,#]&,s1]]];

(* Gamma series as defined in Eq (65) up to a maximum weight *)
(* Does not include the empty Young tableau {} *)
sgam[maxp_]:=sgam[maxp]=
Block[{p,fm,sa,sb},
      p=Floor[maxp/2];
      fm=Table[{i+1,i},{i,p,0,-1}];
      sa=Map[(#*fm)&,Union[Map[Map[If[#!=0,1,0]&,#]&,parts[p+1,p+1]]]];
      sb=Map[Select[#,(#!={0,0})&]&,sa];
      Select[Map[ftoy,sb],(wei[#]<=maxp)&]];

(* Delta series as defined in Eq (70) up to a maximum weight *)
(* Does not include the empty Young tableau {} *)
sdel[maxp_]:=sdel[maxp]=2*Flatten[Table[syou[w],{w,1,Floor[maxp/2]}],1];

(* Eta series as defined in Theorem IB (self-conjugate partitions) up to a maximum weight *)
(* Does not include the empty Young tableau {} *)
seta[maxp_]:=seta[maxp]=
Block[{p,fm,sa,sb},
      p=Floor[maxp/2];
      fm=Table[{i,i},{i,p+1,1,-1}];
      sa=Map[(#*fm)&,Union[Map[Map[If[#!=0,1,0]&,#]&,parts[p+1,p+1]]]];
      sb=Map[Select[#,(#!={0,0})&]&,sa];
      Select[Map[ftoy,Map[(#-1)&,sb,{2}]],(wei[#]<=maxp)&]];

(** Branching from U(n1*n2) to U(n1) x U(n2) **)
(* If u has one row *)
bruuu1[n1_,n2_,u_]:=
Block[{l1,l2},
      l1=-Sort[-Union[-Map[Sort[-#]&,parts[u[[1]],Min[u[[1]],Min[n1,n2]]]]]];
      l2=Map[Select[#,(#!=0)&]&,l1];
      Map[{#,#}&,l2]]/;Length[chop[u]]==1;
(* General u *)
bruuu1[n1_,n2_,u_]:=bruuu1[n1,n2,u]=
Block[{ua,uf,rf,ul,rl,ifl,rfl,m2,r2},
      ua=chop[u];
      uf=Drop[ua,-1];
      rf=bruuu1[n1,n2,uf];
      ul=Take[ua,-1];
      rl=bruuu1[n1,n2,ul];
      ifl=Flatten[Table[{rf[[i]],rl[[j]]},{i,1,Length[rf]},{j,1,Length[rl]}],1];
      rfl=Flatten[Map[omu[n1,n2,#[[1]],#[[2]]]&,ifl],1];
      m2=Select[omu0[n1*n2,uf,ul],(#!=ua)&];
      r2=Flatten[Map[bruuu1[n1,n2,#]&,m2],1];
      Sort[complement[rfl,r2],(wei[#1[[1]]]>wei[#2[[1]]])&]];

(** Branching from U(n1+n2) to U(n1) x U(n2) **)
(* If u has one row *)
bruuu2[n1_,n2_,u_]:=Table[{{i},{u[[1]]-i}},{i,u[[1]],0,-1}]/;Length[chop[u]]==1;
(* General u *)
bruuu2[n1_,n2_,u_]:=bruuu2[n1,n2,u]=
Block[{ua,uf,rf,ul,rl,ifl,rfl,m2,r2},
      ua=chop[u];
      uf=Drop[ua,-1];
      rf=bruuu2[n1,n2,uf];
      ul=Take[ua,-1];
      rl=bruuu2[n1,n2,ul];
      ifl=Flatten[Table[{rf[[i]],rl[[j]]},{i,1,Length[rf]},{j,1,Length[rl]}],1];
      rfl=Flatten[Map[omu[n1,n2,#[[1]],#[[2]]]&,ifl],1];
      m2=Select[omu0[n1*n2,uf,ul],(#!=ua)&];
      r2=Flatten[Map[bruuu2[n1,n2,#]&,m2],1];
      Sort[complement[rfl,r2],(wei[#1[[1]]]>wei[#2[[1]]])&]];
(* Alternative algorithm with symmetric S functions (slower) *)
(*bruuu2[n1_,n2_,u_]:=
Block[{sh,sha,shh,suu},
      sh=ytoh[u];
      sha=Map[{#[[1]],Map[bruuu2[n1,n2,#]&,#[[2]]]}&,sh];
      shh=Map[Map[tf4,#,{2}]&,sha];
      suu=Map[tf3[{#[[1]],Fold[omul[3,6,#1,#2]&,{{1,{{0},{0}}}},
                                Table[#[[2,i]],{i,1,Length[#[[2]]]}]]}]&,shh];
      Select[tf2[Flatten[suu,1]],(#[[1]]\[NotEqual]0)&]];*)


(*** An application: su4[n,T] gives all SU(4) irreps in order of maximal orbital symmetry
                     for a given particle number n and isospin T ***)
gsu4[u4_]:=
Block[{u4a,la,mu,nu},
      u4a=Join[u4,Table[0,{i,1,4-Length[u4]}]];
      la=u4a[[1]]-u4a[[2]];
      mu=u4a[[2]]-u4a[[3]];
      nu=u4a[[3]]-u4a[[4]];
      3*la*(la+4)+3*nu*(nu+4)+4*mu*(mu+4)+4*mu*(la+nu)+2*la*nu];
su4[n_,T_]:=
Block[{sy},
      sy=Sort[syou[4,n],(gsu4[#1]<gsu4[#2])&];
      Select[sy,MemberQ[Flatten[Map[eq1[2,#]/2&,bruuu1[2,2,#],{2}]],T]&]];
favsu4[n_,T_]:=
Block[{k2,k4,t1,t2},
      k2=Floor[n/2];
      k4=Floor[n/4];
      t1=Ceiling[(n/2-T)/2];
      t2=Floor[(n/2-T)/2];
      Which[Mod[n,4]==2 && T==0,{k4+1,k4+1,k4,k4},
            Mod[n,2]==0,{k2-t2,k2-t1,t1,t2},
            Mod[n,2]==1,{k2-t1+1,k2-t2,t1,t2}]];
(*** Choice of SU(3) representation with most quanta in z followed by x followedby y ***)
(* NN = oscillator shell; n = # identical particles; *)
hw[NN_,n_]:=
Block[{ps},
ps=-Sort[-parts[NN,3]];
ps=Flatten[Map[({#,#})&,ps],1];
u3=Apply[Plus,Take[ps,n]];
eq3[3,u3]];

(*** Multiplicity for the SO(2f+1) -> SO(3) reduction for given angular momentum ff ***)
(* multiplicity[f_,0,ff_]:=ff; multiplicity[f_,v_,-1]:=v. *)
multiplicity[f_,v_,ff_]:=multiplicity[f,v,ff]=
-Residue[
(z^(2*ff+1)-1)*(z^(2*v+2*f-1)-1)*Product[z^(v+k)-1,{k,1,2*f-2}]/
(z^(f*v+ff+2)*Product[z^(k+1)-1,{k,1,2f-2}]),{z,0}]/2;

tabula[f_,vmax_]:=
(tab=Table[multiplicity[f,v,ff],{ff,-1,f*vmax},{v,0,vmax}];TableForm[tab]);
