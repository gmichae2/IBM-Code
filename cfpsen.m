(* ::Package:: *)
Get[FileNameJoin[{NotebookDirectory[], "racah.m"}]]
Get[FileNameJoin[{NotebookDirectory[], "stats.m"}]]


(*** Single-j CFPs in a seniority basis ***)
(* Must be read in from shells.m or ibm.m *)
(* j is integer for bosons and half-odd integer for fermions *)
(* General notation:
   cfps[j,m,vm,am,Jm,r,vr,ar,Jr,n,vn,an,Jn]=[j^m(vm,am,Jm),j^r(vr,ar,Jr)|}j^n,vn,an,Jn] *)

(* Number of n-particle states with angular momentum J *)
muln[j_,n_,J_]:=0/; n<0;
muln[j_,0,J_]:=If[J==0,1,0];
muln[j_,1,J_]:=If[j==J,1,0];
muln[j_,n_,J_]:=muln[j,n,J]=
Which[EvenQ[2*j],nstat1[1,{j},n,{J}],OddQ[2*j],nstat1[-1,{j},n,{J}]];
(* Number of states with seniority v and angular momentum J *)
mulv[j_,v_,J_]:=0/; v<0;
mulv[j_,0,J_]:=If[J==0,1,0];
mulv[j_,1,J_]:=If[j==J,1,0];
mulv[j_,v_,J_]:=muln[j,v,J]-muln[j,v-2,J];

(** The [(m,r=n-m)->n] CFP [j^m(vm,am,Jm),j^r(vr,ar,Jr)|}j^n,vn,an,Jn] **)
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:="gobledigook"/; r+m!=n;
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=0/;
vn>n || vn<0 || vm>m || vm<0 || vr>r || vr<0 || OddQ[n-vn] || OddQ[m-vm] || OddQ[r-vr];
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=0/;
Abs[vm-vr]>vn || vm+vr<vn || an>mulv[j,vn,Jn] || am>mulv[j,vm,Jm] || ar>mulv[j,vr,Jr];
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=0/;
!trian[Jm,Jr,Jn];
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=1/;
m==0 && vr==vn && ar==an && Jr==Jn;
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=0/;
m==0 && (vr!=vn || ar!=an || Jr!=Jn);
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=1/;
n==m && vm==vn && am==an && Jm==Jn;
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=0/;
n==m && (vm!=vn || am!=an || Jm!=Jn);

(* The [(1,r=n-1)->n] CFP [j,j^r(vr,ar,Jr)|}j^n,vn,an,Jn] *)
(* In terms of the [(r=n-1,1)->n] CFP [j^r(vr,ar,Jr),j|}j^n,vn,an,Jn] *)
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=
Which[EvenQ[2*j],1,OddQ[2*j],(-1)^r]*(-1)^(Jm+Jr-Jn)*
cfps[j,n,vr,ar,Jr,vn,an,Jn]/; m==1;

(* The [(m=n-1,1)->n] CFP [j^m(vm,am,Jm),j|}j^n,vn,an,Jn] *)
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=
cfps[j,n,vm,am,Jm,vn,an,Jn]/; r==1;

cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=
Which[EvenQ[2*j],1,OddQ[2*j],(-1)^(m*r)]*(-1)^(Jm+Jr-Jn)*
cfps[j,r,vr,ar,Jr,m,vm,am,Jm,n,vn,an,Jn]/; m>r;

(* As a sum over [(1,n-1)->n] times [(1,m-1)->m] times [(m-1,n-m)->n-1] CFPs *)
cfps[j_,m_,vm_,am_,Jm_,r_,vr_,ar_,Jr_,n_,vn_,an_,Jn_]:=
cfps[j,m,vm,am,Jm,r,vr,ar,Jr,n,vn,an,Jn]=
Block[{s,Rn1,Jn1,Qn1,Jm1s,nm1s,Rm1s,Rm1,Jm1,Qm1},
s=Sqrt[2*Jm+1]*
Sum[Sqrt[2*Jn1+1]*cfps[j,1,1,1,j,n-1,vn1,an1,Jn1,n,vn,an,Jn]*
    Sum[wcoef[j,Jm1,Jn,Jr,Jm,Jn1]*
        cfps[j,1,1,1,j,m-1,vm1,am1,Jm1,m,vm,am,Jm]*
        cfps[j,m-1,vm1,am1,Jm1,r,vr,ar,Jr,n-1,vn1,an1,Jn1],
        {vm1,Abs[vm-1],vm+1,2},{Jm1,Abs[Jm-j],Jm+j},{am1,1,mulv[j,vm1,Jm1]}],
   {vn1,Abs[vn-1],vn+1,2},{Jn1,Abs[Jn-j],Jn+j},{an1,1,mulv[j,vn1,Jn1]}];
redsqrtrat[s]];

(* Calculation of v<n CFPs from seniority relations *)
(* Bosons *)
cfps[j_,n_,v1_,a1_,J1_,v_,a_,J_]:=
Sqrt[(2*j-1+n+v)*v/(n*(2*j-1+2*v))]*
cfps[j,v,v1,a1,J1,v,a,J]/; EvenQ[2*j] && v<n && v1==v-1;
cfps[j_,n_,v1_,a1_,J1_,v_,a_,J_]:=
(-1)^(J+J1)*Sqrt[(n-v)*(v+1)*(2*J1+1)/(n*(2*j+1+2*v)*(2*J+1))]*
cfps[j,v1,v,a,J,v1,a1,J1]/; EvenQ[2*j] && v<n && v1==v+1;
(* Fermions *)
cfps[j_,n_,v1_,a1_,J1_,v_,a_,J_]:=
Sqrt[(2*j+3-n-v)*v/(n*(2*j+3-2*v))]*
cfps[j,v,v1,a1,J1,v,a,J]/; OddQ[2*j] && v<n && v1==v-1;
cfps[j_,n_,v1_,a1_,J1_,v_,a_,J_]:=
(-1)^(J+j-J1)*Sqrt[(n-v)*(v+1)*(2*J1+1)/(n*(2*j+1-2*v)*(2*J+1))]*
cfps[j,v1,v,a,J,v1,a1,J1]/; OddQ[2*j] && v<n && v1==v+1;

(* The n=1 CFP *)
cfps[j_,1,0,1,0,1,1,J_]:=If[j==J,1,0];

(* Recursive calculation of non-orthonormal v=n CFPs *)
(* The parent state has v0=n-1, which can give rise to a state
      with v=n
      with v=n-2 (which is known and should be projected out).
   J0 refers to the angular momentum and a0 refers to the multiplicity label
   of the v0=n-1 state *)
cfpsno[j_,1,0,1,0,0,1,0,J_]:=If[j==J,1,0];
cfpsno[j_,n_,v1_,a1_,J1_,v0_,a0_,J0_,J_]:=0/;
!trian[j,J0,J] || !trian[j,J1,J] || v0>n-1 || v1>n-1 || v0<0 || v1<0 ||
a0>mulv[j,v0,J0] || a1>mulv[j,v1,J1];
cfpsno[j_,n_,v1_,a1_,J1_,v0_,a0_,J0_,J_]:=cfpsno[j,n,v1,a1,J1,v0,a0,J0,J]=
Block[{s},
s=delta[v0,v1]*delta[a0,a1]*delta[J0,J1]+
(-1)^(J0+J1)*(n-1)*Sqrt[(2*J0+1)*(2*J1+1)]*
Sum[racah[J2,j,J0,J,j,J1]*
    cfps[j,n-1,v2,a2,J2,v0,a0,J0]*cfps[j,n-1,v2,a2,J2,v1,a1,J1],
    {v2,Max[Abs[v0-1],Abs[v1-1]],Min[n-2,v0+1,v1+1],2},
    {J2,Max[Abs[J0-j],Abs[J1-j]],Min[J0+j,J1+j]},
    {a2,1,mulv[j,v2,J2]}];
redsqrtrat[s]];

(* Conversion to an orthonormal basis for v=n CFPs *)
cfps[j_,n_,v1_,a1_,J1_,v_,a_,J_]:=
cfps[j,n,v1,a1,J1,v,a,J]=
Block[{dim2,lis,s},
dim2=mulv[j,v-2,J];
lis=lininds[j,v,J];
s=Sum[acs[j,v,J,dim2+a,k]*
      If[k<=dim2,cfps[j,v,v1,a1,J1,v-2,k,J],
                cfpsno[j,v,v1,a1,J1,v-1,lis[[k-dim2,1]],lis[[k-dim2,2]],J]],
      {k,dim2+a,1,-1}];
redsqrtrat[s]];

(* List of all n-particle states with angular momentum J
   obtained by coupling all states |n-1,v1=n-1,a1,J1> to j *)
lindeps[j_,v_,J_]:=
Flatten[Table[{a1,J1},{J1,Abs[J-j],J+j},{a1,1,mulv[j,v-1,J1]}],1];

(* List of a set of linearly independent n-particle states with angular momentum J
   obtained by coupling states |n-1,v1=n-1,a1,J1> to j. *)
lininds[j_,v_,J_]:=lininds[j,v,J]=
Block[{dim,lisoc,lis,prec,dl,do,itel,over},
dim=mulv[j,v,J];
lisoc=lindeps[j,v,J];
(*Print["j=",j,"; v=",v,"; J=",J,"; dim=",dim,lisoc];*)
prec=0.1^12;
For[lis={}; dl=1.; itel=1,
    itel<=Length[lisoc] && Length[lis]<dim,itel++,
    lis=Join[lis,{lisoc[[itel]]}];
    (*Print[lis];*)
    over=omas[lis,j,v,J];
    do=Det[N[over]];
    (*Print["do=",do];*)
    (*lis=If[Det[over]==0,Drop[lis,-1],lis]];*)
    lis=If[Abs[do]<prec*dl,Drop[lis,-1],lis];
    dl=If[Abs[do]<prec*dl,dl,Abs[do]];
    (*Print["dl=",dl]*)];
lis];

(* Overlap matrix:
   the first dim2 states are |n,v=n-2,a,J> (orthonormal)
   the remaining states are |(n-1,v1=n-1,a1,J1) x j; J> *)
omas[lis_,j_,v_,J_]:=
Block[{dim2},
dim2=mulv[j,v-2,J];
Table[Which[ia<=dim2 && ib<=dim2,
            Sum[cfps[j,v,v1,a1,J1,v-2,ia,J]*cfps[j,v,v1,a1,J1,v-2,ib,J],
                {v1,v-3,v-1,2},{J1,Abs[J-j],J+j},{a1,1,mulv[j,v1,J1]}],
            ia<=dim2 && ib>dim2,
            Sum[cfps[j,v,v1,a1,J1,v-2,ia,J]*
                cfpsno[j,v,v1,a1,J1,v-1,lis[[ib-dim2,1]],lis[[ib-dim2,2]],J],
                {v1,v-3,v-1,2},{J1,Abs[J-j],J+j},{a1,1,mulv[j,v1,J1]}],
            ia>dim2 && ib<=dim2,
            Sum[cfpsno[j,v,v1,a1,J1,v-1,lis[[ia-dim2,1]],lis[[ia-dim2,2]],J]*
                cfps[j,v,v1,a1,J1,v-2,ib,J],
                {v1,v-3,v-1,2},{J1,Abs[J-j],J+j},{a1,1,mulv[j,v1,J1]}],
            ia>dim2 && ib>dim2,
            Sum[cfpsno[j,v,v1,a1,J1,v-1,lis[[ia-dim2,1]],lis[[ia-dim2,2]],J]*
                cfpsno[j,v,v1,a1,J1,v-1,lis[[ib-dim2,1]],lis[[ib-dim2,2]],J],
                {v1,v-3,v-1,2},{J1,Abs[J-j],J+j},{a1,1,mulv[j,v1,J1]}]],
      {ia,1,dim2+Length[lis]},{ib,1,dim2+Length[lis]}]];
omas[j_,v_,J_]:=omas[j,v,J]=
redsqrtrat[omas[lininds[j,v,J],j,v,J]];

(* Recursive calculation of acs[v,J,i,j] *)
acs[j_,v_,J_,k_,l_]:=acs[j,v,J,k,l]=
Which[ncs[j,v,J,k]==0,Print["Zero norm","; j=",j,"; v=",v,"; J=",J,"; k=",k]; Abort[],
      k==l,1/Sqrt[ncs[j,v,J,k]],
      k>l,-redsqrtrat[Sum[ots[j,v,J,k,i]*acs[j,v,J,i,l],{i,l,k-1}]/
                      Sqrt[ncs[j,v,J,k]]]];
ncs[j_,v_,J_,k_]:=(*ncs[j,v,J,k]=*)
redsqrtrat[omas[j,v,J][[k,k]]-Sum[ots[j,v,J,k,i]^2,{i,1,k-1}]];
ots[j_,v_,J_,k_,l_]:=(*ots[j,v,J,k,l]=*)
redsqrtrat[Sum[acs[j,v,J,l,i]*omas[j,v,J][[k,i]],{i,1,l}]];
(*oos[j_,v_,J_,k_,l_]:=omas[j,v,J][[k,l]];*)

(* Reduce r to the sqrt of a rational number *)
redsqrtrat[r_]:=
Block[{s,r2},
s=Sign[N[r]];
r2=Expand[r^2];
If[Element[r2,Rationals],s*Sqrt[r2],Print["No Sqrt of rational number: ",r]; Abort[]]];

(** Tests **)
testcfps[j_,n_,m_]:=
Block[{sa,Jns,bn,vn1,an1,vn2,an2,Jn,Jms,bm,vm,am,Jm,r,Jrs,br,vr,ar,Jr,s},
sa=Which[EvenQ[2*j],1,OddQ[2*j],-1];
Jns=serj[sa,{j},n]; Jms=serj[sa,{j},m];
r=n-m; Jrs=serj[sa,{j},r];
Do[Jn=Jns[[in,1]];
   Print["Jn=",Jn];
   bn=Which[EvenQ[2*j],basb[{j},n,Jn],OddQ[2*j],basf[{{0,j-1/2,{j}}},n,Jn]];
   Do[vn1=bn[[in1,1,2]]; an1=bn[[in1,1,3]];
      vn2=bn[[in2,1,2]]; an2=bn[[in2,1,3]]; 
      s=Sum[Jm=Jms[[im,1]]; Jr=Jrs[[ir,1]];
            If[!trian[Jm,Jr,Jn],0,
               bm=Which[sa==1,basb[{j},m,Jm],sa==-1,basf[{{0,j-1/2,{j}}},m,Jm]];
               br=Which[sa==1,basb[{j},r,Jr],sa==-1,basf[{{0,j-1/2,{j}}},r,Jr]];
               Sum[vm=bm[[ima,1,2]]; am=bm[[ima,1,3]];
                   vr=br[[ira,1,2]]; ar=br[[ira,1,3]];
                   cfps[j,m,vm,am,Jm,r,vr,ar,Jr,n,vn1,an1,Jn]*
                   cfps[j,m,vm,am,Jm,r,vr,ar,Jr,n,vn2,an2,Jn],
                   {ima,1,Length[bm]},{ira,1,Length[br]}]],
             {im,1,Length[Jms]},{ir,1,Length[Jrs]}];
      (*Print["bra=",bn[[in1,1]]," & ket=",bn[[in2,1]],": ",redsqrtrat[s]];*)
      If[(in1==in2 && redsqrtrat[s]!=1) || (in1!=in2 && redsqrtrat[s]!=0),
         Print["!!!bra=",bn[[in1,1]]," & !!!ket=",bn[[in2,1]],": ",redsqrtrat[s]]],
      {in1,1,Length[bn]},{in2,1,Length[bn]}],
   {in,1,Length[Jns]}]];



