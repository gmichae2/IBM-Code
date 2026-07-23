(* ::Package:: *)

(*** Numbers of states for n bosons (s=+1) or for n fermions (s=-1) ***)

(* Partitions of a positive integer n in p positive integers *)
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

(* Number of (anti-)symmetric, independent n-particle states
   distributed over p orbitals b={q1,...,qp} coupled to total angular momentum J *)
nstat[s_,b1_,n_,J_]:=0/; n==0 && J!=Table[0,{i,1,Length[J]}];
nstat[s_,b1_,n_,J_]:=1/; n==0 && J==Table[0,{i,1,Length[J]}];
nstat[s_,b1_,n_,J_]:=nstat[s,b1,n,J]=
Block[{jlast,Jk,Jks,JJks},
jlast=b1[[-1,3]];
If[Length[b1]==1,nstat1[s,jlast,n,J],
   Sum[Jks=serj[s,jlast,k];
       Sum[Jk=Jks[[i]];
           JJks=genang[J,Jk];
           nstat1[s,jlast,k,Jk]*
           Sum[nstat[s,Drop[b1,-1],n-k,JJks[[j]]],{j,1,Length[JJks]}],
           {i,1,Length[Jks]}],
       {k,0,n}]]];
(* Number of (anti-)symmetric, independent n-particle states
   distributed over p orbitals b={q1,...,qp} with occupancies nb={n1,...,np}
   coupled to total angular momentum J *)
nstat[s_,b1_,n_,nb_,J_]:="rubbishn"/; n!=Apply[Plus,nb];
nstat[s_,b1_,n_,nb_,J_]:=0/; Apply[Or,Map[(#<0)&,nb]];
nstat[s_,b1_,n_,nb_,J_]:=0/; n==0 && J!=Table[0,{i,1,Length[J]}];
nstat[s_,b1_,n_,nb_,J_]:=1/; n==0 && J==Table[0,{i,1,Length[J]}];
nstat[s_,b1_,n_,nb_,J_]:=nstat[s,b1,n,nb,J]=
Block[{jlast,nlast,Jk,Jks,JJks},
jlast=b1[[-1,3]]; nlast=nb[[-1]];
If[Length[b1]==1,nstat1[s,jlast,nlast,J],
   Jks=serj[s,jlast,nlast];
   Sum[Jk=Jks[[i]];
       JJks=genang[J,Jk];
       nstat1[s,jlast,nlast,Jk]*
       Sum[nstat[s,Drop[b1,-1],n-nlast,Drop[nb,-1],JJks[[j]]],{j,1,Length[JJks]}],
       {i,1,Length[Jks]}]]];
       
(* Series of angular momenta possible for n particles in orbital j *)
serj[s_,j_,n_]:={Table[0,{i,1,Length[j]}]}/; n==0;
serj[s_,j_,n_]:={j}/; n==1;
serj[s_,j_,n_]:=
Block[{ser,ser1},
ser1=serj[s,j,n-1];
ser=Union[Flatten[Map[genang[#,j]&,ser1],1]];
Select[ser,(nstat1[s,j,n,#]!=0)&]];
(* Series of angular momenta possible for n particles
   distributed over p orbitals b={q1,...,qp} with occupancies nb={n1,...,np} *)
serb[s_,b1_,n_,nb_]:="rubbishs"/; n!=Apply[Plus,nb];
serb[s_,b1_,n_,nb_]:={Table[0,{i,1,Length[b1[[1,3]]]}]}/; n==0;
serb[s_,b1_,n_,nb_]:=
Block[{zero,ser},
zero={Table[0,{i,1,Length[b1[[1,3]]]}]};
ser=Map[serj[s,#[[1]],#[[2]]]&,Table[{b1[[i,3]],nb[[i]]},{i,1,Length[b1]}]];
Fold[serbl,zero,ser]];
serbl[l1_,l2_]:=
Union[Flatten[Table[genang[l1[[i1]],l2[[i2]]],{i1,1,Length[l1]},{i2,1,Length[l2]}],2]];
(* Series of angular momenta possible for n particles
   distributed over p orbitals b1={q1,...,qp} *)
serb[s_,b1_,n_]:={Table[0,{i,1,Length[b1[[1,3]]]}]}/; n==0;
serb[s_,b1_,n_]:=
Block[{p,o,nbs},
p=Length[b1]; o=Map[df[#[[3]]]&,b1];
nbs=Which[s==1,parts[n,p],s==-1,parts[n,p,o]];
Union[Flatten[Table[serb[s,b1,n,nbs[[i]]],{i,1,Length[nbs]}],1]]];
(* Series of angular momenta possible for (nn+np) particles
   distributed over pn orbitals b1n={qn1,...,qnp} and pp orbitals b1p={qp1,...,qpp} *)
serb[s_,b1n_,b1p_,nn_,np_]:=
Block[{sern,serp,sernp},
sern=serb[s,b1n,nn]; serp=serb[s,b1p,np];
sernp=Table[genang[sern[[in]],serp[[ip]]],{in,1,Length[sern]},{ip,1,Length[serp]}];
Union[Flatten[sernp,2]]];
    
(* Number of (anti-)symmetric, independent n-particle states
   in orbital j coupled to total angular momentum J *)
nstat1[s_,j_,n_,J_]:=1/; n==0 && J==Table[0,{i,1,Length[j]}];
nstat1[s_,j_,n_,J_]:=0/; n==0 && J!=Table[0,{i,1,Length[j]}];
nstat1[s_,j_,n_,J_]:=
nstatm[s,j,n,J+{0}]-nstatm[s,j,n,J+{1}]/; Length[j]==1;
nstat1[s_,j_,n_,J_]:=
nstatm[s,j,n,J+{0,0}]-nstatm[s,j,n,J+{0,1}]-
nstatm[s,j,n,J+{1,0}]+nstatm[s,j,n,J+{1,1}]/; Length[j]==2;
nstat1[s_,j_,n_,J_]:=
nstatm[s,j,n,J+{0,0,0}]-nstatm[s,j,n,J+{0,0,1}]-
nstatm[s,j,n,J+{0,1,0}]+nstatm[s,j,n,J+{0,1,1}]-
nstatm[s,j,n,J+{1,0,0}]+nstatm[s,j,n,J+{1,0,1}]+
nstatm[s,j,n,J+{1,1,0}]-nstatm[s,j,n,J+{1,1,1}]/; Length[j]==3;
nstatm[s_,j_,n_,M_]:=Length[statm[s,j,n,M]];

(* Number of (anti-)symmetric, independent n-particle states
   in orbital j with total angular momentum projection M *)
statm[s_,j_,n_,M_]:=statm[s,j,n,M]=
Which[s==1 && Length[j]==1,
	  Select[Flatten[Table[Map[(Join[#,{{m1}}])&,statm[s,j,n-1,M-{m1}]],
						   {m1,-j[[1]],+j[[1]]}],1],
			 (Sort[#]==#)&],
	  s==1 && Length[j]==2,
	  Select[Flatten[Table[Map[(Join[#,{{m1,m2}}])&,statm[s,j,n-1,M-{m1,m2}]],
						   {m1,-j[[1]],+j[[1]]},{m2,-j[[2]],+j[[2]]}],2],
			 (Sort[#]==#)&],
      s==1 && Length[j]==3,
	  Select[Flatten[Table[Map[(Join[#,{{m1,m2,m3}}])&,statm[s,j,n-1,M-{m1,m2,m3}]],
						   {m1,-j[[1]],+j[[1]]},{m2,-j[[2]],+j[[2]]},{m3,-j[[3]],+j[[3]]}],3],
             (Sort[#]==#)&],
      s==-1 && Length[j]==1,
	  Select[Select[Flatten[Table[Map[(Join[#,{{m1}}])&,statm[s,j,n-1,M-{m1}]],
								  {m1,-j[[1]],+j[[1]]}],1],
					(Sort[#]==#)&],(Union[#]==#)&],
	  s==-1 && Length[j]==2,
      Select[Select[Flatten[Table[Map[(Join[#,{{m1,m2}}])&,statm[s,j,n-1,M-{m1,m2}]],
								  {m1,-j[[1]],+j[[1]]},{m2,-j[[2]],+j[[2]]}],2],
					(Sort[#]==#)&],(Union[#]==#)&],
	  s==-1 && Length[j]==3,
      Select[Select[Flatten[Table[Map[(Join[#,{{m1,m2,m3}}])&,statm[s,j,n-1,M-{m1,m2,m3}]],
								  {m1,-j[[1]],+j[[1]]},{m2,-j[[2]],+j[[2]]},{m3,-j[[3]],+j[[3]]}],3],
					(Sort[#]==#)&],(Union[#]==#)&]];
statm[s_,j_,n_,M_]:={{M}}/;
n==1 && Apply[And,Map[(#>=0)&,j-Abs[M]]] && Apply[And,Map[IntegerQ,j-M]];
statm[s_,j_,n_,M_]:={}/;
n==1 && !(Apply[And,Map[(#>=0)&,j-Abs[M]]] && Apply[And,Map[IntegerQ,j-M]]);
