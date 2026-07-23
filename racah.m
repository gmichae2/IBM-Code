(* ::Package:: *)

(*** Angular momentum objects ***)

delta[i_,j_]:=0/;i!=j;
delta[i_,j_]:=1/;i==j;
(* Triangular condition *)
trian[j1_,j2_,j3_]:=(Abs[j1-j2]<=j3 && j1+j2>=j3 && IntegerQ[j1+j2-j3]);

(** Coupling coefficients with multiple arguments **)
(* g can be {j} or {j,t} or {l,s,t} *)
trianv[g1_,g2_,g3_]:=Apply[And,MapThread[trian,{g1,g2,g3}]];
clebschv[j1_,j2_,j3_,m1_,m2_,m3_]:=Apply[Times,MapThread[clebsch,{j1,j2,j3,m1,m2,m3}]];
wignerv[j1_,j2_,j3_,m1_,m2_,m3_]:=Apply[Times,MapThread[wigner,{j1,j2,j3,m1,m2,m3}]];
racahv[g1_,g2_,g3_,g4_,g5_,g6_]:=Apply[Times,MapThread[racah,{g1,g2,g3,g4,g5,g6}]];
ucoefv[g1_,g2_,g3_,g4_,g5_,g6_]:=Apply[Times,MapThread[ucoef,{g1,g2,g3,g4,g5,g6}]];
wcoefv[g1_,g2_,g3_,g4_,g5_,g6_]:=Apply[Times,MapThread[wcoef,{g1,g2,g3,g4,g5,g6}]];
ninejv[g1_,g2_,g3_,g4_,g5_,g6_,g7_,g8_,g9_]:=Apply[Times,MapThread[ninej,{g1,g2,g3,g4,g5,g6,g7,g8,g9}]];
xcoefv[g1_,g2_,g3_,g4_,g5_,g6_,g7_,g8_,g9_]:=Apply[Times,MapThread[xcoef,{g1,g2,g3,g4,g5,g6,g7,g8,g9}]];
twelvej1v[j1_,j2_,j3_,j4_,l1_,l2_,l3_,l4_,k1_,k2_,k3_,k4_]:=
Apply[Times,MapThread[twelvej1,{j1,j2,j3,j4,l1,l2,l3,l4,k1,k2,k3,k4}]];
twelvej2v[j1_,j2_,j3_,j4_,l1_,l2_,l3_,l4_,k1_,k2_,k3_,k4_]:=
Apply[Times,MapThread[twelvej2,{j1,j2,j3,j4,l1,l2,l3,l4,k1,k2,k3,k4}]];

(** Generate all allowed angular momenta from the coupling of g1 and g2 **)
genang[g1_,g2_]:=nonsens/;Length[g1]!=Length[g2];
genang[g1_,g2_]:=Table[{a},{a,Abs[g1[[1]]-g2[[1]]],g1[[1]]+g2[[1]]}]/;Length[g1]==1;
genang[g1_,g2_]:=Flatten[Table[{a,b},{a,Abs[g1[[1]]-g2[[1]]],g1[[1]]+g2[[1]]},
							         {b,Abs[g1[[2]]-g2[[2]]],g1[[2]]+g2[[2]]}],1]/;Length[g1]==2;
genang[g1_,g2_]:=Flatten[Table[{a,b,c},{a,Abs[g1[[1]]-g2[[1]]],g1[[1]]+g2[[1]]},
							           {b,Abs[g1[[2]]-g2[[2]]],g1[[2]]+g2[[2]]},
						               {c,Abs[g1[[3]]-g2[[3]]],g1[[3]]+g2[[3]]}],2]/;Length[g1]==3;

(** Phase factors pf, dimensional factors df and sf **)
(*pf[g_]:=(-1)^Apply[Plus,Flatten[g]];*)
pf[g_]:=(-1)^Apply[Plus,g];
df[g_]:=Apply[Times,Map[(2#+1)&,g]];
sf[g_]:=Sqrt[Apply[Times,Map[(2#+1)&,g]]];

(** Clebsch-Gordan and Wigner coefficients **)
clebsch[j1_,j2_,j_,m1_,m2_,m_]:=(*clebsch[j1,j2,j,m1,m2,m]=*)
(-1)^(j1-j2+m)*reduceSqrt[Sqrt[2j+1]*wigner[j1,j2,j,m1,m2,-m]];

wigner[j1_,j2_,j3_,m1_,m2_,m3_]:=0/;m1+m2+m3!=0;
wigner[j1_,j2_,j3_,m1_,m2_,m3_]:=0/;m1+j1<0 || m1-j1>0 || m2+j2<0 || m2-j2>0 || m3+j3<0 || m3-j3>0;
wigner[j1_,j2_,j3_,m1_,m2_,m3_]:=0/;Abs[j1-j2]-j3>0 || j1+j2-j3<0;
wigner[j1_,j2_,j3_,m1_,m2_,m3_]:=wignerNumeric[j1,j2,j3,m1,m2,m3]/;
NumberQ[j1] && NumberQ[j2] && NumberQ[j3] && NumberQ[m1] && NumberQ[m2] && NumberQ[m3];
wigner[j1_,j2_,j3_,m1_,m2_,m3_]:=wignerSymbolic[j1,j2,j3,m1,m2,m3];

wignerNumeric[j1_,j2_,j3_,m1_,m2_,m3_]:=(*wignerNumeric[j1,j2,j3,m1,m2,m3]=*)
Block[{t,tmin,tmax,fac},
      fac=(-1)^(j1-j2-m3)*Sqrt[delta[j1,j2,j3]];
      fac=fac*Sqrt[(j1+m1)!(j1-m1)!(j2+m2)!(j2-m2)!(j3+m3)!(j3-m3)!];
      tmin=Max[0,j2-j3-m1,j1-j3+m2];
      tmax=Min[j1+j2-j3,j1-m1,j2+m2];
      fac=fac*Sum[worm[j1,j2,j3,m1,m2,t],{t,tmin,tmax}];
      reduceSqrt[fac]];
delta[x_,y_,z_]:=(x+y-z)!(x-y+z)!(-x+y+z)!/(x+y+z+1)!;
worm[j1_,j2_,j3_,m1_,m2_,t_]:=
(-1)^t/(t!*(j1+j2-j3-t)!*(j1-m1-t)!*(j2+m2-t)!*(j3-j2+m1+t)!*(j3-j1-m2+t)!);

wignerSymbolic[j1_,j2_,j3_,m1_,m2_,m3_]:=wignerSymbolic[j2,j3,j1,m2,m3,m1]/;
NumberQ[j1] && (!NumberQ[j3] || j1-j3<0);
wignerSymbolic[j1_,j2_,j3_,m1_,m2_,m3_]:=wignerSymbolic[j3,j1,j2,m3,m1,m2]/;
NumberQ[j2] && (!NumberQ[j3] || j2-j3<0);
wignerSymbolic[j1_,j2_,j3_,m1_,m2_,m3_]:=wignerSymbolic[j2,j1,j3,-m2,-m1,-m3]/;j2-j1<0;
wignerSymbolic[j1_,j2_,j3_,m1_,m2_,m3_]:=(-1)^(j1-m1)/Sqrt[2j1+1]/;j3==0;
wignerSymbolic[j1_,j2_,j3_,m1_,m2_,m3_]:=
((Sqrt[(j2+m2)(j3-m3)]*wigner[j1,j2-1/2,j3-1/2,m1,m2-1/2,m3+1/2]
 -Sqrt[(j2-m2)(j3+m3)]*wigner[j1,j2-1/2,j3-1/2,m1,m2+1/2,m3-1/2])/Sqrt[(j1+j2+j3+1)*(-j1+j2+j3)]);

wignerc2[j1_,j2_,j3_,m1_,m2_,m3_]:=
1/Pi/Sqrt[-Det[{{0,(j1+1/2)^2-m1^2,(j2+1/2)^2-m2^2,1},
	            {(j1+1/2)^2-m1^2,0,(j3+1/2)^2-m3^2,1},
	            {(j2+1/2)^2-m2^2,(j3+1/2)^2-m3^2,0,1},
	            {1,1,1,0}}]];

(** Racah and U coefficients **)
racah[a_,b_,c_,d_,e_,f_]:=0/;
(Abs[a-b]-c>0 || a+b-c<0 || Abs[b-d]-f>0 || b+d-f<0 || 
 Abs[a-e]-f>0 || a+e-f<0 || Abs[c-d]-e>0 || c+d-e<0);
racah[a_,b_,c_,d_,e_,f_]:=racahNumeric[a,b,c,d,e,f]/;
NumberQ[a] && NumberQ[b] && NumberQ[c] && NumberQ[d] && NumberQ[e] && NumberQ[f];
racah[a_,b_,c_,d_,e_,f_]:=racahSymbolic[a,b,c,d,e,f];

racahNumeric[a_,b_,c_,d_,e_,f_]:=(*racahNumeric[a,b,c,d,e,f]=*)
Block[{t,tmin,tmax,fac},
      fac=delta[a,b,c]*delta[a,e,f]*delta[b,d,f]*delta[c,d,e];
      fac=Sqrt[fac];
      tmin=Max[a+b+c,a+e+f,b+d+f,c+d+e];
      tmax=Min[a+b+d+e,b+c+e+f,a+c+d+f];
      fac=fac Sum[term[a,b,c,d,e,f,t],{t,tmin,tmax}]];
term[a_,b_,c_,d_,e_,f_,t_]:=
(-1)^t*(t+1)!/((t-a-b-c)!*(t-a-e-f)!*(t-b-d-f)!*(t-c-d-e)!*(a+b+d+e-t)!*(b+c+e+f-t)!*(a+c+d+f-t)!);

racahSymbolic[a_,b_,c_,d_,e_,f_]:=racahSymbolic[b,c,a,e,f,d]/;NumberQ[a] && (!NumberQ[c]||a-c<0);
racahSymbolic[a_,b_,c_,d_,e_,f_]:=racahSymbolic[a,c,b,d,f,e]/;NumberQ[b] && (!NumberQ[c]||b-c<0);
racahSymbolic[a_,b_,c_,d_,e_,f_]:=racahSymbolic[f,b,d,c,e,a]/;NumberQ[d] && (!NumberQ[c]||d-c<0);
racahSymbolic[a_,b_,c_,d_,e_,f_]:=racahSymbolic[a,f,e,d,c,b]/;NumberQ[e] && (!NumberQ[c]||e-c<0);
racahSymbolic[a_,b_,c_,d_,e_,f_]:=racahSymbolic[a,e,f,d,b,c]/;NumberQ[f] && (!NumberQ[c]||f-c<0);
racahSymbolic[a_,b_,c_,d_,e_,f_]:=0/;c<0;
racahSymbolic[a_,b_,c_,d_,e_,f_]:=(-1)^(a+d+f)/Sqrt[(2a+1)*(2d+1)]/;a-b==0 && d-e==0 && c==0;
racahSymbolic[a_,b_,c_,d_,e_,f_]:=0/;(a-b!=0 || d-e!=0) && c==0;
racahSymbolic[a_,b_,c_,d_,e_,f_]:=racahStretched[b,a,c,e,d,f]/;e-c-d==0 && b-a-c==0;
racahSymbolic[a_,b_,c_,d_,e_,f_]:=racahStretched[a,b,c,d,e,f]/;a-b-c==0 && d-c-e==0;
racahStretched[a_,b_,c_,d_,e_,f_]:=
Block[{r,r1,r2,r3,r4},
      r1=(2b)!/(2b+2c+1)!//.reduceFactorial;
      r2=(2e)!/(2c+2e+1)!//.reduceFactorial;
      r3=(-b+c+e+f)!/(-b-c+e+f)!//.reduceFactorial;
      r4=(b+c-e+f)!/(b-c-e+f)!//.reduceFactorial;
      r=(-1)^(b+c+e+f)*Sqrt[r1 r2 r3 r4]];
racahSymbolic[a_,b_,c_,d_,e_,f_]:=racahSymbolic[b,a,c,e,d,f]/;e-c-d==0||a-b-c==0;
racahSymbolic[a_,b_,c_,d_,e_,f_]:=
((-2c Sqrt[(b+d+f+1)*(b+d-f)]*racah[a,b-1/2,c-1/2,d-1/2,e,f]
  +Sqrt[(a+b-c+1)*(a-b+c)*(-c+d+e+1)*(c-d+e)] racah[a,b,c-1,d,e,f])
 /Sqrt[(a+b+c+1)*(-a+b+c)*(c+d+e+1)*(c+d-e)]);

ucoef[a_,b_,e_,d_,c_,f_]:=(-1)^(a+b+e+d)*Sqrt[(2*c+1)*(2*f+1)]*racah[a,b,c,d,e,f];
wcoef[a_,b_,e_,d_,c_,f_]:=(-1)^(a+b+e+d)*racah[a,b,c,d,e,f];

(** Nine-j and X coefficients **)
(* No symbolic calculation *)
ninej[j1_,j2_,j12_,j3_,j4_,j34_,j13_,j24_,j_]:=0/;
(Abs[j1-j2]-j12>0 || j1+j2-j12<0 || Abs[j3-j4]-j34>0 || j3+j4-j34<0 ||
 Abs[j1-j3]-j13>0 || j1+j3-j13<0 || Abs[j2-j4]-j24>0 || j2+j4-j24<0 ||
 Abs[j12-j34]-j>0 || j12+j34-j<0 || Abs[j13-j24]-j>0 || j13+j24-j<0);
ninej[j1_,j2_,j12_,j3_,j4_,j34_,j13_,j24_,j_]:=(*ninej[j1,j2,j12,j3,j4,j34,j13,j24,j]=*)
Block[{t,tmin,tmax},
      tmin=Max[Abs[j1-j],Abs[j2-j34],Abs[j3-j24]];
      tmax=Min[j1+j,j2+j34,j3+j24];
      Sum[(-1)^(2t)*(2t+1)*
          racah[j1,j3,j13,j24,j,t]*
          racah[j2,j4,j24,j3,t,j34]*
          racah[j12,j34,j,t,j1,j2],
          {t,tmin,tmax}]];

xcoef[j1_,j2_,j12_,j3_,j4_,j34_,j13_,j24_,jj_]:=(*xcoef[j1,j2,j12,j3,j4,j34,j13,j24,jj]=*)
Sqrt[(2*j12+1)*(2*j34+1)*(2*j13+1)*(2*j24+1)]*ninej[j1,j2,j12,j3,j4,j34,j13,j24,jj];

(** Twelve-j coefficients of the first and second kind **)
twelvej1[j1_,j2_,j3_,j4_,l1_,l2_,l3_,l4_,k1_,k2_,k3_,k4_]:=0/;
(Abs[j1-j2]-l1>0 || j1+j2-l1<0 || Abs[l1-k1]-k2>0 || l1+k1-k2<0 ||
 Abs[j2-j3]-l2>0 || j2+j3-l2<0 || Abs[l2-k2]-k3>0 || l2+k2-k3<0 ||
 Abs[j3-j4]-l3>0 || j3+j4-l3<0 || Abs[l3-k3]-k4>0 || l3+k3-k4<0 ||
 Abs[j4-l4]-k1>0 || j4+l4-k1<0 || Abs[j1-l4]-k4>0 || j1+l4-k4<0);
twelvej1[j1_,j2_,j3_,j4_,l1_,l2_,l3_,l4_,k1_,k2_,k3_,k4_]:=
(*twelvej1[j1,j2,j3,j4,l1,l2,l3,l4,k1,k2,k3,k4]=*)
Block[{tmin,tmax,r4},
      tmin=Max[Abs[j1-k1],Abs[j2-k2],Abs[j3-k3],Abs[j4-k4]];
      tmax=Min[j1+k1,j2+k2,j3+k3,j4+k4];
	  r4=j1+j2+j3+j4+l1+l2+l3+l4+k1+k2+k3+k4;
      Sum[(-1)^(r4-t)*(2t+1)*
		  racah[j1,k1,t,k2,j2,l1]*
		  racah[j2,k2,t,k3,j3,l2]*
		  racah[j3,k3,t,k4,j4,l3]*
		  racah[j4,k4,t,j1,k1,l4],{t,tmin,tmax}]];

twelvej2[j1_,j2_,j3_,j4_,l1_,l2_,l3_,l4_,k1_,k2_,k3_,k4_]:=0/;
(Abs[j1-j2]-l1>0 || j1+j2-l1<0 || Abs[l1-k1]-k2>0 || l1+k1-k2<0 ||
 Abs[j2-j3]-l2>0 || j2+j3-l2<0 || Abs[l2-k2]-k3>0 || l2+k2-k3<0 ||
 Abs[j3-j4]-l3>0 || j3+j4-l3<0 || Abs[l3-k3]-k4>0 || l3+k3-k4<0 ||
 Abs[j4-l4]-j1>0 || j4+l4-j1<0 || Abs[k1-l4]-k4>0 || k1+l4-k4<0);
twelvej2[j1_,j2_,j3_,j4_,l1_,l2_,l3_,l4_,k1_,k2_,k3_,k4_]:=
(*twelvej2[j1,j2,j3,j4,l1,l2,l3,l4,k1,k2,k3,k4]=*)
Block[{tmin,tmax,r4},
      tmin=Max[Abs[j1-k1],Abs[j2-k2],Abs[j3-k3],Abs[j4-k4]];
      tmax=Min[j1+k1,j2+k2,j3+k3,j4+k4];
	  r4=j1+j2+j3+j4+l1+l2+l3+l4+k1+k2+k3+k4;
      Sum[(-1)^r4*(2t+1)*
		  racah[j1,k1,t,k2,j2,l1]*
		  racah[j2,k2,t,k3,j3,l2]*
		  racah[j3,k3,t,k4,j4,l3]*
		  racah[j4,k4,t,k1,j1,l4],{t,tmin,tmax}]];
twelvej2b[j1_,j2_,j3_,j4_,l1_,l2_,l3_,l4_,k1_,k2_,k3_,k4_]:=
(-1)^(-j1+j2+j3-j4+k1-k2-k3+k4)*twelvej2[k3,j1,k1,j2,l2,l1,l3,l4,k4,j3,k2,j4];

(** Three-n-j coefficients of the first and second kind **)
(* Three arguments are the three rows of the symbol, each an array of length n *)
threenj1[jn_,ln_,kn_]:=
Block[{n,tmin,tmax,rn},
      n=Length[jn];
      tmin=Max[Map[Abs,jn-kn]];
      tmax=Min[jn+kn];
	  rn=Apply[Plus,jn+ln+kn];
      Sum[(-1)^(rn+(n-1)*t)*(2t+1)*
          Product[racah[jn[[i]],kn[[i]],t,kn[[Mod[i,n]+1]],jn[[Mod[i,n]+1]],ln[[i]]],
                  {i,1,n}],
          {t,tmin,tmax}]];
threenj2[jn_,ln_,kn_]:=
Block[{n,tmin,tmax,rn},
      n=Length[jn];
      tmin=Max[Map[Abs,jn-kn]];
      tmax=Min[jn+kn];
	  rn=Apply[Plus,jn+ln+kn];
      Sum[(-1)^(rn+n*t)*(2t+1)*
          Product[racah[jn[[i]],kn[[i]],t,kn[[Mod[i,n]+1]],jn[[Mod[i,n]+1]],ln[[i]]],
                  {i,1,n}],
          {t,tmin,tmax}]];

(* Tests by sum rules *)
(* test6j gives delta(l3a,l3b) *)
test6j[j1_,j2_,l1_,l2_,l3a_,l3b_]:=
(xmin=Max[Abs[j1-j2],Abs[l1-l2]];
 xmax=Min[j1+j2,l1+l2];
 Sum[(2*l3a+1)*(2*x+1)*
	 racah[j1,j2,x,l1,l2,l3a]*
	 racah[j1,j2,x,l1,l2,l3b],{x,xmin,xmax}]);

(* test9j gives delta(k3a,k3b)*delta(l3a,l3b) *)
test9j[j3_,k1_,k2_,k3a_,k3b_,l1_,l2_,l3a_,l3b_]:=
Simplify[Sum[(2*k3a+1)*(2*l3a+1)*(2*x1+1)*(2*x2+1)*
			 ninej[x1,x2,j3,k1,k2,k3a,l1,l2,l3a]*
			 ninej[x1,x2,j3,k1,k2,k3b,l1,l2,l3b],
			 {x1,Abs[k1-l1],k1+l1},{x2,Max[Abs[x1-j3],Abs[k2-l2]],Min[x1+j3,k2+l2]}]];

(* test12j1 gives delta(l1a,l1b)*delta(k2a,k2b)*delta(k3a,k3b) *)
test12j1[j1_,j2_,l1a_,l1b_,l2_,l3_,k1_,k2a_,k2b_,k3a_,k3b_,k4_]:=
Simplify[Sum[(2*l1a+1)*(2*k2a+1)*(2*k3a+1)*(2*x1+1)*(2*x2+1)*(2*x3+1)*
			 twelvej1[j1,j2,x1,x2,l1a,l2,l3,x3,k1,k2a,k3a,k4]*
			 twelvej1[j1,j2,x1,x2,l1b,l2,l3,x3,k1,k2b,k3b,k4],
			 {x1,Abs[j2-l2],j2+l2},{x2,Abs[x1-l3],x1+l3},{x3,Max[Abs[x2-k1],Abs[j1-k4]],Min[x2+k1,j1+k4]}]];

(* test12j2 gives delta(l4a,l4b)*delta(k3a,k3b)*delta(k4a,k4b) *)
test12j2[j1_,j4_,l2_,l3_,l4a_,l4b_,k1_,k2_,k3a_,k3b_,k4a_,k4b_]:=
Simplify[Sum[(2*l4a+1)*(2*k3a+1)*(2*k4a+1)*(2*x1+1)*(2*x2+1)*(2*x3+1)*
			 (-1)^(2*(x2+x3+j1+j4+k1+k2)-k3a-k3b-k4a-k4b)*
			 twelvej2[j1,x2,x3,j4,x1,l2,l3,l4a,k1,k2,k3a,k4a]*
			 twelvej2[j1,x2,x3,j4,x1,l2,l3,l4b,k1,k2,k3b,k4b],
			 {x1,Abs[k1-k2],k1+k2},{x2,Abs[x1-j1],x1+j1},{x3,Max[Abs[x2-l2],Abs[j4-l3]],Min[x2+l2,j4+l3]}]];

reduceSqrt[x_. y_^c1_ z_^c2_]:=x (y z)^c1/;c1==c2;
reduceSqrt[x_. y_^c1_ z_^c2_]:=x (y/z)^c1/;c1==-c2;
reduceSqrt[x_]:=x;
reduceFactorial={
(k_)! k1_ :> (k1)!/;k1==k+1,
(n_)!/(m_)! :>   Product[i,{i,m+1,n}]/;n-m>0&&IntegerQ[n-m],
(n_)!/(m_)! :> 1/Product[i,{i,n+1,m}]/;m-n>0&&IntegerQ[m-n]};
