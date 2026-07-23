(* ::Package:: *)

(* Normalised eigenvectors; eigenvalues ordered *)
eigensystem[m_]:=
Block[{eig,eigval,eigvec,i,j,x,y},
eig=Eigensystem[m];
eigval=Chop[eig[[1]]];
eigvec=Chop[eig[[2]]];
Do[eigvec[[i]]=Chop[eigvec[[i]]/Sqrt[eigvec[[i]] . eigvec[[i]]]],{i,1,Length[m]}];
Do[Do[If[eigval[[i]]>eigval[[i+1]],
         x=eigval[[i]];eigval[[i]]=eigval[[i+1]];eigval[[i+1]]=x;
         y=eigvec[[i]];eigvec[[i]]=eigvec[[i+1]];eigvec[[i+1]]=y,Null],
      {i,1,Length[m]-1}],
   {j,1,Length[m]}];
{eigval,eigvec}];
eigenvalues[m_]:=eigensystem[m][[1]];

(* Normalised eigenvectors *)
eigensystem2[m_]:=
Block[{eig,eigval,eigvec,i,j,x,y},
eig=Eigensystem[m];
eigval=Chop[eig[[1]]];
eigvec=Chop[eig[[2]]];
Do[eigvec[[i]]=Chop[eigvec[[i]]/Sqrt[eigvec[[i]] . eigvec[[i]]]],{i,1,Length[m]}];
{eigval,eigvec}];

(* Diagonalisation in a non-orthogonal basis *)
(* hm is the hamiltonian matrix; om is the overlap matrix *)
(* Version 1: returns wave functions in orthogonalised basis *)
eigensystem[hm_,om_]:=
Block[{eom,eomval,eomvec,ho},
eom=Chop[eigensystem[om]];
eomval=eom[[1]];
eomvec=eom[[2]]/Sqrt[eomval];
ho=Chop[eomvec . hm . Transpose[eomvec]];
eigensystem[ho]];
      
(* Version 2: returns wave functions in original (non-orthogonal) basis *)
eigensystem2[hm_,om_]:=
Block[{eom,eomval,eomvec,ho,eh},
eom=Chop[eigensystem2[om]];
eomval=eom[[1]];
eomvec=eom[[2]]/Sqrt[eomval];
ho=Chop[eomvec . hm . Transpose[eomvec]];
eh=eigensystem[ho];
{eh[[1]],eh[[2]] . eomvec}];

(* Convert Hamiltonian to square matrix *)
sqh[h_]:=
Block[{d},
d=(Sqrt[8*Length[h]+1]-1)/2;
Table[If[i<=k,h[[(2*d-i)*(i-1)/2+k]],h[[(2*d-k)*(k-1)/2+i]]],
      {i,1,d},{k,1,d}]];
sqh[h_,ev_]:=
Block[{d},
d=(Sqrt[8*Length[h]+1]-1)/2;
Table[If[i<=k,N[h[[(2*d-i)*(i-1)/2+k]]/.ev],N[h[[(2*d-k)*(k-1)/2+i]]/.ev]],
      {i,1,d},{k,1,d}]];
