/ q-math initial commit by dbyu on 2012.05.10

/ least-squares fit, compact version
LSF:{[x;y;z]raze(inv(z+1)#/:(til z+1)_\:sum each x xexp/:til 1+z*2) mmu sum each y*/:x xexp/:til 1+z}

/ least-squares fit, verbose version (works to much higher orders)
LSF2:{[X;Y;n]raze -1#flip{x-(not(til count x)=y)*'((x@til count x)@\:y)*\:x[y;]%:x[y;y]}over((enlist((n+1)#/:(til n+1)_\:sum each X xexp/:til 1+n*2),'sum each Y*/:X xexp/:til 1+n),(til n+1))}

/ fitted list, 2nd arg is list (of coefficients) output by LSF
FL:{sum y*'x xexp/:til count y}

/ levenberg-marquardt nonlinear fit, with 2 test cases
LM:{[x;y;f;df;a]
  params:a;
  lambda:0.001;
  error:1f;
  while[error>0.0001;
    chisq:{sum(x-y)xexp 2}[y;f[x;params]];
    dparams:(inv{x$flip x}[df[x;params]]${`float$0=((x;x)#til(x*x))mod x+1}[count params]*1+lambda)${[x;y;f;fprime;a]sum each(y-f[x;a])*/:fprime[x;a]}[x;y;f;df;params];
    newchisq:{sum(x-y)xexp 2}[y;f[x;params+dparams]];
    $[newchisq>chisq;lambda*:3.0;[lambda%:3.0;params:params+dparams]];
    error:abs(1f-newchisq%chisq)];
  :params
  }

/ LM test case 1
/
X:(-200+til 400)%400
g:{[x;a] a[0]%1+a[1]*x xexp 2}
gprime:{[x;a] ( 1%1+a[1]*x xexp 2;
  (-1)*a[0]*(x xexp 2)%((1+a[1]*(x xexp 2))xexp 2) )}
Y:g[X;(1.33;50.33)]+400?.05
atrial:(25.0;25.0)
t:([] x:X;y:Y;f:g[X;LM[X;Y;g;gprime;(22.2;4.44)]])
LM[X;Y;g;gprime;(22.2;4.44)] / compare to (1.33;50.33). (22.2;4.44) is inital (bad) guess.
\

/ LM test case 2
/
X:(-200+til 400)%400
g:{[x;a] a[0]%1+a[1]*(x-a[2])xexp 2}
gprime:{[x;a] (1%1+a[1]*(x-a[2])xexp 2;
  (-1)*a[0]*((x-a[2])xexp 2)%((1+a[1]*((x-a[2])xexp 2))xexp 2);
  2*a[0]*a[1]*(x-a[2])%((1+a[1]*((x-a[2])xexp 2))xexp 2))}
Y1:g[X;(1.33;50.33;-.234123)]+400?0.2
Y2:g[X;(-4.1;100.2;.3694)]+400?0.2
atrial:(30.33;1.444;.5)
t:([] x:X; y1:Y1; y2:Y2; f1:g[X;LM[X;Y1;g;gprime;atrial]]; f2:g[X;LM[X;Y2;g;gprime;atrial]])
LM[X;Y1;g;gprime;atrial] / compare to (1.33;50.33;-.234123), the original parameters.
\



// Linear algebra routines.

// SLS: solve linear system Ax=b.
// input:square matrix A, list b; output:list x.
SLS:{[A;b]{x*0.0001<abs x}[-1#flip{x-(not(til count x)=y)*'((x@til count x)@\:y)*\:x[y;]%:x[y;y]}over((enlist(A),'b),(til count b))]}
SLS2:{[A;b] (inv A) mmu b} / duh

// QR: QR decomposition of matrix M. 
// input:symmetric matrix M, choice of output T; output is determined by T.
QR:{[M;T]
  Q:`float$M;
  R:Q*0;
  now:0;
  eigenvalues:`float$();
  do[count M;
    eig:sqrt sum Q[;now]*Q[;now];
    Q[;now]:Q[;now]%sqrt sum Q[;now]*Q[;now];
    pivot:Q[;til now+1];
    R[now;]:(sum Q[;now]*Q)%sqrt sum Q[;now]*Q[;now];
    Q:Q-Q[;now]*\:R[now;];
    Q[;til now+1]:pivot;
    R[now;now]:eig;
    eigenvalues:eigenvalues,eig;
    now:now+1;
    ];
  : $[T=`A;R mmu Q;$[T=`E;eigenvalues;$[T=`R;R;$[T=`Q;Q;0]]]]
  }

// ID: identity matrix rank n. 
// input: rank n; output: identity matrix.
ID:{[n]`float$0=((n;n)#til(n*n))mod n+1}

// OP: outer product of vector with itself. 
// input: vector v; output: matrix of rank n (n*n values in symmetric matrix).
OP:{[v]`float$v*/:v}

// HH: Householder transformation.
// inputs: symmetric matrix; output: tridiagonal form.
HH:{[M]
  A:`float$M;
  now:0;
  do[-2+count M;
    x:A[now;];
    s:(signum x[1+now])*sqrt sum((now+1)_A[now;])*((now+1)_A[now;]);
    v:(`float$((now+1)?1),(x[now+1]+s),(now+2-count x)#x)%(sqrt 2*s*s+x[now+1]);
    Q:(ID count x)-2*(OP v);
    now:now+1;
    A:Q mmu A mmu Q
    ];
  :A
  }

// GJE:Gauss-Jordan elimination. 
// input: matrix A, index n; output: matrix. (n can be null int, 0N).
GJE:{$[not y=0N;x-(not(til count x)=y)*'((x@til count x)@\:y)*\:x[y;]%:x[y;y];x]}


/ numerical recipes in c, ch 14 statistical functions, getting off ground ..
adev:{(sum abs x - avg x)%count x}
skew:{(sum ((x-avg x)%(dev x)) xexp 3)%count x}
kurt:{((sum ((x - avg x)%(dev x)) xexp 4)%count x)-3}
stderr:{[x;y] sqrt((1%count x)+(1%count y))*((sum(x-avg x)xexp 2)+(sum(y-avg y)xexp 2))%((count x)+(count y)-2)}
ttest:{[x;y] ((avg x)-avg y)%stderr[x;y]}
tutest:{[x;y] ((avg x)-avg y)%sqrt(((var x)%count x)+(var y)%count y)}
tptest:{[x;y] ((avg x)-avg y)%sqrt(((var x)+(var y)-2*cov[x;y])%count x)}
gamma:{[z;a]((z+a-1)xexp(z-0.5))*(exp(-1*a+z-1))*((sqrt(2*3.1415926535))+sum({[k;b]((-1)xexp(k-1))*((b-k)xexp(k-0.5))*(exp(b-k))%({(*) over 1+til x}[k-1])}[;a] each 1+til a-1) %' z+til a-1)}
beta:{gamma[x;6]*gamma[y;6]%gamma[x+y;6]}

/ added S.Plouffe's BBP base digit extraction algorithm for computing pi (1995).
/ arg is # of terms to use, can be used to arbitrary precision. for \P 12, pi[8]
/ is good enough:
pi:{sum(1%16 xexp til x)*'{[k](4%(1+8*k))-(2%(4+8*k))+(1%(5+8*k))+(1%(6+8*k))}[til x]}