# A Turán inequality sufficient for the full conjecture

Let $P_{k,i}$ denote the internal-descent normalization of the Jacobi–Stirling polynomial. Use the transformed row
```math
 h_{k,i}(x)=(1+x)^{2k-i} P_{k,i}\left(\frac{x}{1+x}\right),\qquad
 D_j f=(1+jx)f+x(1+x)f'.
```
The insertion recurrence gives $h_{k,i}=D_k(D_k h_{k-1,i}+h_{k-1,i-1})$, with entries outside the row equal to zero and $h_{0,0}=1$. For $k\ge1$ all entries have a factor $1+x$. Write $f_{k,i}=h_{k,i}/(1+x)$. The first row is $1+2x,1$. Since $D_k((1+x)f)=(1+x)D_{k+1}f$, subsequent rows obey
```math
 f_{k,i}=D_{k+1}\bigl(D_{k+1}f_{k-1,i}+f_{k-1,i-1}\bigr).
```
The degree of $f_{k,i}$ is $2k-i-1$, with positive leading coefficient. This follows from the first row and the fact that $D_j$ raises the degree of a polynomial of positive leading coefficient by one when $j>0$. [Insertion operators and normalization](https://arxiv.org/html/2610.03111v1#S4) · [Earlier transformed recurrence](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/campaign-20261121/gessel-lin-zeng-followup.md)

**Conditional reduction.** Suppose the aggregate rows satisfy the following inequalities for every $k\ge1$, $1\le i<k$, and $-1<x<0$:
```math
 T_{k,i}(x)=f_{k,i}(x)^2-f_{k,i-1}(x)f_{k,i+1}(x)\ \ge\ 0 .
```
Then every $f_{k,i}$ has only simple roots in $(-1,0)$ and consecutive polynomials in each row strictly interlace. In particular every original numerator satisfies Conjecture 15. The inequality concerns only the equal-weight aggregate. It can hold even when a polynomial formed by summing over the deletion index has nonreal roots.

## Proof of the reduction

Proceed by induction on the row. The first row has the asserted properties. In one subsequent step write $f_i$ for the old row and set $g_i=D_j f_i+f_{i-1}$, with $j=k+1>1$ and zero entries outside the old row. Put $s=x(1+x)$. For an old entry $f_i$ with simple zeros $\rho$, the rational function $g_i/f_i$ is the sum of
```math
 1+jx+\sum_{\rho}\frac{s}{x-\rho}
 \quad\text{and}\quad \frac{f_{i-1}}{f_i}.
```
By strict interlacing and positive leading coefficients, the second term has positive linear slope and negative residues at the zeros of $f_i$ when $i>0$. For $i=0$ it vanishes. Each summand $s/(x-\rho)$ has linear slope one and residue $\rho(1+\rho)<0$. Thus $g_i/f_i$ is strictly increasing between poles, tending to positive infinity on the left of each pole and negative infinity on its right. Its value at $-1$ is negative and its value at zero is positive, by the endpoint signs of the two old polynomials. Each pole-free interval inside $[-1,0]$ therefore contains one simple zero of $g_i$, so $f_i$ strictly interlaces $g_i$. At the new last index $g_i$ is the old final entry.

For consecutive old entries define $W_i=f_i'f_{i+1}-f_i f_{i+1}'$. Strict interlacing implies $W_i>0$ on the real line. Away from the zeros of $f_{i+1}$, divide by $f_{i+1}^2$ and differentiate the partial fractions of $f_i/f_{i+1}$. At each pole the negative residue gives strict positivity by taking the limit after multiplying by $f_{i+1}^2$. Direct expansion gives
```math
 g_i f_{i+1}-g_{i+1} f_i=sW_i-T_{k-1,i}.
```
For $i=0$ the final term is $f_0^2$. At every zero of $g_{i+1}$ the right side is strictly negative. Hence $g_i$ and $f_{i+1}$ have opposite signs there. Since $f_{i+1}$ strictly interlaces $g_{i+1}$, the signs alternate. The positive leading coefficient of $g_i$ and its endpoint signs give one zero of $g_i$ on each outer side as well. More explicitly, at the largest zero of $g_{i+1}$ the sign of $g_i$ is negative, whereas $g_i(0)>0$. At the smallest zero its sign is opposite to $g_i(-1)$ by the same degree count. This proves strict interlacing of $g_i,g_{i+1}$. For the last pair this already follows from the old final entry interlacing its $g_i$.

Applying $D_j$ to all the $g_i$ preserves their strict interlacing. To see this, use the same pole argument with the previous-row summand omitted. The determinant comparison becomes $(D_j g_i)g_{i+1}-(D_j g_{i+1})g_i=s(g_i'g_{i+1}-g_i g_{i+1}')<0$. Thus the whole next row has the required roots and interlacing. Finally $x\mapsto x/(1+x)$ sends $(-1,0)$ bijectively to the negative real axis. The quotient removed the padding root $-1$; restoring the source's terminal-descent factor restores a real root at zero. The source convention at $k=0$ gives the constant polynomial one.

## Remaining step

A proof of $T_{k,i}\ge0$ for all rows would close the induction. The determinant identity also permits a weaker sufficient condition, as its sign is needed only at the zeros of $g_{i+1}$. Neither sign condition has been established in general here.

## Real zeros for a continuous deletion weight

The generating polynomial $H_k(x,u)=\sum_i h_{k,i}(x)u^i$ obeys $H_k=D_k(D_k+u)H_{k-1}$. For each $-1<u<0$ and each $k\ge1$, it has one simple root at $-1$ and all other roots simple in $(-1,0)$. The interior roots move strictly to the left as $u$ increases. This assertion treats the whole deletion-marker polynomial at once, but does not by itself control all its coefficients.

Here is the root-motion argument. An insertion $D_j+v$, with $v=u$ or $v=0$, has secular equation away from the input roots
```math
 R(x,u)=1+jx+v+\sum_{\rho}\frac{x(1+x)}{x-\rho(u)}=0 .
```
With interior input roots, the residues are strictly negative and the slope on every gap is strictly positive. An input root at $-1$ contributes the regular term $x$; the output keeps that simple root whenever $R(-1,u)\ne0$. Begin with $D_1+u$ applied to one. Its single root $-1-u$ lies in the interval and has derivative $-1$. The subsequent $D_1$ inserts the fixed root $-1$ because $R(-1,u)=0$ before that root is present; the slope there is strictly positive. At every later insertion $R(-1,u)=1-j+v-1<0$ and $R(0,u)=1+v>0$, so the fixed root remains simple and each interior root gap produces one new simple zero.

At an interior output root the derivative of $R$ with respect to $u$ at fixed $x$ is
```math
 \frac{\partial v}{\partial u}+\sum_{\rho}
 \frac{x(1+x)\rho'(u)}{(x-\rho(u))^2}.
```
Each term is nonnegative when all interior roots move left. After the initial insertion there is always a strictly moving root, so the sum is strictly positive. Implicit differentiation and $R_x>0$ now give strict leftward motion at every interior output root. This proves the assertion by induction.

After removing $1+x$, the leading coefficient in $x$ is independent of $u$. At a zero of the resulting polynomial $F$, its partial derivative $F_u$ equals $-F_x\rho'(u)$. The alternating signs at the roots show that $F_u$ strictly interlaces $F$ whenever the derivative has positive degree, with the constant case at the first step. Passing to higher $u$-derivatives requires further control of the root motion of $F_u$.

## A restriction on the binomially weighted stability approach

One might weight column $i$ by $\binom{k}{i}$ and try to prove that insertion preserves real stability for every bivariate input. That operator fails even after specializing $x=0$. At that point $D_k$ acts by evaluation on the constant term in $x$. If the weighted input in row three is the stable polynomial $(1+y)^3$, its unweighted coefficients are all one. Ordinary insertion adds neighboring coefficients, and the row-four binomial weights give
```math
  1+8y+12y^2+8y^3+y^4.
```
Dividing by $y^2$ and setting $v=y+y^{-1}$ yields $v^2+8v+10$. One root is $-4+\sqrt{6}$, strictly between $-2$ and $2$. Its two preimages are nonreal, so this output fails real-rootedness. This input is an example for the abstract operator. The actual row-three input has different coefficients, and the binomially weighted stability question on the actual trajectory remains open.
