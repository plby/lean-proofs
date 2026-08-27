# Independent reconstruction of the log-log bound for Erdős 587

Proof, 2026-08-27. This is **not** the unavailable CFP manuscript and
does not change the completed logarithmic proof in `../587.tex` or its Lean
formalization. Let \(\Sigma(A)\) be the set of sums of subsets of \(A\),
including the empty sum, and let \(\operatorname{SF}(N)\) be the largest
size of a subset of \(\{1,\ldots,N\}\) whose subset sums contain no
positive square. We prove

\[
 \operatorname{SF}(N)\ll N^{1/3}(\operatorname{Log}_2N)^C,
 \qquad \operatorname{Log}x=\max(1,\log x),\quad
 \operatorname{Log}_2x=\operatorname{Log}(\operatorname{Log}x).
\]

**Theorem.** There are absolute constants \(C_*,N_0\) such that
\(\operatorname{SF}(N)\le C_*N^{1/3}(\operatorname{Log}_2N)^{16}\)
for every integer \(N\ge N_0\).

**Lean status: complete.** `Erdos587.unconditional_loglog_upper_bound` in
`src/latest/ErdosProblems/Erdos587/HooleyUpperBound.lean` proves this bound
unconditionally and is imported by the main `ErdosProblems.Erdos587` module.
Section 11 records the independently proved analytic and geometric route;
it uses a weaker sufficient harmonic Delta estimate instead of assuming
the sharper published mean. Sections 1–10 retain the original informal
reconstruction and its provenance. Their finite tests are not used as
evidence for an analytic inequality or as assumptions of the Lean proof.

## Inputs and provenance

- Koukoulopoulos–Tao, [Theorem 1](https://arxiv.org/html/2306.08615v4):
  \(\sum_{n\le X}\Delta(n)\ll X(\operatorname{Log}_2X)^{11/4}\).
  Write the exponent as \(c_0\) below. This published input gives
  \(c_0=11/4\); the independent unconditional Lean development in §11
  instead proves a sufficient harmonic bound with \(c_0=5\).
- Nair–Tenenbaum, [*Short sums of certain arithmetic functions*, Theorem 1,
  p. 6](https://tenenb.perso.math.cnrs.fr/PPP/ShortSums.pdf), applied only to
  primitive linear polynomials. This is an additional published input: the
  global Delta mean alone does not imply a short-progression mean.
- Conlon–Fox–Pham, [*Homogeneous structures in subset sums and non-averaging sets*
  (author PDF)](https://www.its.caltech.edu/~dconlon/subset_sums_highdim.pdf).
  We use its resilient seed theorem and iterated-sumset lower bound,
  together with the standard convex-geometric results used there. Local
  source labels are `thm:hom-AP-build2`, `lem:lower-hA`,
  `lem:zonotope-volume`, and `lem:TV-convexbody`.
- The classical [Burgess character-sum bound, with parameter 2](https://arxiv.org/pdf/1203.5219v2)
  and the [van der Corput second derivative test](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf).
  Section 10 below derives the root-density and small-step facts needed
  from these inputs. The common-factor reduction is proved in Section 8.

All constants depending on a fixed ambient dimension or a fixed positive
power separation are harmless. Write \(D_c(X)=(\operatorname{Log}_2X)^c\).
We use \(e(t)=\exp(2\pi i t)\), \(\tau(n)=\#\{d>0:d\mid n\}\),
and the Fourier transform \(\widehat w(\xi)=\int w(t)e(-t\xi)\,dt\).
The Delta function is
\(\Delta(n)=\sup_{u\in\mathbb R}\#\{d>0:d\mid n,\ e^u<d\le e^{u+1}\}\).
In particular, divisors in any interval \((D,2D]\) number at most
\(\Delta(n)\), since \(2<e\).
A bounded Schwartz family means that each fixed Schwartz seminorm is
bounded uniformly in the indexing parameters. Only finitely many such
seminorms are needed in any particular estimate.

## 1. A full-width structural extraction through convex quotients

### 1.1 Statement

There are absolute positive constants \(c,C,C_1\) such that, if
\(A\subset[1,N]\), \(|A|=m\ge C N^{1/3}\), then \(\Sigma(A)\) contains a
proper homogeneous GAP \(Q\) of rank \(r\in\{1,2\}\) satisfying

\[
 \min_i\operatorname{width}_i Q\ge cm,\qquad
 |Q|\ge cm^{r+1},\qquad
 \max Q\le mN,\qquad \max Q\le C_1\operatorname{diam} Q.
 \tag{S}
\]

The convention for widths (number of coefficient values versus their
difference) only changes constants. A translate is homogeneous if its base
point is divisible by the gcd of its steps.

### 1.2 Seed and convex body

Put \(n=N+1\), take the CFP parameters \(\beta=6\), \(\eta=1/2\),
and resilience parameter \(\epsilon_0=1/100\), and let
\(s=\lfloor m/(\log m)^2\rfloor\). For sufficiently large \(m\),
\(n\le s^6\) and \(m^{1/2}\le s\le c m/\log m\). Apply the resilient
seed theorem. Center its coordinate box at zero, and then symmetrize it.
A translate of a symmetric box with radii comparable to the original
widths fits inside the original dilated seed box. Thus, after changing
fixed constants, the output is:

1. \(\widehat A\subset A\), \(|\widehat A|\ge c m\), in a symmetric
   coordinate GAP \(P=\psi(\prod[-L_i,L_i]\cap\mathbb Z^d)\), with \(d\)
   bounded absolutely, \(L_i\ge1\), and \(\psi:\mathbb Z^d\to\mathbb Z\).
2. A seed \(A'\subset\widehat A\), \(|A'|\le s\), whose subset sums contain
   a homogeneous translate \(t_0+\psi(Q')\) of a symmetric box with
   coordinate radii \(\gg sL_i\).
3. \(\widehat A\) is \((\epsilon_0,6)\)-resilient in CFP's terminology:
   for every \(V\subseteq\widehat A\) of size at least
   \(|\widehat A|/100\), and every integer \(j\le7\),
   \(\operatorname{Vol}P_j(V\cup\{0\})\ge
   n^{-\epsilon_0}\operatorname{Vol}P_j(\widehat A\cup\{0\})\).

Here \(P_j(D)\) denotes a minimum-volume \(j\)-dimensional GAP containing
\(D\). To make the coordinate normalization precise, use the representation
of 0 to remove the base point of the original GAP. Its coefficient
intervals now contain 0; their widths are comparable to
\(L_i=\max(|a_i|,|b_i|)\). A centered symmetric box of radii
\(\gg sL_i\) fits, after integer translation, inside the seed's coordinate
box. It is proper there, and contains the symmetrized box for large \(s\).
The translated center is a seed subset sum, hence belongs to
\(\psi(\mathbb Z^d)\). Zero-width coordinates may be omitted. This
also verifies homogeneity after normalization, without changing lattices.

**Robust linear spanning follows directly.** For such a \(V\), let \(j\)
be the \(s\)-dimension of \(V\cup\{0\}\). The published iterated-sumset
lower bound, whose hypothesis is \(n\le s^6\), gives \(j\le7\) and

\[
 |s(V\cup\{0\})|
 \gg s^j\operatorname{Vol}P_j(V\cup\{0\})
 \ge n^{-\epsilon_0}s^j\operatorname{Vol}P_j(\widehat A\cup\{0\})
 \ge n^{-\epsilon_0}|s(\widehat A\cup\{0\})|.                       \tag{S1}
\]

The last inequality just counts coefficient vectors in a dilated GAP;
that GAP need not be proper. Since \(|A'|\le s\), the proper seed box
also gives \(|s(\widehat A\cup\{0\})|\gg s^d|P|\). If the coordinate
copy of \(V\) lay in a proper linear subspace \(\Gamma\), choose an
original coordinate direction not in \(\Gamma\). Each line parallel
to that direction meets \(\Gamma\) at most once. Counting the other
coordinates in \(sP\) gives
\(|s(V\cup\{0\})|\ll_d s^{d-1}|P|\), contradicting (S1), because
\(s n^{-\epsilon_0}\to\infty\). Thus every such \(V\) spans
\(\mathbb R^d\) **linearly**. Affine spanning is neither asserted nor
needed. Choosing \(\beta=6\), rather than 3, avoids any borderline
issue in the condition \(n\le s^\beta\).

Delete the seed. Choose a basis from the parity vectors of the remaining
elements over \(\mathbb F_2\), express their total sum in that basis,
and delete the at most \(d\) basis elements used in that expression.
The coordinate sum of the surviving set \(U\) is even. Then
\(|U|\ge|\widehat A|/2\gg m\) for large \(m\), and every subset
of \(U\) of size at least \(|U|/10\) still has full linear dimension.
Let

\[
 Z=\sum_{u\in U}[-u/2,u/2],\qquad B=Z+\gamma\operatorname{conv}(Q')
\]

for a fixed small \(\gamma>0\). The following elementary rounding fact
is useful: any point \(\sum_{u\in U}\alpha_u u\), \(0\le\alpha_u\le1\),
is within coordinate error \(dL_i\) of a subset sum. To prove it, while
more than \(d\) coefficients are fractional, move them along a linear
dependence, preserving the vector sum, until another coefficient reaches
0 or 1. Finally round the at most \(d\) fractional coefficients.
This error is absorbed by the unused part of \(Q'\), since its radii
are \(\gg sL_i\). Consequently

\[
 \psi(z_0+(B\cap\mathbb Z^d))\subseteq\Sigma(\widehat A)               \tag{1}
\]

for an integer vector \(z_0\). Here the zonotope center is integral, and
homogeneity of the seed supplies an integer lift of \(t_0\).
The body \(B\) contains \(c s F\), where
\(F=[-1/2,1/2]^d\) is a rounding cell, as well as \(Z\).

### 1.3 Exact lattice-point lifting

Let \(\Lambda\) be a lattice in its real span, \(B\) a symmetric convex
body, and \(\psi:\Lambda\to\mathbb Z\) a homomorphism. Fix \(0<\eta<1/4\).
Suppose a primitive vector \(v\in\Lambda\cap\ker\psi\) lies in \(\eta B\).
Let \(\pi\) be quotient by \(\mathbb Rv\), let
\(\Lambda'=\pi(\Lambda)\), and set \(B'=(1-\eta)\pi(B)\).
The lattice \(\Lambda'\) has rank one less: primitivity makes
\(\Lambda/\mathbb Zv\) torsion-free.

Every \(y\in B'\cap\Lambda'\) has a lattice lift in \(B\). Indeed, choose
a real lift \(x\in(1-\eta)B\) and a lattice lift \(x_0\). Their difference
is \(tv\). Subtract a nearest integer multiple of \(v\) from \(x_0\);
the resulting lattice point differs from \(x\) by at most \(v/2\), and so
lies in \((1-\eta)B+(\eta/2)B\subset B\). Therefore

\[
 \psi'(B'\cap\Lambda')\subseteq\psi(B\cap\Lambda).                    \tag{2}
\]

The integer center projects too. Repeat this operation whenever a nonzero
kernel vector lies in \(\eta B\), replacing it first by its primitive
part. There are at most \(d-1\) operations, since \(\psi\ne0\).
At the end \(\psi\) is injective on \((\eta/2)B\cap\Lambda\).
All shrinkages are bounded-dimensional constant factors.

At every stage, the projected elements of \(U\) are distinct: equal
projections would imply equal original integer values under \(\psi\).
Their robust linear spanning property also survives, because the inverse
image of a proper linear subspace under a surjective linear map is proper.
The final body contains constant multiples of the projected \(Z\) and of
\(sF\), with \(F\) now the projected original cube.

### 1.4 Rounding, a lattice basis, and all long sides

The projected cube remains a rounding cell: lift any real point to the
original space and round its coordinates. Thus every point is within \(F\)
of a point of the quotient lattice, even if the shape of \(F\) is badly
conditioned.

If a symmetric body \(C\) contains \(s_1F\), rounding a support point of
\((1-1/s_1)C\) gives a lattice point of \(C\). For every linear functional
\(\ell\), the loss is at most \(h_F(\ell)\le h_C(\ell)/s_1\). Hence

\[
 \operatorname{conv}(C\cap\Lambda)\supseteq(1-2/s_1)C.                \tag{3}
\]

Apply discrete John to a sufficiently small fixed multiple \(C\) of the
final body, so that its lattice-point image is injective. It supplies a
coordinate progression \(P_0\) generated by independent \(w_1,\ldots,w_r\)
with

\[
 c_r C\cap\Lambda\subseteq P_0\subseteq C\cap\Lambda.                \tag{4}
\]

The generators actually form a basis of the whole quotient lattice. Each
projected original basis vector lies in \(c_r C\) for large \(s\), and these
vectors generate \(\Lambda\). Inclusion (4) puts them in the subgroup
generated by the \(w_i\). Independence now proves the basis assertion.
This step must not be replaced by the false general assertion that any
independent integer vectors form a lattice basis.

Equations (3)–(4) imply \(\operatorname{conv}(P_0)\supset cB\). For each
dual basis coordinate \(\ell_i\), robust spanning of the projected \(U\)
implies that at least \(c m\) elements have \(\ell_i(u)\ne0\). These values
are integers, so the width of its zonotope in this direction is at least
\(cm\). Thus every coefficient width of \(P_0\) is at least \(cm\).

For completeness, here is the zonotope-volume argument relative to
\(\Lambda\). Any \(k\) distinct lattice points spanning linearly, together
with the origin, have a convex hull of volume \(\gg_r k\), by the lattice
polytope volume bound. A maximum-volume simplex on those points has volume
\(\gg_r k\): its barycentric coordinates bound the hull inside a fixed
dimensional dilation of that simplex. This argument needs affine spanning
only **after adjoining the origin**, which linear spanning supplies.

Repeatedly remove the nonzero vertices of such a simplex. Robust spanning
allows \(\gg m\) disjoint batches, each chosen while \(\gg m\) points
remain; each simplex has volume \(\gg m\). Their Minkowski sum lies in
the zonotope. Brunn–Minkowski gives its volume at least
\((c m\,(c m)^{1/r})^r\gg m^{r+1}\).
Together with (3)–(4), this gives
\(|P_0|\gg m^{r+1}\): in its lattice basis, the number of points of
the coefficient box is at least its real volume. The final image is
proper by construction.
Its integer translation lies in \(\psi(\Lambda)\), and the final steps
generate \(\psi(\Lambda)\), proving homogeneity.

### 1.5 Height, span, and rank

All subset sums used lie in \([0,\sum\widehat A]\subset[0,mN]\).
The image width of the original body is at least a fixed multiple of

\[
 \sum_{u\in U}\psi(u)+s\operatorname{diam}(P).
\]

The omitted seed and parity elements contribute at most
\((s+d+1)\operatorname{diam}(P)\), since \(0\in P\).
Quotienting by the kernel preserves image width, except for the fixed
shrinkages, and (3)–(4) preserve a fixed fraction afterwards. Hence
\(\operatorname{diam}Q\gg\sum\widehat A\ge\max Q\).

Finally, \(cm^{r+1}\le|Q|\le mN+1\). If \(m\ge C N^{1/3}\) with \(C\)
large enough, this excludes \(r\ge3\). Rank zero is impossible because
\(\psi\ne0\). This proves the structural statement (S).

## 2. Delta means in short linear progressions

The following describes the original literature-based route. The Lean
proof now establishes its needed weaker-exponent version directly from
the harmonic Delta mean and a finite large-sieve argument; see §11.9.
That checked version also permits a zero affine value, since \(\Delta(0)=0\).

For fixed \(\kappa>0\), suppose \(I\) consists of \(Y\ge X^\kappa\)
consecutive integers, \(B\ne0\), and \(0<|A+Bt|\le X\) on \(I\).
The consequence of Nair–Tenenbaum and KT that we need is

\[
 \sum_{t\in I}\Delta(|A+Bt|)
 \ll_\kappa \tau((A,B))\,Y D_{c_0+1}(X).                              \tag{5}
\]

First suppose \((A,B)=1\). Reindex \(I\) as \(Y<j\le2Y\), with
integer \(Y\). The resulting linear polynomial has coefficients \(O(X)\):
its slope has absolute value at most \(2X/(Y-1)\), and recentering changes
its constant term by at most \(O(Y|B|)\). In Nair–Tenenbaum's Theorem 1,
take \(x=y=Y\), the degree and the number of factors both equal to 1,
the short-interval parameter \(1/16\), and the coefficient-size parameter
\(\delta=\min(\kappa/4,1/4)\). The condition
\(x>c_0\|Q\|^\delta\) holds for large \(X\), since \(Y\ge X^\kappa\);
the condition \(x^{1/4}\le y\le x\) is immediate.

The polynomial is primitive, so it has no fixed prime divisor. Its
discriminant is 1, and its root-count function is
\(\rho(n)=1_{(n,B)=1}\). Thus the theorem's constant has no hidden
dependence on the slope or constant term. Its function-class condition
holds because \(\Delta(ab)\le\tau(a)\Delta(b)\) and
\(\tau(a)\ll_\epsilon a^\epsilon\) for every fixed positive \(\epsilon\).
It gives

\[
 \sum_{t\in I}\Delta(|A+Bt|)
 \ll Y\prod_{p\le Y,\ p\nmid B}(1-1/p)
          \sum_{n\le Y}{\Delta(n)\over n}.
\]

Partial summation of KT bounds the last sum by
\(\operatorname{Log}Y D_{c_0}(Y)\). Mertens' product bound cancels
\(\operatorname{Log}Y\), leaving at most the factor
\(|B|/\varphi(|B|)\ll\operatorname{Log}_2X\). This proves the primitive
case. Divide the polynomial by \((A,B)\) for the general case, and use
the same value bound \(X\). The divisor bound used here holds even
without coprimality: map a divisor \(d\mid ab\) to
\((\gcd(d,a),d/\gcd(d,a))\), and group by its first coordinate.
Rounding and bounded \(X\) only change the constant. The interval must
avoid an integral zero of the polynomial.

We will repeatedly use the elementary Euler-factor estimates
\(q/\varphi(q)\ll\operatorname{Log}_2q\) and
\(\sum_{d\mid q}d^{-1}\le q/\varphi(q)\). For example, split the
prime factors at \(\log q\). Mertens bounds the product for the smaller
primes by \(O(\operatorname{Log}_2q)\). There are at most
\(\log q/\log\log q\) larger prime factors, whose Euler factors have
bounded product. Small \(q\) are absorbed by the modified logarithms.

## 3. A smooth major-arc estimate

Let \(w\) vary in a bounded Schwartz family, \(K\ge2\), \((h,b)=1\),
\(1\le b\le K\), and \(|\beta|\le1/(bK)\). Uniformly in real \(\theta\),

\[
 \left|\sum_j w(j/K)e((h/b+\beta)j^2+\theta j)\right|^2
 \ll_w {K^2\over b(1+K^2|\beta|)}.                                  \tag{6}
\]

For \(G(h,k;b)=\sum_{s\bmod b}e((hs^2+ks)/b)\), finite Fourier
inversion and Poisson give the exact identity

\[
 \sum_j w(j/K)e((h/b+\beta)j^2+\theta j)
 ={K\over b}\sum_{\ell\in\mathbb Z}G(h,\ell;b)
       \widehat W\bigl(K(\ell/b-\theta)\bigr),\qquad
 W(t)=w(t)e(\beta K^2t^2).
\]

The complete Gauss coefficients have magnitude at most \(\sqrt{2b}\).
Writing
\(A=K^2|\beta|\), the Fourier transform of the smooth chirped weight has
the uniform stationary-phase envelope

\[
 C(1+A)^{-1/2}(1+|\xi|/(1+A))^{-2}.
\]

For any translate of a lattice of spacing \(s\), the sum of
\((1+|\xi|/H)^{-2}\) is \(O(1+H/s)\), uniformly in the translate.
Here \(s=K/b\), \(H=1+A\), and \(H/s\le2\). Multiplying this bound
by \(K/\sqrt b\) proves (6). One exact way to
justify the envelope for \(A\ge1\) is the Fresnel identity: the transform
is a factor of modulus \((2A)^{-1/2}\), times a quadratic phase, times
\(\Psi_A(\pm\xi/(2A))\), where \(\Psi_A\) is the inverse transform of
\(\widehat w(\zeta)e(\mp\zeta^2/(4A))\). This family is uniformly
Schwartz. For \(A\le1\) the original chirped weights are uniformly
Schwartz directly. A fixed constant in the major-arc width changes only
the implied constant in (6).

## 4. Centered quadratic mean: the power-separated modulus range

Let \(M,q\ge1\) be integers, \(L\ge2\), \((a,q)=1\), and
\(X\ge16(q+ML+2)\). Set

\[
 S_m=\sum_z w_m(z/L)e(amz^2/q),\qquad
 B_m={G(am;q)\over q}\int_{\mathbb R}w_m(z/L)\,dz,
\]

for a uniformly Schwartz family \(w_m\). If
\(q\le ML X^{-\kappa}\), then

\[
 \sum_{m\le M}|S_m-B_m|^2\ll_\kappa ML D_{c_0+2}(X).                 \tag{7}
\]

Here and below constants in choosing \(X\) or fixed exponents can be
absorbed by slightly reducing \(\kappa\).

For reduced denominator \(Q=q/(m,q)\le L\), smooth Poisson completion
and the Gauss bound give

\[
 |S_m-B_m|\ll_A {L\over\sqrt Q}
       \sum_{\ell\ne0}(1+|\ell|L/Q)^{-A}
 \ll_A {L\over\sqrt Q}(Q/L)^A\ll\sqrt L
\]

on taking \(A\ge2\). For \(Q>L\), the retained term is itself
\(O(L/\sqrt Q)=O(\sqrt L)\). It remains to bound \(|S_m|^2\) for
these indices. Choose one reduced Dirichlet approximant \(h/b\),
\(b\le\lfloor L\rfloor\), with
\(|am/q-h/b|\le2/(bL)\). The error is nonzero because the exact reduced
denominator exceeds \(L\). The constant 2 is allowed in (6).

Group \(b\) into dyadic blocks \(B<b\le2B\), starting with \(B=1/2\)
to include \(b=1\). Use the shell \(|am/q-h/b|\le L^{-2}\), and then
the shells \(\delta/2<|am/q-h/b|\le\delta\), for
\(\delta=2^jL^{-2}\) up to \(O((BL)^{-1})\). There are
\(O(1+\log(L/B))\) shells. Within each, (6) bounds a squared sum by
\(CL^2/[B(1+L^2\delta)]\). Encode each approximant by

\[
 t=amb-qh\ne0,\quad |t|\ll qB\delta,\qquad
 n=mb\le2MB,\quad n\equiv\bar a t\pmod q.                           \tag{8}
\]

For fixed \(t,n\), the possible \(b\)'s are divisors in a ratio-two
interval, so there are at most \(\Delta(n)\). The integers \(m=n/b\)
and \(h=(an-t)/q\) are then determined. Thus this encoding counts all
the approximants, even though we ignore several restrictions when taking
an upper bound. No dyadic subdivision of \(m\) is needed. Put
\(\eta=\min(\kappa,1)/100\).

If \(MB/q\ge X^\eta\), each positive residue progression for \(n\)
through \([1,2MB]\) has between \(MB/q\) and \(3MB/q\) terms. All
its values are at most \(X\). Apply (5); its gcd with \(q\) is
\((t,q)\). The resulting total over a tolerance class is bounded by

\[
 C {MB\over q}D_{c_0+1}(X)
       \sum_{0<|t|\le CqB\delta}\tau((t,q)).
\]

For every real \(T_1>0\), including \(T_1<1\),

\[
 \sum_{0<|t|\le T_1}\tau((t,q))
 =2\sum_{d\mid q}\lfloor T_1/d\rfloor
 \le 2T_1\sum_{d\mid q}1/d\ll T_1\operatorname{Log}_2X.
\]

Consequently the number of approximants in (8) is
\(\ll MB^2\delta D_{c_0+2}(X)\). Multiplication by (6) and summation of
\(\delta\) costs
\(\ll MB(1+\log(L/B))D_{c_0+2}(X)\). Summing the dyadic \(B\)'s costs
\(O(MLD_{c_0+2}(X))\), not a harmonic logarithm.

For \(B<B_0=qX^\eta/M\), use \(\Delta(n)\ll_\eta X^\eta\) and at
most \(2MB/q+1\) points per residue progression. The nonzero \(t\)'s
number \(O(qB\delta)\), with no additive 1. The class therefore has
at most \(C_\eta(MB^2+qB)\delta X^\eta\) approximants. After applying
(6) and summing its shells, this contributes at most
\(C_\eta(MB+q)X^\eta(1+\log(L/B))\).
Since \(B_0<L\) for large \(X\), summing the dyadic blocks costs

\[
 \ll_\eta (MB_0+q\log X)X^\eta\log X
 \ll_\eta qX^{2\eta}(\log X)^2
 \ll_\kappa ML.
\]

The last inequality uses \(q\le ML X^{-\kappa}\) and \(2\eta<\kappa\).
If \(B_0<1/2\), this sum is empty. Combining both ranges with the
small-\(Q\) and retained-term bounds proves (7). Excluding \(t=0\)
is essential: including it would invalidate the small-denominator bound.

## 5. Reciprocal quadratic means

Use fixed positive integers \(a,c\) (only small parity factors occur),
\(v\in\mathbb Z\), \((v,q)=1\), \(K\ge2\), and \(q>aK\), with

\[
 \alpha_r={av\bar q\over cr},\qquad (q,cr)=1,                       \tag{9}
\]

where the inverse of \(q\) is taken modulo \(cr\). The bounded range
\(1\le K\le2\) is handled by absolute summation.

For \(R<r\le2R\), let \(w_r\) be uniformly Schwartz and allow arbitrary
linear phases \(\theta_r\). Take
\(X\ge64(a|v|K+cqR+q+R+K+1)\), and suppose \(R/K\ge X^\kappa\).
Then

\[
 \sum_r\left|\sum_jw_r(j/K)e(\alpha_rj^2+\theta_rj)\right|^2
 \ll RK D_{c_0+2}(X).                                               \tag{10}
\]

For an approximant \(h/b\), \(b\le K\), with tolerance \(\delta\), write
\(A_r\) for the residue of \(av\bar q\) modulo \(cr\) and set
\(t=bA_r-hcr\). Then
\(cr\mid bav-qt\) and \(|t|\ll_c bR\delta\).
The encoded integer cannot vanish: that would force \(q\mid abv\) or
equivalently \(q\mid ab\), contrary to \(q>aK\).
Possible \(r\)'s are therefore divisors in a fixed-ratio interval.

More explicitly, choose one Dirichlet approximant for each \(r\), and
use the shells \(\delta=2^jK^{-2}\) as above. For fixed \(b,t,r\),
the value of \(h\) is determined; and \(cr\) is a divisor of
\(|bav-qt|\) in \((cR,2cR]\). Thus a tolerance class contains at most

\[
 \sum_{|t|\le 2cRb\delta}\Delta(|bav-qt|)                             \tag{10a}
\]

indices. All polynomial values appearing here are nonzero and at most
\(X\), by the assumed bound on \(X\). Choose
\(\eta=\min(\kappa,1)/100\).

For \(b\ge B_0=K^2X^\eta/R\), the interval in (10a) has
\(\asymp_c Rb\delta\ge X^\eta\) terms, so (5) applies already at
\(\delta=K^{-2}\). The polynomial's gcd is
\((bav,q)=(ab,q)\). The count is at most
\(CRb\delta\,\tau((q,ab))D_{c_0+1}(X)\).
Using (6) and summing dyadic \(\delta\) gives

\[
 CR\tau((q,ab))(1+\log(K/b))D_{c_0+1}(X).
\]

Finally
\[
 \sum_{b\le K}\tau((q,ab))(1+\log(K/b))
 \ll_a K\sum_{d\mid q}1/d\ll_a K\operatorname{Log}_2X.
\]

To see the first inequality, use
\(\tau((ab,q))\le\tau(a)\sum_{d\mid(b,q)}1\), interchange the sums,
and bound
\(\sum_{j\le K/d}(1+\log(K/(dj)))\ll K/d\).

For \(b<B_0\), (10a) and \(\Delta(n)\ll_\eta X^\eta\) give
\(C_\eta(Rb\delta+1)X^\eta\) indices. Multiplying by (6) and summing
the shells costs at most

\[
 C_\eta X^\eta\left[R(1+\log(K/b))+{K^2\over b}\right].
\]

Summing \(b<B_0\) gives
\(O_\eta(K^2X^{2\eta}\log X)\), absorbed by \(RK\) because
\(R/K\ge X^\kappa\) and \(2\eta<\kappa\). If \(B_0<1\), there
are no such denominators. This completes the proof of (10) and only requires the
power separation \(R/K\ge X^\kappa\), not \(R/K^2\ge X^\kappa\).
There is no integral zero of the encoding; Nair–Tenenbaum already uses
absolute polynomial values, so a change of sign needs no extra argument.

## 6. Nearby mean, with a power-sized frequency tail

Fix \(\epsilon=1/1000\), \(\delta=1/100\), and put \(L=\sqrt T\).
Assume \((u,v)=1\), \(au-bv=1\), and

\[
 T^{1/16}\le u\le LT^\epsilon,\quad
 cT^{3/4-\epsilon}\le v\le T^{3/4},\quad
 H\ge LT^{-\epsilon},\quad uH\le T,\quad
 v/H\le M\le 2(v/H)T^\delta.
\]

For a smooth weight \(w\) supported in a fixed compact subinterval of
\((0,\infty)\), define

\[
 S_m=\sum_z w(z/L)e(ma z^2/v),\qquad
 B_m={G(mb;u)\over u}\int w(z/L)e(mz^2/(uv))\,dz.
\]

The replacement for `lem:nearby-mean` is

\[
 \sum_{m\le M}|S_m-B_m|\ll M\sqrt L D_{c_0/2+2}(T).                 \tag{11}
\]

For \(m\le M_2=\lfloor uv/L^2\rfloor\), the weights
\(w(s)e(ms^2L^2/(uv))\) form a bounded Schwartz family. If \(M_2\ge1\),
then \(M_2\ge uv/(2L^2)\) and
\(u/(M_2L)\le2L/v\ll T^{-1/4+\epsilon}\).
Use (7), with \(q=u\) and \(X=T^4\), followed by Cauchy–Schwarz.
This costs \(M_2\sqrt L D_{c_0/2+1}(T)\), and \(M_2\le v/H\le M\).
If \(M_2=0\) this portion is empty. No separate reciprocity estimate for
inverse coefficients at a fixed denominator is needed.

For larger \(m\), set \(d=(m,u)\), \(q=u/d\), \(r=m/d\), and
\(A=mL^2/(uv)>1\). Then \((r,q)=(b,q)=(v,q)=1\),
\(bv\equiv-1\pmod q\), and Poisson summation gives exactly

\[
 S_m-B_m={1\over q}\sum_{\ell\ne0}G(rb,\ell;q)
    \int w(z/L)e(rz^2/(qv)-\ell z/q)\,dz.                           \tag{11a}
\]

The integral equals

\[
 {L e(1/8)\over\sqrt{2A}}e(-v\ell^2/(4rq))
       \Psi_A(\ell/(2K_r)),\qquad K_r=rL/v,
\]

with the uniformly Schwartz family \(\Psi_A\) from Section 3.
Completing the Gauss square gives the following identities. Each \(C\)
is independent of the summation index and has modulus at most \(\sqrt{2q}\):

\[
\begin{array}{ll}
q\text{ odd}:&G(rb,\ell;q)e(-v\ell^2/(4rq))
 =C e(-v\bar q\ell^2/(4r));\\
4\mid q:&G(rb,\ell;q)=0\ (\ell\text{ odd}),\\
&G(rb,2j;q)e(-vj^2/(rq))=C e(-v\bar qj^2/r);\\
q=2q_0,\ q_0\text{ odd}:&G(rb,\ell;q)=0\ (\ell\text{ even}),\\
&G(rb,\ell;q)e(-v\ell^2/(8rq_0))
 =C e(-v\bar q_0\ell^2/(8r))\quad(\ell\text{ odd}).
\end{array}                                                        \tag{11b}
\]

Inverses are taken modulo the displayed denominator. For odd \(q\),
completion gives the phase \(v\overline{4r}\ell^2/q\), and
\(\overline{4r}/q-1/(4rq)\equiv-\bar q/(4r)\pmod1\).
For \(4\mid q\), shift by \(q/2\) to eliminate odd indices and complete
the square for \(\ell=2j\). For \(q=2q_0\), the same shift eliminates
even indices; for odd \(\ell\), reduce to
\(2G(rb\overline2,\ell\overline2;q_0)\), complete the square, and apply
the inverse identity with \(8r\) in place of \(4r\).
These are algebraic identities, not conclusions from the numerical tests.

The prefactor in (11a) has modulus \(O(\sqrt{v/r})\). Its remaining
sum has length \(K_r\) with uniformly Schwartz weights, and its phase
has the form (9). The constants
\((a,c)\) there are \((1,4)\), \((1,1)\), or \((4,8)\); in the last
case use modulus \(q/2\) and write the odd index as \(2j+1\), allowing
the resulting linear phase. Signs of \(v\) are immaterial. A removed
zero-frequency term costs \(O(\sqrt L)\) when \(K_r\ge1\).
When \(K_r<1\), the nonzero-frequency Schwartz tail directly costs
\(O(\sqrt L)\).

On a dyadic block \(R<r\le2R\), set \(K=RL/v\). The weights after
rescaling have uniformly bounded Schwartz seminorms, including the
translated odd-index weight. The bounds above give

\[
 K\ll T^{\epsilon+\delta}/d,\quad
 q/K\gg T^{1/16-\epsilon-\delta},\quad
 R/K=v/L\gg T^{1/4-\epsilon}.
\]

Thus (10) applies (also to \(q/2\)) with \(X=T^4\) and, for example,
a sufficiently small fixed \(\kappa<1/100\). All encoded integers
are \(O(qR+vK+1)\ll T^4\). Cauchy–Schwarz gives a block contribution

\[
 \sqrt{v/R}\sqrt R\sqrt{RKD_{c_0+2}(T)}
 \ll R\sqrt L D_{c_0/2+1}(T).
\]

The dyadic blocks sum geometrically, and
\(\sum_{d\mid u}M/d\ll M\operatorname{Log}_2T\), proving (11).
There is no truncation or partial summation in the dual index: the
Schwartz version of (10) handles it directly.
Partial blocks, coprimality restrictions and the restriction \(A>1\)
are handled by setting the other weights to zero; no regularity in the
index \(r\) is required. Blocks with bounded \(K\) are estimated trivially.

## 7. Primitive terminal theorem

Write \(\ell=\operatorname{Log}_2T\). Fix the translation constant
\(C_0\). We claim that, for large \(T\), a proper progression

\[
 Q=\{t+ux+vy:0\le x\le H,\ 0\le y\le J\},\quad (u,v)=1,
\]

with positive steps, \(t\ge0\), \(T=\max Q\le C_0(uH+vJ)\), contains
a positive square if

\[
 \min(H,J)\ge T^{1/4}\ell^{10},\qquad HJ\ge T^{3/4}\ell^{10}.
 \tag{12}
\]

The exponent 10 is deliberately generous, not optimized. Orient
\(vJ\ge uH\). Properness implies \(v>H\), and \(vJ\asymp T\).
The long-side lemma in Section 10 handles \(H\ge4L\), since
\(J^2/u\ge J(HJ)/T\ge\ell^{20}\).

### 7.1 Noncritical side length

Suppose \(J\ge T^{1/4+\epsilon}\). Then
\(v\le T^{3/4-\epsilon}\). Use the coefficient interval
\([H/8,H/4]\) and the real root interval

\[
 I_z=[\sqrt{t+uH/4},\sqrt{t+vJ+uH/8}].
\]

For every pair in this rectangle,
\(0\le z^2-t-ux\le vJ\). Thus an integral solution of
\(z^2\equiv ux+t\pmod v\) gives a positive square in \(Q\).
The root interval has length \(\gg L\): its squared width is at least
\(7vJ/8\), while the sum of its endpoints is at most \(2L\).
Take fixed smooth nonnegative windows: \(F\) supported
in the interior coefficient interval, with a plateau of length \(\gg H\),
and \(w(z/L)\) supported inside the root interval, with integral \(\gg L\).
All rescaled derivatives are uniformly bounded. Periodize

\[
 f(s)=\sum_n F(v(s+n)),\qquad
 |\widehat f(m)|\ll_A {H\over v}(1+|m|H/v)^{-A}.                     \tag{13}
\]

The nonnegative count is \(\mathcal N=\sum_z w(z/L)f(\bar u(z^2-t)/v)\).
Its complete-period main term is

\[
 \mathcal C={1\over v}\left(\int w(z/L)\,dz\right)
       \sum_{x\in\mathbb Z}F(x)\rho_v(ux+t).
\]

This follows by retaining the complete Gauss contribution in every
Fourier mode and grouping roots modulo \(v\). In particular it is at least
\(cLH/(v\ell)\): the root-density lemma applies on the plateau because
\(H^2/v\ge H(HJ)/T\ge\ell^{20}\).

Put \(M_0=v/H\) and \(M_* =\lfloor\sqrt L/\ell^5\rfloor\).
The area bound gives \(M_0\le\sqrt L/\ell^{10}\), so \(M_*\ge M_0\).
Use (7) for prefixes up to \(M_*\) and then dyadic prefixes above it,
with \(X=T^8\) and a fixed \(\kappa<\epsilon/32\). Uniformly through
\(M\le2T^2\), its range condition follows from
\(v/(M_*L)\ll T^{-\epsilon}\ell^5\).
Together with (13), Cauchy–Schwarz bounds the total error by

\[
 \ll {H\over v}M_*\sqrt L\,\ell^{(c_0+2)/2}+O(1).                  \tag{14}
\]

The tail beyond \(T^2\) is bounded trivially using (13), with a large
fixed \(A\); the zero mode costs \(O(H/v)\). One must not discard the
tail immediately beyond \(M_*\):
there is only a log-log separation there. The centered mean is used on
all its dyadic blocks. Comparing (14) to the main term leaves the factor
\(\ell^{-5+(c_0+2)/2+1}\to0\), also for the checked
\(c_0=5\), when the exponent is \(-1/2\).

### 7.2 Critical side length

Now \(J<T^{1/4+\epsilon}\). The geometric bounds give

\[
 H\ge LT^{-\epsilon}\ell^{10},\quad
 u\le LT^\epsilon,\quad
 cT^{3/4-\epsilon}\le v\le T^{3/4}.
\]

If \(u<T^{1/16}\), the square-root fiber lemma in Section 10.3 applies, since
\(J\ge16u\), \(J<T^{1/4+\epsilon}<L\), and
\(H^7J^3/(u^2T^4)\ge T^{1/8-4\epsilon}\ell^{70}\to\infty\).
This is a positive power margin and consumes no log-log budget.
Otherwise the hypotheses of (11) hold.

Use \(F\) as in (13), supported in \([H/8,H/4]\) and with a plateau
of length \(\gg H\). Choose \(w\) inside the valid root interval, equal
to 1 on all roots of \(t+vy+ux\) with \(J/3\le y\le J/2\) and
\(x\in\operatorname{supp}F\). The dominant span ensures fixed margins
and uniformly bounded rescaled derivatives. The alternative main term is
exactly the positive expression

\[
 \mathcal B={1\over u}\sum_y\rho_u(t+vy)
       \int w(z/L)F((z^2-t-vy)/u)\,dz.                              \tag{15}
\]

Indeed, retaining \(B_m\) in the Fourier expansion and using
\(a/v=b/u+1/(uv)\) gives
\(u^{-1}\sum_{r\bmod u}\int w(z/L)
 f(b(r^2-t)/u+(z^2-t)/(uv))\,dz\).
Expanding the periodization makes its integer parameter \(y\) satisfy
\(y\equiv-b(r^2-t)\pmod u\), equivalently
\(t+vy\equiv r^2\pmod u\), proving (15).

For the indicated \(y\)'s the integral is \(\gg uH/L\). Since
\(J^2/u\ge\ell^{20}\), root density and
\(\varphi(u)/u\gg1/\ell\) give

\[
 \mathcal B\gg HJ/(L\ell)\ge\sqrt L\,\ell^9.                       \tag{16}
\]

The Fourier terms of the count and (15) are the same coefficients and
unit phases times \(S_m\) and \(B_m\) from (11), respectively. Apply
(11) on dyadic frequency blocks up to \(M_0T^\delta\), using (13).
Their sum costs \(O(\sqrt L\,\ell^{c_0/2+2})\), with exponent
\(9/2\) for the checked input. Beyond that frequency the
trivial bound \(|S_m|+|B_m|\ll L\), together with (13) of sufficiently
large fixed order, gives \(O(T^{-2})\). The zero mode costs \(O(H/v)\).
The error is therefore smaller than (16), proving positivity.

## 8. Common factor and final exponents

### 8.1 Removing a common factor without a logarithmic loss

Consider the proper homogeneous progression
\(Q=\{g(t+ux+vy):0\le x\le H,0\le y\le J\}\), with \((u,v)=1\),
\(t\ge0\), and \(T=\max Q\le C_0g(uH+vJ)\). Suppose its minimum
width and area exceed \(T^{1/4}\ell^B\) and \(T^{3/4}\ell^B\),
respectively, where \(\ell=\operatorname{Log}_2T\). Relabel so that
\(H\ge J\), and put \(V=HJ\).
Properness implies \(gV\le T\), hence
\(g\le T^{1/4}\ell^{-B}\). With \(d_u=(g,u)\),
\(J^2/(d_u u)\ge JV/T\ge\ell^{2B}\), so the long-side lemma applies
if \(H\ge4\sqrt T/d_u\). Otherwise retain the strict opposite inequality.

The lattice
\(\mathcal L=\{(x,y)\in\mathbb Z^2:ux+vy\equiv0\pmod g\}\)
has index \(g\), and its coset with \(t+ux+vy\equiv0\pmod g\)
is nonempty. Scale the axes by \(D=\operatorname{diag}(1/H,1/J)\).
A Gauss-reduced lattice basis \(b_1,b_2\), with
\(\lambda_i=\|Db_i\|\), satisfies

\[
 \lambda_1\le\lambda_2,\quad
 |\langle Db_1,Db_2\rangle|\le\lambda_1^2/2,\quad
 {g\over V}\le\lambda_1\lambda_2\le{2g\over\sqrt3 V}.
\]

Such a basis is obtained by subtracting nearest integer multiples and
interchanging shorter vectors; discreteness makes the reductions terminate.
At least one of \((g,0),(0,g)\) is independent of \(b_1\) and has
scaled length at most \(g/J\). Its determinant with \(Db_1\) is a
nonzero integral multiple of \(g/V\), giving
\(\lambda_2\ll g/J\ll\ell^{-2B}\).

Round the scaled center \((1/2,1/2)\) to the required lattice coset, with
error at most \((\lambda_1+\lambda_2)/2\). Around the resulting point
\(z_*\), take the coefficient box \(|n_i|\le l_i\), where
\(l_i=\lfloor1/(64\lambda_i)\rfloor\). For large \(T\), it lies in
\([H/4,3H/4]\times[J/4,3J/4]\) and \(l_i\lambda_i\asymp1\).
Its image under \((x,y)\mapsto(t+ux+vy)/g\) is a proper progression
\(Q_0\) with \(g^2Q_0\subset Q\). Its steps are coprime: the image of
\(\mathcal L\) under \((x,y)\mapsto ux+vy\) is exactly \(g\mathbb Z\).
No step vanishes, by original properness. Reverse negative steps.

Write \(T_0=\max Q_0\). The central containment gives
\(T/(4g^2)\le T_0\le T/g^2\). The angle of the reduced basis is
bounded away from zero and \(\pi\), so
\(\operatorname{diam}Q_0\gg(uH+vJ)/g\), proving uniform translation
control. Its area is \(\gg V/g\).

For the minimum width, write \(b_1=(a,b)\). If \(b\ne0\), then
\(\lambda_1\ge1/J\), so
\(1/\lambda_2\gg H/g\ge V/\sqrt{gT}\), using \(gJ^2\le T\).
If \(b=0\), then \(|a|\ge g/d_u\), and the short-side inequality gives
\(\lambda_1\ge g/(d_uH)>g/(4\sqrt T)\), so
\(1/\lambda_2\gg V/\sqrt T\). Thus in either case

\[
 \min(H_0,J_0)\gg(T/g^2)^{1/4}\ell^B,\qquad
 H_0J_0\gg(T/g^2)^{3/4}\ell^B.
\]

Also \(\max Q_0\ge T^{1/2}/4\to\infty\). Thus exponent \(B=11\)
in the nonprimitive problem gives (12), for sufficiently large \(T\):
\(\operatorname{Log}_2T_0\le\ell\), and the spare power of \(\ell\)
absorbs all fixed constants. A square in \(Q_0\) produces one in \(Q\).

### 8.2 The subset-sum bound

Suppose \(A\subset[1,N]\) has \(m\) elements and no positive square
among its subset sums. Apply (S). Reverse negative steps in its progression
and factor out their gcd. Homogeneity and nonnegativity make the base point
an integer \(gt\), with \(t\ge0\). In rank two we therefore have exactly
the form used in Section 8.1, with \(H,J\gg m\), \(HJ\gg m^3\), and
the required translation control. No step vanishes, since the progression
is proper and every coefficient interval has more than one value.

For the structural output (S), put \(E=m^3/N\) and
\(T=\max Q\le mN=m^4/E\). Then

\[
 {m\over T^{1/4}}\ge E^{1/4},\qquad
 {m^3\over T^{3/4}}\ge E^{3/4}.
\]

Consequently \(m\ge C N^{1/3}(\operatorname{Log}_2N)^{16}\) has ample
room for the terminal exponent 11: the minimum-side ratio has log-log
exponent 12 and the area ratio exponent 36. Here
\(\operatorname{Log}_2T\asymp\operatorname{Log}_2N\), since
\(cm^3\le T+1\le mN\) in rank two. In rank one, (S) gives coefficient
length \(W\gg m^2\), whose square divided by \(T\) is \(\gg E\).
For large \(N\) this gives \(W\ge4\sqrt T\); since \(gW\le T\),
it also gives \(W\ge2\sqrt T+g\). Section 10.2 applies.
Both ranks therefore give a positive square in \(\Sigma(A)\), a
contradiction. It follows that \(m<C_*N^{1/3}(\operatorname{Log}_2N)^{16}\)
for a suitable absolute \(C_*\), proving the theorem.

**Conclusion:**

\[
 \boxed{\operatorname{SF}(N)\ll N^{1/3}(\operatorname{Log}_2N)^{16}.}
\]

The exponent is not optimized. The lower bound and
\(N^{1/3+o(1)}\) consequence were already formalized for the older
logarithmic upper bound and are unchanged. The new upper bound is now
formalized unconditionally in Lean by the route recorded in Section 11.

## 9. Regression checks and audit record

Run `python3 tex/erdos587/check_loglog_reconstruction.py` from the repository
root. The deterministic run on 2026-08-27 passed:

- 30,643 centered divisor encodings and 21,946 reciprocal encodings,
  checked using exact rational arithmetic;
- 6,960 exact rational lattice lifts in two-dimensional ellipses;
- 35,637 Gauss-reciprocity identities, checked numerically in all three
  parity cases (maximum absolute discrepancy below \(2.5\cdot10^{-14}\));
- 1,500 Gaussian major-arc samples (largest normalized squared sum
  approximately 3.87505); this is a diagnostic, not a universal constant;
- positive exact rational margins for the modulus separations, both
  main-term comparisons, the small-step exit, and the final exponent 16.

The second mathematical pass specifically checked these possible failure
points: the discriminant and coefficient uniformity in Nair–Tenenbaum;
the exclusion of the zero encoding in the centered mean; the small
denominator contribution in both means; the full-lattice basis, integer
translation, and rounding cell after quotienting; the noncritical Fourier
tail beyond \(M_*\); and the power-sized critical tail permitted by (11).
No finite test verifies the analytic inequalities or the asymptotic theorem.

The completion audit additionally corrected linear versus affine spanning
and proved the robust spanning assertion from resilience with \(\beta=6\),
so that \(n\le s^6\) is valid. The logical dependencies are:

| Required conclusion | Mathematical proof in this document |
| --- | --- |
| Full-size, full-width homogeneous progression, including dimension drops | Section 1; exact quotient lifting and a lattice-basis argument |
| Delta averages uniform in a changing linear polynomial | Section 2; the degree-one specialization of Nair–Tenenbaum |
| No harmonic logarithm in either quadratic mean | Sections 3–5; smooth completion and nonzero divisor encodings |
| Critical rational approximation and all Fourier tails | Sections 6–7; retained nearby mean and fixed smooth windows |
| All positive translated progressions, including a common factor and small steps | Sections 7–8 and 10 |
| The claimed exponent and contradiction for subset sums avoiding squares | Section 8.2; minimum-width exponent 12 and area exponent 36 exceed 11 |

## 10. Auxiliary square-location facts

These are the elementary reductions used above, with their analytic inputs
made explicit. They also appear in the older proof, but the arguments here
do not assume its logarithmic upper bound.

### 10.1 Roots in a linear interval

Put \(\rho_q(n)=\#\{z\bmod q:z^2\equiv n\pmod q\}\), with
\(\rho_1=1\). There are absolute \(c,C>0\) such that, for \((a,q)=1\),
any interval \(I\) of \(H\ge C\sqrt q\) consecutive integers satisfies

\[
 \sum_{x\in I}\rho_q(ax+b)\ge cH\varphi(q)/q.                       \tag{17}
\]

Here is a proof. Count only roots coprime to \(q\). Write \(q=2^\nu Q\)
with \(Q\) odd, and let \(R\) be its squarefree kernel. For odd \(q\)
put \(k=c_2=1\); otherwise put \(k=2^{\min(\nu,3)}\), \(c_2=k/2\),
and restrict \(x\) to the unique class \(ax+b\equiv1\pmod k\).
Write \(x=x_0+ky\) and \(f(y)=a(x_0+ky)+b\). Elementary lifting of
quadratic residues shows that the unit-root count is

\[
 c_2\sum_y1_{(f(y),Q)=1}\prod_{p\mid R}(1+\chi_p(f(y))),
\]

where \(\chi_p\) is the Legendre symbol. The term with no characters
is \(H\varphi(q)/q+O(2^{\omega(Q)})\), by inclusion-exclusion.

For each other term, let \(d>1\) be the product of its character primes.
Expand the coprimality indicator as \(\sum_{e\mid R}\mu(e)1_{e\mid f(y)}\).
If \((e,d)>1\) the term vanishes. Otherwise reindex the unique selected
class modulo \(e\). The resulting character is a unit multiple of a
translate of the primitive quadratic character modulo \(d\), on an
interval of length at most \(H/(ke)+1\). Burgess with parameter 2 bounds
it by \(O_\xi(\sqrt H\,q^{3/16+\xi}+1)\). There are at most
\(4^{\omega(Q)}\ll_\xi q^\xi\) terms. Thus the total error is

\[
 O_\xi(\sqrt H\,q^{3/16+2\xi}+q^\xi).
\]

With \(\xi=1/128\), this is \(o(H\varphi(q)/q)\) uniformly for
\(\sqrt q\le H\le q\). For \(H\ge q\), use disjoint complete periods,
whose unit-root count is exactly \(\varphi(q)\). Finally increase \(C\)
to cover the finitely many small moduli. This proves (17).

A useful nonprimitive version is: if \((a,v)=1\), \(d=(g,v)\), and
\(H\ge C\sqrt{dv}\), then there exists \(x\in I\) and a residue \(z\)
with \(gz^2\equiv ax+b\pmod v\). Indeed first restrict \(x\) to the
class \(ax+b\equiv0\pmod d\); divide by \(d\), invert \(g/d\) modulo
\(v/d\), and apply (17) on an interval of \(\gg H/d\) terms.

### 10.2 Rank one and long sides

A homogeneous arithmetic progression \(\{g(t+j):0\le j\le W\}\)
in \([0,T]\) contains a positive square if \(W\ge2\sqrt T+g\).
Choose \(k=\lfloor\sqrt{t/g}\rfloor+1\). Then
\(0<gk^2-t\le2\sqrt{gt}+g\le2\sqrt T+g\), and the corresponding
term of the progression is \(g^2k^2\).

For \(Q=\{g(t+ux+vy):0\le x\le H,0\le y\le J\}\), put
\(d=(g,u)\). If \(J+1\ge C\sqrt{du}\) and \(H\ge4\sqrt T/d\),
the preceding nonprimitive root bound gives \(y\in[0,J]\) and
\(z_0\) with \(gz_0^2\equiv t+vy\pmod u\).
The congruence is preserved by \(z\equiv z_0\pmod{u/d}\).
The interval

\[
 [\sqrt{(t+vy)/g},\sqrt{(t+vy+uH)/g}]
\]

has length at least \(uH/(2\sqrt T)\ge2u/d\), so it contains a
positive integer in this residue class. Its square gives
\(gz^2=t+ux+vy\), for integral \(0\le x\le H\), and therefore
\(g^2z^2\in Q\). Interchanging the coordinates gives the other exit.

### 10.3 The small primitive step

We need the following consequence of the second derivative test. Suppose
an interval has \(n\ge2\) integer points and a \(C^3\) phase \(f\)
satisfies \(|f^{(j)}|\asymp F/n^j\), \(j=2,3\), with \(F\ge n\).
Then, if \(0<\delta\le1/2\) and \(\delta^7 n^3\ge C F\), some
fractional part \(f(j)\) lies in any specified open interval of length
\(\delta\). Constants depend only on the derivative comparability bounds.

To prove this, for integer \(h\ge1\) put \(G=hF\). We have
\(\left|\sum e(hf(j))\right|\ll G^{1/6}n^{1/2}\).
For \(n\le G\le n^{3/2}\), the second derivative test gives
\(O(\sqrt G+n/\sqrt G)\), which is at most this bound. For
\(G\ge n^3\), the trivial bound suffices. In between, put
\(\lambda=G/n^3\), and difference with
\(K=\lfloor\lambda^{-1/3}\rfloor\asymp\lambda^{-1/3}\le\sqrt n\).
The differenced phases have second derivative \(\asymp r\lambda\)
because \(f'''\) has a constant sign. The shift-and-Cauchy–Schwarz
inequality and the second derivative test give

\[
 \left|\sum e(hf(j))\right|^2
 \ll {n^2\over K}+n^2\lambda^{1/2}K^{1/2}
                       +n\lambda^{-1/2}K^{-1/2}
 \ll n^2\lambda^{1/3}+n\lambda^{-1/3}.
\]

The second term is no larger than the first when \(G\ge n^{3/2}\),
proving the assertion. Now place a triangular nonnegative function of
integral 1 inside the target interval on the circle. Its nonzero Fourier
coefficients are \(O(\min(1,(h\delta)^{-2}))\). The difference between
its sum on the \(n\) fractional parts and its expected value \(n\) is

\[
 \ll F^{1/6}n^{1/2}\sum_{h\ge1}h^{1/6}
                         \min(1,(h\delta)^{-2})
 \ll F^{1/6}n^{1/2}\delta^{-7/6}<n/2
\]

when the constant in \(\delta^7n^3\ge CF\) is large enough. Positivity
of the sum places a fractional part in the open interval.

Apply this to a primitive progression
\(Q=\{t+ux+vy:0\le x\le H,0\le y\le J\}\), with controlled
translation, \(J\ge16u\), \(J\le\sqrt T\), and
\(H^7J^3\ge C u^2T^4\). Choose \(0\le y_0<u\) with
\(t+vy_0\equiv0\pmod u\), and restrict \(y=y_0+u j\).
The subprogression is
\(u(t'+x+vj)\), where \(t'=(t+vy_0)/u\) and
\(0\le j\le J'=\lfloor(J-y_0)/u\rfloor\asymp J/u\).
Its maximum is comparable to \(T\), and translation control passes to it.
Properness implies \(v>H\).

If \(H\ge4\sqrt T\), the rank-one assertion handles a row, since
\(uH\le T\). Otherwise, for \(J'/4\le j\le J'/2\), put

\[
 f(j)=\sqrt{(t'+vj)/u},\quad n\asymp J/u,\quad
 F=\sqrt T/u,\quad \delta=H/(8\sqrt T).
\]

On this interval \(t'+vj\asymp T/u\), giving the stated derivative
bounds. Also \(F\ge n\) and
\(\delta^7n^3/F\gg H^7J^3/(u^2T^4)\). Find a fractional part in
\((1-\delta,1)\), and let \(k=\lceil f(j)\rceil\). Then

\[
 0<uk^2-(t'+vj)<2\sqrt T\,\delta+u\delta^2<H.
\]

The middle expression is an integer \(x\); hence
\(u^2k^2=u(t'+x+vj)\in Q\), as required. This proves precisely the
fiber criterion used in Section 7.2.

## 11. A less sharp Delta input for the Lean proof

The final exponent 16 does not require the sharp KT exponent 11/4.
The following variant of their moment argument is enough and avoids the
Gaussian truncation and fractional-exponent moment envelope. Its target is
the **harmonic** bound

\[
 \sum_{n\le X}\frac{\Delta(n)}n
   \ll \operatorname{Log}X\,(\operatorname{Log}_2X)^4.               \tag{L1}
\]

This is exactly the input needed after partial summation in Section 2;
we need not also formalize the conversion to an unweighted Delta mean.
This section gives the mathematical argument. The corresponding Lean
mean-value estimate is not yet proved.

### 11.1 Maximal divisor control without a Gaussian

Fix the ambient cutoff \(X>1\), and let \(\mathcal S_{<X}\) consist of
the squarefree products of primes less than \(X\). Give it probability
mass proportional to \(1/n\). The prime indicators are independent,
with \(\mathbb P(p\mid n)=1/(p+1)\). Enumerating the primes increasingly,
write \(\tau_i\) for the number of divisors of the product of the selected
first \(i\) primes, and put

\[
 c_i=\prod_{j\le i}\left(1+\frac1{p_j+1}\right),\qquad Z_i=\tau_i/c_i.
\]

Then \(Z_i\) is a nonnegative martingale of mean 1. The elementary
finite stopping argument gives \(\mathbb P(\max_i Z_i>B)\le1/B\):
partition by the first crossing prefix, and on each such prefix the
conditional expectation of the terminal value equals its current value.
Mertens' estimate gives \(c_i\ll\operatorname{Log}p_i\). Consequently,
if \(\mathcal S^A_{<X}\) imposes

\[
 \tau(n_{<y})\le A\operatorname{Log}y\quad(1\le y\le X),
\]

then
\(\sum_{\mathcal S_{<X}\setminus\mathcal S^A_{<X}}1/n
\ll\operatorname{Log}X/A\).
The same definition makes sense with any smaller cutoff. Above the last
prime present in \(n\), the condition only becomes weaker.

### 11.2 An ambient-cutoff moment induction

Put \(L=\operatorname{Log}_2X\), fix a sufficiently large absolute
constant \(C\), and use

\[
 B=CAL,\qquad m_q=(q!)^2 B^{q-1}\quad(q\ge1).
\]

Thus \(m_1=1\), \(m_2=4CAL\), and

\[
 \sum_{1\le b\le q/2}\binom qb m_bm_{q-b}\le m_q/B.               \tag{L2}
\]

Indeed, after multiplying a summand by \(Bq\), its ratio to \(m_q\)
is \(q/\binom qb\le1\); there are at most \(q\) summands.
Also \(A m_q\le(q^2B)^q\), since \(q!\le q^q\) and \(A\le B\).

Impose the lower-moment conditions \(M_j(n)/\tau(n)\le m_j\) up to
order \(q\), as in KT, and denote the resulting sets by
\(\mathcal S^{q,A}_{<x}\). All these conditions are preserved by
prime truncation, because the exact prime recurrence implies
\(M_j(pn)\ge2M_j(n)\) and \(\tau(pn)=2\tau(n)\).
Define

\[
 T_q(x)=\sum_{n\in\mathcal S^{q-1,A}_{<x}}
            \frac{M_q(n)}{\tau(n)n}\qquad(1<x\le X).
\]

We prove \(T_q(x)\le C m_q\operatorname{Log}x/(q^2A)\) by induction
on \(q\ge2\). KT's exact prime decomposition, reflection symmetry,
and short-prime-interval estimate give the same recurrence and prime
averaging bound as their equations (mq-2), (tax), and (qx):

\[
 T_q(x)\ll Q_q(x)+\sum_{p<x}\frac{Q_q(p)}p
                          \frac{\operatorname{Log}x}{\operatorname{Log}p}.
\]

In the integral for \(Q_q\), use sets with prime cutoff
\(\min(y,X)\). This is essential: its integration range reaches \(x^2\),
but the moment envelopes have the one fixed ambient parameter \(L\).
For \(y>X\), the divisor restriction still holds since
\(\tau(n)\le A\operatorname{Log}X\le A\operatorname{Log}y\), and the
induction hypothesis at \(X\) is bounded by the same expression with
\(\operatorname{Log}y\).

For \(q=2\), unrestricted Euler products give
\(Q_2(x)\ll\operatorname{Log}x\), whence
\(T_2(x)\ll L\operatorname{Log}x\), as required.
For \(q\ge3\), the short-interval remainder satisfies

\[
 R_q(x)\ll c^q q! A^{q-2}
\]

for an absolute \(c\). One can use the particularly simple bound
\(M_a(n)M_b(n)\le\tau(n)^{a+b}\), which follows from
\(M_j\le\Delta^{j-1}M_1\le\tau^j\). Together with
\(\tau^{q-1}\le(A\operatorname{Log}y)^{q-2}\tau\), the Euler product
\(\sum_{\mathcal S_{<y}}\tau(n)/n\ll(\operatorname{Log}y)^2\), and
\(\sum_b\binom qb2^b=3^q\), the remaining integral is bounded by a
constant times
\(3^q A^{q-2}\int_1^\infty(\operatorname{Log}y)^{q-1}y^{-5/4}dy\).

For the principal part, the induction hypothesis and \(q-b\ge q/2\)
give, using (L2),

\[
 Q'_q(x)\ll\frac{C}{q^2}\frac{m_q}{CAL}\operatorname{Log}x.
\]

Iterating costs at most \(\operatorname{Log}_2x\le L\), so

\[
 T_q(x)\ll\left(c^q q! A^{q-2}+\frac{m_q}{q^2A}\right)
                    \operatorname{Log}x.
\]

Both terms are absorbed by \(C m_q/(q^2A)\) for a sufficiently large
fixed \(C\). For the first, cancel factorials and powers of \(A\),
and use \(q^2\le4^q\), \(q!\ge1\), \(L\ge1\). All implied constants
are independent of \(q,A,X,x\).

### 11.3 Weak and strong harmonic bounds

Markov's inequality at each moment order and \(\sum_{q\ge2}q^{-2}<\infty\)
show that the total harmonic mass lost from all the restrictions through
any order is \(O(\operatorname{Log}X/A)\). For a retained integer,

\[
 \Delta(n)^q\le2^qM_q(n)\le2^q A m_q\operatorname{Log}X.
\]

Take \(q=\lceil L\rceil\). Since
\((\operatorname{Log}X)^{1/q}\le e\) and \(q\le2L\), (L2)'s growth
bound gives \(\Delta(n)\ll A L^3\). Thus

\[
 \sum_{\substack{n\in\mathcal S_{<X}\\\Delta(n)>C' A L^3}}\frac1n
       \ll\frac{\operatorname{Log}X}{A}.
\]

Dyadic summation below \((\operatorname{Log}X)^{10}\) costs \(O(L)\)
ranges. Above that cutoff, use
\(\Delta(n)\le\tau(n)^2/(\operatorname{Log}X)^{10}\) and the Euler
product for \(\tau^2\). This proves
\(\sum_{\mathcal S_{<X}}\Delta(n)/n\ll L^4\operatorname{Log}X\).
Changing the endpoint to include primes equal to \(X\) is harmless.

Finally, write each integer uniquely as \(n=ab\), where \(a\) contains
all prime powers of exponent at least 2, and \(b\) contains the primes
of exponent exactly 1. Then
\(\Delta(n)\le\tau(a)\Delta(b)\). Dropping coprimality and size
restrictions gives (L1), because

\[
 \sum_{a\text{ squarefull}}\frac{\tau(a)}a
   =\prod_p\left(1+\sum_{j\ge2}\frac{j+1}{p^j}\right)<\infty.
\]

### 11.4 Downstream exponents and Lean status

Using (L1) in Section 2 corresponds to the weaker effective value
\(c_0=4\). The linear-progression, quadratic-mean, and nearby-mean
log-log exponents become 5, 6, and 4, respectively. The noncritical
terminal error ratio is now \(\ell^{-5+3+1}=\ell^{-1}\), still tending
to zero. In the critical case the main term is at least
\(T^{1/4}\ell^9\), whereas the error is \(O(T^{1/4}\ell^4)\).
The common-factor and final exponent calculations are unchanged.

The Lean files `HooleyDelta`, `HooleyDivisorCounting`, `HooleyMoments`,
`HooleyReflection`, `HooleyPrimeRecursion`, `HooleyConcentration`,
`HooleyMomentEnvelope`, `HooleyMaximal`, `HooleyEulerProducts`, and
`HooleyMertens` compile at the unchanged resource limits. Their principal
declarations have been audited and use only standard Lean axioms.
The sharp Mertens estimate is reused from the 697 development; the finite
weighted maximal inequality is proved directly on a binary choice tree.
The exponent-4 route above was not pursued further. The simpler
exponent-5 route below now has both its full harmonic induction and
short-progression transfer formalized.

### 11.5 Unit-window smoothing: the simpler route used in Lean

There is a further simplification if we allow exponent 5 instead of 4 in
(L1), which still leaves the final exponent 16 unchanged. Replace the
envelope by

\[
 m_q=(q!)^3(CAL)^{q-1}.
\]

For a finite collection of primes \(P\) all at least \(Y>1\), the proved
prime-interval estimate implies

\[
 \sup_v\sum_{\substack{p\in P\\v\le\log p\le v+1}}\frac1p
       \le\frac{8e+336}{\log Y}.
\]

To check the constant, the Selberg estimate at sieve level \(x^{1/4}\)
gives a prime count at most \(8h/\log x+168\sqrt x\) in \([x,x+h]\).
Here \((1+t)^3\le28e^t\), obtained from the cubic exponential-series
term, absorbs the sieve remainder. Divide by \(x\), use
\(\log x\le2\sqrt x\), and place the logarithmic window inside
\([x,ex]\), taking \(x\) to be the maximum of \(Y\) and its lower
endpoint. This also covers singleton and clipped windows.

For every real \(r\), the two-window covering inequality gives

\[
 \Delta(n;r)^b\le
  2^{b-1}\int_{r-1}^{r}
    \big(\Delta(n;v)^b+\Delta(n;v+1)^b\big)\,dv.
\]

Apply this with \(r=u-\log p\), sum with weights \(1/p\), and exchange
the finite sum and integral. At each \(v\), the contributing primes
lie in one unit logarithmic window. Thus

\[
 \sum_{p\in P}\frac{\Delta(n;u-\log p)^b}{p}
 \le\frac{8e+336}{\log Y}\,2^bM_b(n),
\]

and, after multiplying by \(\Delta(n;u)^a\) and integrating,

\[
 \sum_{p\in P}\frac1p
   \int\Delta(n;u)^a\Delta(n;u-\log p)^b\,du
 \le\frac{8e+336}{\log Y}\,2^bM_a(n)M_b(n).                     \tag{L3}
\]

These inequalities have **no short-interval remainder**. The extra
\(2^b\) in the main term is absorbed because

\[
 \sum_{1\le b\le q/2}2^b\binom qb m_bm_{q-b}\le\frac{m_q}{CAL}.
\]

For each summand its ratio after multiplication by \(CAL\) to \(m_q\)
is \(2^b/\binom qb^2\le1/q\), using
\(\binom qb\ge q\) and \(\binom qb\ge2^b\) on this half range.
The latter follows from \(\binom{2b}b\ge2^b\) and monotonicity in
the upper index. Also \(A m_q\le(q^3CAL)^q\).

Use (L3) in the induction of Section 11.2 with \(Y=\sqrt y\).
The same principal-term calculation proves
\(T_q(x)\le C m_q\operatorname{Log}x/(q^2A)\), and there is now no
\(R_q\) term to estimate. The base case still gives
\(T_2(x)\ll L\operatorname{Log}x\), since \(m_2=8CAL\).
The weak threshold becomes \(O(AL^4)\), and dyadic summation gives

\[
 \sum_{n\le X}\frac{\Delta(n)}n
       \ll\operatorname{Log}X\,(\operatorname{Log}_2X)^5.
\]

In the square-location argument this corresponds to \(c_0=5\):
the progression mean, quadratic mean, and nearby mean have exponents
6, 7, and \(9/2\). The noncritical error ratio is
\(\ell^{-5+7/2+1}=\ell^{-1/2}\); in the critical case the error is
\(O(T^{1/4}\ell^{9/2})\), below the \(T^{1/4}\ell^9\) main term.
The final \(N^{1/3}(\operatorname{Log}_2N)^{16}\) target is unchanged.

`HooleySmoothEnvelope`, `HooleySmoothedMean`, `HooleyPrimeIntervals`,
and `HooleyPrimeMean` implement the new envelope, generic finite smoothing,
prime-window bound, and (L3). The restricted-moment induction and its
prime-prefix exceptional-set argument now also compile; the resulting
weak mean estimate is `deltaSmooth_weak_mean` in `HooleyWeakMean.lean`.
The strong harmonic mean, including squarefull removal and the closed
upper endpoint, is now proved in `HooleyHarmonicMean.lean`. The
short-progression transfer is proved in `HooleyProgressionGcd.lean`.
The quadratic mean improvements, full-width extraction, and final
log-log upper-bound theorem remain unfinished.

### 11.6. Integer square-root iteration and the checked weak bound

The Lean implementation uses an integer square-root cutoff, avoiding a
continuous cutoff integral. For every integer \(x\ge4\), put
\(y=\lfloor\sqrt x\rfloor\). Then

\[
 2\le y<x,\qquad 2\log y\le\log x\le4\log y.
\]

Fix an ambient prime cutoff \(X\), \(A\ge1\), and a budget \(L\ge1\)
satisfying \(\sum_{p<X}1/p\le L\). Let \(G\) be a downward-closed
restriction containing 1, with
\(\tau(n)\le VA\log x\) whenever \(n\in G\) is squarefree and all
its prime factors are below \(x\), for \(2\le x\le X\).
Write \(m_q=(q!)^3(CAL)^{q-1}\), and let \(T_q(x)\) be the harmonic
sum of \(M_q(n)/\tau(n)\) over these integers subject to the moment
constraints through order \(q-1\).

Largest-prime decomposition gives a finite Volterra inequality with
mixed-moment error \(E_q(x)\). Set \(Q_q(x)=1+E_q(x)\). For \(q\ge3\),
the lower-order induction hypotheses and (L3) yield

\[
 E_q(x)-E_q(y)
 \le \frac{16(8e+336)V m_q}{A L q^2}\log x.
\]

The small cutoffs 2 and 3 satisfy
\(Q_q(x)\le1+2^q\le3m_q/(q^2CAL)\). Thus integer strong induction gives

\[
 Q_q(x)\le H(V)\frac{m_q\log x}{ALq^2},\qquad
 H(V)=\frac3{\log2}+32(8e+336)V.
\]

At order two, the mixed sum is just four times the harmonic divisor sum,
which is \(O((\log x)^2)\) by the exact Euler product and Mertens.
The same square-root iteration proves \(Q_2(x)\ll\log x\).
The Mertens-weighted Volterra bound then gives

\[
 T_q(x)\le \frac{C m_q\log x}{Aq^2}
\]

for one constant \(C\), simultaneously for all moment orders and all
cutoffs below \(X\). The summability of \(1/q^2\) bounds the harmonic
mass discarded by the moment restrictions by \(C\log X/A\).

For the base restriction \(G\), order the primes below \(X\) and impose
at every prefix \(P_k\) the constraint

\[
 2^{|\{p\mid n\}\cap P_k|}
 \le A\prod_{p\in P_k}\frac{1+2/p}{1+1/p}.
\]

This is downward closed. The product is at most
\(\prod_{p\in P_k}(1+1/p)\), hence at most \(V\log x\) at a
prime cutoff \(x\). The weighted binary-choice maximal inequality
shows that the discarded reciprocal mass is at most
\(A^{-1}\prod_{p<X}(1+1/p)\le V\log X/A\).
The identification of binary choices with squarefree prime products,
including their exact reciprocal weights and prefix values, is checked
in `HooleyPrimeChoices` and `HooleyPrimeCaps`.

If also \(\log\log X\le L\), choose \(q=\lceil L\rceil\).
For one constant \(R>0\), \(V\log X\le R^q\), and on the retained set
the concentration inequality and envelope imply
\(\Delta(n)\le2R q^3CAL\ll AL^4\).
Consequently there are absolute constants \(K,D>0\) such that

\[
 \sum_{\substack{n\ \mathrm{squarefree},\ P^+(n)<X\\
                  \Delta(n)>KAL^4}}\frac1n
       \le\frac{D\log X}{A},\qquad A\ge1.
\]

This finite smooth-number weak bound is proved in Lean without an
analytic assumption.

### 11.7. Checked strong harmonic mean and squarefull removal

The generic finite dyadic lemma `finite_delta_weak_to_strong` proves

\[
 \sum_n f(n)w(n)\le T\sum_n w(n)+kTM+
                  \frac{\sum_n f(n)^2w(n)}{T2^k}
\]

whenever \(w\ge0\) and
\(\sum_{f(n)>T2^j}w(n)\le M/2^j\) for \(j<k\).
Apply it with \(T=KL^4\), \(M=D\log X\), and
\(k=\lceil4L/\log2\rceil\). Then \(k=O(L)\) and
\(2^k\ge(\log X)^4\). The exact divisor-square Euler product bounds
the weighted second moment by \(O((\log X)^4)\), so the tail is bounded
by an absolute constant. This proves the squarefree smooth harmonic
mean \(O(\log X\,L^5)\).

The bounded-error Mertens estimate supplies
\(L=\max(1,\log\log X+C_0)\), which is
\(O(\max(1,\log\log X))\). For a general integer, write \(n=ab\),
where \(a\) contains exactly the prime powers of exponent at least two
and \(b\) contains the exponent-one primes. The repository's Ford
development already proves this decomposition and
\(\sum_{a\text{ squarefull}}\tau(a)/a\ll1\). Combining them with
\(\Delta(ab)\le\tau(a)\Delta(b)\) gives

\[
 \sum_{n\le X}\frac{\Delta(n)}n
 \ll\log X\,\max(1,\log\log X)^5\qquad(X\ge2).
\]

This is `Erdos587.exists_hooleyDelta_harmonic_loglog_bound`. Its complete
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
No resource limits have been raised. The harmonic theorem alone does not
imply uniform short-progression transfer; the separate sieve argument
completing that step is recorded in §§11.8–11.9.

For that next step, `HooleyAffineCoefficients.lean` proves exact
recentering into \((Y,2Y]\), preservation of primitivity, and coefficient
bounds \(|B|\le2X\), \(|A|\le3X\), and \(|A-BY|\le7X\) from the
endpoint value bounds, when \(Y\ge2\). `HooleyGrowth.lean` proves the
two growth majorants required by the transfer, including
\(\Delta(ab)\le\min(2^{\Omega(a)},C_\varepsilon a^\varepsilon)\Delta(b)\)
without a coprimality assumption, and the constant divisor bound for a
rough cofactor in a fixed-power size range.

### 11.8. Checked Rankin tails and fixed-divisor sieves

For a nonnegative exponent, put \(g_\beta=(n\mapsto n^\beta)*\mu\).
The new Rankin modules prove multiplicativity, nonnegativity, and
\(\sum_{d\mid n}g_\beta(d)=n^\beta\). The local Euler estimate is

\[
 \sum_{k\le m}\frac{\tau(p^k)g_\beta(p^k)}{p^k}
 \le 1+20\frac{p^\beta-1}{p},\qquad 0\le\beta\le\tfrac12.
\]

Weighted Mertens gives an absolute \(D>0\) such that, when
\(\beta\log z\le M\), the product of these factors over primes at most
\(z\) is at most \(\exp(20DM e^M)\). Expanding the divisor twist and
using \(\Delta(dm)\le\tau(d)\Delta(m)\) gives, for fixed \(M\ge0\),

\[
 \sum_{\substack{T\le n\le N\\P^+(n)\le z}}\frac{\Delta(n)}n
 \ll_M \log N\,\max(1,\log\log N)^5
           \exp\!\left(-M\frac{\log T}{\log z}\right),
 \qquad 2M\le\log z.
\]

This is `exists_delta_smooth_harmonic_tail_bound` in
`HooleySmoothTail.lean`; its statement also allows any subset of that
range. There is no squarefree restriction.

For primitive signed coefficients \(A,B\), the large sieve already
proved in the repository supplies a uniform rough-value count. On a
fiber \(d\mid A+Bt\), recentering at its least index and dividing the
index differences by \(d\) leaves slope \(B\), not \(Bd\). If
\(dQ^2\le Y\), the checked result is

\[
 \#\{1\le t\le Y:d\mid A+Bt,\ p\nmid(A+Bt)/d
                         \text{ for every prime }p\le Q\}
 \le \frac{3|B|}{\varphi(|B|)}\frac{Y}{d\log(Q+1)},
\]

where the exclusion condition means that no prime at most \(Q\)
divides the integer quotient \((A+Bt)/d\).
The precise statement is `delta_affine_divisor_fiber_card_le_three`.

The Delta growth inequality does not need coprimality. Accordingly,
`HooleyPrimePrefixSplit.lean` splits the sorted prime-factor list with
repetitions, instead of splitting only at whole prime powers. For
\(n>R^2\), it gives \(n=ab\) and a next prime \(p\) with

\[
 a\le R^2<ap,\qquad P^+(a)\le p\le P^-(b).
\]

If \(p>R\), the cofactor is uniformly rough. Otherwise \(a>R\),
so the smooth-prefix harmonic sum has the Rankin saving. This removes
the separate large-prime-power exceptional case from the general
Nair--Tenenbaum argument. The prefix split, Rankin tail, and signed
fixed-divisor sieve have all passed the axiom audit with only the three
standard axioms. The subsequent prime-scale summation and transfer are
now also checked, as recorded next.

### 11.9. Checked uniform short-progression transfer

Choose an integer \(R\ge2\) with \(R^4\le Y\) and suppose that the
absolute affine values are at most \(N\le(R+1)^k\), with fixed \(k>0\).
The prime-prefix split gives three finite covering ranges.

In the main range, \(a\le R^2\) and every prime factor of the cofactor
\(b\) exceeds \(R\). Thus \(\tau(b)\le2^k\). Apply the divisor-fiber
sieve with cutoff \(R\), and sum \(\Delta(a)/a\) using the harmonic
mean. Since \(\log N/\log(R+1)\le k\), this range contributes
\(O_k((|B|/\varphi(|B|))Y\max(1,\log\log N)^5)\).

For the other ranges, the prefix has \(R<a\le R^2\) and a next prime
\(p\le R\), with \(P^+(a)\le p\le P^-(b)\). Put

\[
 j=\left\lfloor\frac{\log R}{\log p}\right\rfloor,\qquad
 z_j=\left\lfloor e^{\log R/j}\right\rfloor,\qquad
 Q_j=\left\lfloor e^{\log R/(j+1)}\right\rfloor.
\]

Then \(1\le j\), \(Q_j<p\le z_j\), \(Q_j^2\le R\),
\(\log(Q_j+1)>\log R/(j+1)\), and \(j\log z_j\le\log R\).
The rough divisor count is at most
\(\exp((\log2)\log N/\log(Q_j+1))\).
Choose the fixed Rankin parameter \(M=2k+2\). When
\(2M\le\log z_j\), the smooth-prefix tail and the divisor-fiber sieve
give a contribution at most

\[
 C_k\frac{|B|}{\varphi(|B|)}Y\max(1,\log\log N)^5 e^{-j}.
\]

The checked algebra uses \(\log N\le2k\log R\): the exponential
cofactor cost is at most \(2k(j+1)\), while the Rankin saving is at least
\((2k+2)j\). The additional factor \(j+1\) from the sieve denominator
is absorbed by \(j+1\le e^j\). The finite sum of \(e^{-j}\) is at
most 2.

For primes at most the fixed cutoff
\(W_k=\max(2,\lceil e^{2M}\rceil)\), use \(\beta=1/2\) in the
Rankin twist and the sieve cutoff 1. The divisor bound
\(\tau(b)\ll_k b^{1/(8k)}\), together with
\(\log N\le2k\log R\), leaves a factor
\((\log R)e^{-\log R/4}\), which is uniformly bounded. This includes
all repeated-prime cases without an exceptional prime-power argument.

`HooleyProgressionCover.lean` proves that these ranges cover every
positive integer. `HooleyProgressionMean.lean` sums the non-disjoint
cover. Taking \(R=\lfloor Y^{1/4}\rfloor\), implemented as two integer
square roots, removes the auxiliary scale. The proved maximal-order
totient estimate absorbs the slope factor using
\(|B|\le2N\le N^2\), obtained from the endpoint bounds. Finally,
dividing the coefficients by their gcd and applying the unrestricted
Delta multiplication inequality gives

\[
 \sum_{t=1}^{Y}\Delta(|A+Bt|)
 \ll_r \tau(\gcd(A,B))\,Y\max(1,\log\log N)^6,
 \quad B\ne0,\quad Y\ge16,\quad 2\le N\le Y^r,
\]

whenever all the absolute affine values are at most \(N\). A zero value
is allowed and contributes zero. The exact theorem is
`Erdos587.exists_hooleyDelta_progression_mean` in
`HooleyProgressionGcd.lean`. Its complete axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`; no resource limits were
raised. This completes the short-progression input with \(c_0=5\),
but does not yet prove the downstream quadratic means or final upper bound.

### 11.10. Checked inputs for the quadratic mean improvement

`HooleyGcdMean.lean` completes the nonzero-error gcd estimate in its
real-tolerance form. For any finite set of nonzero integers with
\(|t|\le T\), including \(0\le T<1\), it proves

\[
 \sum_t\tau(\gcd(q,|t|))
 \ll T\max(1,\log\log q),\qquad q>0.
\]

The proof uses the exact positive-error divisor identity, the bound
\(\sum_{d\mid q}1/d\le q/\varphi(q)\), and an injective signed
cover. There is no additive \(\tau(q)\) term.

`HooleyChirpDecay.lean` and `HooleySignedChirpDecay.lean` prove, for each
fixed Schwartz weight \(f\), the uniform envelope

\[
 \left|\widehat{f(x)e(Ax^2)}(\xi)\right|
 \le \frac{C_f}{\sqrt{1+|A|}}
          \left(1+\frac{|\xi|}{1+|A|}\right)^{-2}
 \qquad(A,\xi\in\mathbb R).
\]

For bounded \(A\), this follows from the existing uniform Schwartz
seminorm theorem. For \(A\ge1\), the exact Fresnel identity and the
uniform profile estimate give both scales simultaneously. Complex
conjugation supplies negative \(A\).

`HooleyShiftedLattice.lean` proves the uniform bound
\(\sum_{n\in\mathbb Z}(1+\sigma|n-\theta|)^{-2}\le41\) for
\(\sigma\ge1/4\), together with summability. Rounding \(\theta\) to
its nearest integer isolates one point, and every other point is
controlled by a fixed unshifted decay kernel.

These inputs and the already proved Gauss bound and Poisson identity
give `exists_delta_smooth_major_arc_sq_bound` in `HooleyMajorArc.lean`:

\[
 \left|\sum_{n\in\mathbb Z}f(n/K)
       e((a/q+\beta)n^2+\theta n)\right|^2
 \ll_f \frac{K^2}{q(1+K^2|\beta|)},
 \quad 1\le q\le K,\quad (a,q)=1,\quad
 |\beta|\le\frac2{qK}.
\]

It is uniform in the real linear phase and both signs of \(\beta\).
`HooleySchwartzFamily.lean`, `HooleyUniformChirp.lean`, and
`HooleyUniformMajorArc.lean` now extend this to a single constant for
every weight in a bounded subset of Schwartz space. The product
derivative bound is controlled by finitely many input seminorms;
bounded chirp multipliers preserve bounded families, and continuous
Fourier and conjugation operators preserve those bounds. This supplies
the needed uniform-weight-family packaging. The centered mean is now
assembled in §11.11, and the reciprocal mean in §11.12.

`HooleyApproximationCount.lean` now proves the centered encoding's exact
fiber estimate. A finite family of triples \((m,b,h)\), with \(m>0\)
and \(B<b\le2B\), is sent to \((t,n)=(amb-qh,mb)\). In a fixed
fiber, \(b\) determines \(m\) and \(h\), so its cardinality is at most
\(\Delta(n)\). Thus the total cardinality is bounded by the sum of
\(\Delta(n)\) over the corresponding residue progressions.

`HooleyResidueProgression.lean` and `HooleyLinearResidue.lean` reindex
those residue classes into the checked short-progression theorem, with
the exact factor \(\tau(\gcd(q,|t|))\). Consequently
`HooleyApproximationShell.lean` proves, for any fixed positive integer
\(r\), that a family of these triples with \(mb\le X\) and
\(0<|amb-qh|\le T\) has cardinality

\[
 \ll_r \frac Xq\,T\max(1,\log\log X)^7,
 \qquad 16\le\lfloor X/q\rfloor,\quad
 X\le\lfloor X/q\rfloor^r.
\]

For the complementary range, `HooleyApproximationSmallShell.lean`
proves, for every fixed \(\epsilon>0\), the bound

\[
 \ll_\epsilon (X/q+1)\,T X^\epsilon,
\]

without either size restriction. Both bounds are uniform in the
coprime coefficients and the denominator block. In particular neither
introduces an additive zero-error term. All four new modules compile,
and their theorem axiom audits report only Lean's standard axioms.

### 11.11. Checked centered smooth quadratic mean

`HooleyCenteredMean.lean` now proves the centered mean itself, uniformly
over every bounded subset of Schwartz space. For each fixed
\(\kappa>0\), it gives

\[
 \sum_{m=1}^{M}|S_m-B_m|^2
 \ll_\kappa MK\max(1,\log\log X)^7,
 \quad M,q\ge1,\quad K\ge1,\quad(a,q)=1,
 \quad 2MK\le X,\quad qX^\kappa\le MK.
\]

Here \(S_m=\sum_n f_m(n/K)e(am n^2/q)\), and the retained term is
exactly \(B_m=K G(am;q)\widehat f_m(0)/q\). The final Lean theorem is
`Erdos587.exists_delta_smooth_centered_mean`.

The proof chooses reduced Dirichlet approximants and excludes zero
errors before counting. `HooleyDyadicShell.lean` sums the tolerance
shells. `HooleyDenominatorBlocks.lean` gives the exact geometric cost
\(\sum_{j=0}^D 2^j(D-j+3)\le8\cdot2^D\), so summing denominator
blocks adds no harmonic logarithm.

To make the short-range absorption explicit, put \(N=M2^D\), with
\(K\le2^D\le2K\), and choose
\(Y=16+\lceil N^{1/r}\rceil\). Then \(N\le Y^r\). Splitting
the product scale at \(qY\) allows the short-progression mean above
the split and the subpower divisor estimate below it. With divisor
exponent \(1/r\), the total short-range cost is

\[
 \ll_r qN^{1/r}(2Y+D+1)(D+3)
 \ll_r qN^{3/r}.
\]

The last estimate is checked directly using
\(\log N\le rN^{1/r}\); it needs no asymptotic exception. Choose
\(r\) with \(3/r\le\kappa\), and the stated power separation
absorbs this cost into \(N\).

For exact reduced denominators at most \(K\), the centered Poisson
identity and the nonzero-lattice tail bound
\(\sum_{n\ne0}(1+\sigma|n|)^{-2}\le20/\sigma^2\) give a squared
error \(O(K)\). Above \(K\), the retained zero mode also has squared
size \(O(K)\). `HooleySmoothReduction.lean` proves that dividing out
the numerator/modulus gcd preserves both the exact mean and centered
error. Thus the complete-period contribution is never treated as a
divisor-weighted error.

The full centered-mean module builds at the default resource limits.
Its complete axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`. The reciprocal and nearby means are now also checked
below. The terminal locator, full-width extraction, and final assembly remain.

### 11.12. Checked reciprocal smooth quadratic mean

`HooleyReciprocalMean.lean` proves the full reciprocal mean, uniformly over
bounded Schwartz families and arbitrary varying linear phases. Fix positive
integers \(a,c\) and \(\kappa>0\). If \((q,v)=1\), \(q\le X\),
\(K\ge1\), \(R>0\), and

\[
  2K\le X,\qquad aK<q,\qquad avK+16cqR\le X,
  \qquad KX^\kappa\le R,
\]

then, for every finite \(I\subset(R,2R]\) and integer lifts \(A_m\)
satisfying \(cm\mid qA_m-av\),

\[
 \sum_{m\in I}\left|\sum_{n\in\mathbb Z}f_m(n/K)
 e\!\left(\frac{A_m}{cm}n^2+\theta_m n\right)\right|^2
 \ll_{a,c,\kappa} RK\max(1,\log\log X)^7.
\]

The final theorem is `Erdos587.exists_delta_smooth_reciprocal_mean`.
It is unconditional: the inverse congruence and all scale hypotheses are
explicit, and no Fourier truncation or partial-summation loss is used.

For a reduced approximant \(h/b\), write \(t=bA_m-cmh\).
The congruence implies \(cm\mid bav-qt\). This encoded integer is
nonzero because \(b\le K\), \((q,v)=1\), and \(aK<q\), even
when \(t=0\). Fixed-error fibers inject into divisors in
\((cR,2cR]\), so their sizes are bounded by Hooley's Delta function.
The signed short-progression theorem bounds the error sum with the exact
factor \(\tau(\gcd(q,ab))\). Its weighted denominator sum costs only
one additional log-log factor.

For the short progressions, choose \(Y=16+\lceil X^{1/r}\rceil\).
The affine shell-count lemma retains the additive counting error without
multiplying it by the number of shells. After summing denominators with
\(2cRb/K^2<Y\), the total cost is

\[
 \ll_r K^2(Y+2)(D+3)X^{1/r}
 \ll_r K^2X^{3/r},\qquad K\le2^D\le2K\le X.
\]

Choosing \(3/r\le\kappa\) absorbs this into \(RK\). Every
inequality is checked for the stated finite ranges, without an unspecified
large-parameter exception. Both quadratic-mean roots build successfully at
default limits, and the reciprocal theorem's complete axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

### 11.13. Checked complete nearby mean

`HooleyNearbyMean.lean` proves `Erdos587.exists_delta_nearby_mean`.
For fixed Schwartz weight \(f\) and \(\kappa>0\), the full norm sum
is bounded by

\[
 \sum_{m=1}^M |S_m-B_m|
 \ll_{f,\kappa} M\sqrt L\max(1,\log\log X)^{9/2}.
\]

All finite scale conditions are explicit: \(u,v>0\),
\((a,u)=(u,v)=1\), \(u\mid av+1\), \(X\ge2\), \(u\le X\),
\(L\ge1\), \(M_0=\lfloor uv/L^2\rfloor\le M\), and

\[
 4LX^\kappa\le v,\qquad 4ML\le uv,\qquad
 (4L+16u)M\le X.
\]

The remainder is the existing exact `nearbyQuadraticRemainder`, so its
complete-period integral term has not been omitted. Below the cutoff,
the bounded chirp family enters the checked centered mean directly.
The upper cutoff inequality and \(4LX^\kappa\le v\) imply the low
mean's power separation whenever \(M_0>0\); the zero cutoff is handled
as an empty sum.

`HooleyAffineSchwartz.lean` proves uniform seminorm bounds for compact
translations and dilations between \(1/2\) and \(2\), and packages
the Fresnel profiles as a bounded Schwartz family. The reciprocal mean
then applies directly to the full series. The existing exact Gauss
reciprocity identity treats both parity classes with denominator \(r\).
This is a convenient alternative to the three parity cases in §6.

On each closed dyadic block \(R\le r\le2R\), use the real dual width
\(K=2RL/v\). The global conditions above imply every local reciprocal
mean hypothesis. Cauchy–Schwarz gives \(R\sqrt L\,D_{7/2}(X)\).
The short dual widths have the already checked pointwise
\(O(\sqrt L)\) bound. Finally, `HooleyGcdBlocks.lean` improves the
gcd/dyadic cover's mass to \(O(M\operatorname{Log}_2X)\), using
\(\sum_{d\mid u}1/d\le u/\varphi(u)\). This yields exactly
the exponent \(9/2\).

The complete nearby mean builds at the default resource limits and its
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
The critical terminal specialization is checked in §11.14 and the
complete primitive terminal theorem in §11.15. Structural assembly is
not yet complete.

### 11.14. Checked critical terminal branch

`HooleyNearbyPowerScale.lean` checks every finite margin using
\(x=T^{1/40}\) and the integer ambient cutoff
\(X=\lfloor x^{40}\rfloor\). `HooleyCriticalScale.lean` specializes
the nearby mean uniformly to the critical progression parameters, including
a power-enlarged frequency cutoff. The coefficients may have any fixed
additional logarithmic cutoff factor; this is absorbed into a positive
power margin and does not enter the resulting log-log loss.

The weighted prefix argument, summable power tail, conjugation symmetry,
and zero-mode bound give `exists_delta_critical_full_error` in
`HooleyCriticalError.lean`: the entire signed Fourier error is
\(O(T^{1/4}\operatorname{Log}_2(T)^{9/2})\). No frequency range is
discarded without a bound.

The main term now has the matching sharp density input.
`HooleyRootEuler.lean` identifies the inverse Euler density exactly as
\(Q/\varphi(Q)\). The already checked Burgess-based density threshold
then combines with the totient bound, including both parity cases, to give
`exists_delta_complete_root_density`:

\[
 \sum_{i=0}^{H-1}\rho_q(D+Ri)
 \ge \frac{H}{C\operatorname{Log}_2 X},\qquad
 (R,q)=1,\quad q\le X,\quad H\ge A\sqrt q.
\]

Consequently the critical alternative main term is at least
\(HJ/(C\sqrt T\operatorname{Log}_2 T)\). The finite root-window
family and exact Fourier comparison yield a positive square whenever
\(HJ>K T^{3/4}\operatorname{Log}_2(T)^{11/2}\), with the explicit
root-density width condition. This is
`exists_delta_critical_square_of_main_budgets`.

Finally, `HooleyCriticalTerminal.lean` proves
`exists_delta_critical_primitive_terminal`: for each fixed span constant,
the critical branch satisfies the terminal conclusion with the fixed
tenth powers from (12). Its assumptions include
\(u\ge T^{1/16}\) and \(J\le T^{1/4+1/1000}\). The other
branches and the complete primitive terminal theorem are checked in
§11.15.

The entire critical terminal root builds at default limits. Axiom audits
of the new root-density, count-comparison, square-budget, and terminal
theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
The final \(N^{1/3}\operatorname{Log}_2(N)^{16}\) theorem is still
unassembled.

### 11.15. Checked power-separated and complete primitive terminals

`HooleyCenteredWeighted.lean` sums the centered mean against quadratic
frequency decay, with an enlarged base cutoff. The full-series argument
uses
\[
 M=\left\lfloor\frac{T^{1/4}}{\operatorname{Log}_2(T)^6}\right\rfloor,
 \quad N=\lfloor T^2\rfloor,\quad X=\lfloor T^8\rfloor,
 \quad \kappa=1/100000.
\]
This uses a sixth power in the cutoff rather than the fifth power in
§7.1, allowing the mean loss \(7/2\) to be rounded up to 4 while
retaining a log-log margin. The final exponents 10 and 16 are unchanged.
`HooleyWideScale.lean` proves the finite centered-mean hypotheses, and
`HooleyWideTail.lean` bounds the entire Schwartz tail beyond \(N\) by
\(T^{-2}\). Conjugation and the exact zero-frequency bound give
`exists_delta_wide_full_error`:
\[
 \sum_{m\in\mathbb Z}|\sigma\widehat g(\sigma m)(S_m-B_m)|
 \ll \sigma M T^{1/4}\operatorname{Log}_2(T)^4,
 \qquad \sigma=H/q.
\]

`HooleyPeriodicMain.lean` retains all Fourier main terms and identifies
the count-minus-main series exactly. The physical periodic density is
bounded below by \(H/(Cq\operatorname{Log}_2 q)\), and the fixed
root-window plateau has a uniformly positive integral.
`HooleyWideSquare.lean` combines these bounds to produce an actual
positive square. The comparison is strict because
\(K M\operatorname{Log}_2(T)^5<T^{1/4}\) eventually for every fixed
\(K>0\).

`HooleyWideTerminal.lean` discharges the density and frequency budgets
from the tenth-power side and area assumptions. Finally,
`HooleyPrimitiveTerminal.lean` combines the wide, critical, and existing
small-step branches, including interchange of the two coordinates.
The resulting `exists_delta_primitive_terminal_unoriented` has the
fixed thresholds
\[
 H,J\ge T^{1/4}\operatorname{Log}_2(T)^{10},\qquad
 HJ\ge T^{3/4}\operatorname{Log}_2(T)^{10}.
\]
The complete primitive terminal root builds at default limits, and its
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
The common-factor extension is checked in §11.16. Full-width structural
extraction remains; this is not yet a Lean proof of the final upper bound.

### 11.16. Checked common-factor and structural terminal interfaces

`HooleyCommonFactorScales.lean` proves that the existing exact
common-factor subrectangle extraction loses at most one log-log power.
`HooleyCommonFactorTerminal.lean` treats both the nonprimitive long-side
case and the primitive subrectangle case, with the fixed exponent 11.
The common factor is restored in the actual square witness.

`HooleyHomogeneousTerminal.lean` removes the need for a chosen common
factorization. For every fixed span constant, a sufficiently large
homogeneous proper rank-two progression with maximum \(T\) contains a
positive square provided its sides and area satisfy
\[
 H,J\ge T^{1/4}\operatorname{Log}_2(T)^{11},\qquad
 HJ\ge T^{3/4}\operatorname{Log}_2(T)^{11}.
\]
`HooleyStructuralTerminal.lean` applies this result, and the elementary
rank-one square criterion, to a general homogeneous subset-sum GAP with
explicit side, cardinality, and quartic numerical budgets.

All these roots compile at default resource limits and their axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`. The analytic
locator is complete. The full-width structural extraction and final
exponent-16 numerical assembly are not yet proved in Lean.

### 11.17. Checked geometric components for full-width extraction

The structural development now has the following unconditional components,
all at default Lean resource limits:

- `HooleyConvexQuotient.lean` lifts every lattice point of the
  \((1-\eta)\)-shrunken primitive quotient back into the original body,
  when the primitive kernel vector lies in \(\eta B\), for
  \(0\le\eta\le1\). It also proves the corresponding evaluation-image
  inclusion and injectivity on the half-sized body once short kernel
  vectors have been excluded.
- `HooleyRobustSpanning.lean` preserves robust linear spanning under
  surjective linear maps and bounds the number of nonzero values of any
  nonzero linear functional.
- `HooleyCubeFiber.lean` and `HooleyFractionalCoefficients.lean` use a
  compact cube-fiber extreme point to preserve a vector sum with at most
  \(d\) fractional coefficients. `HooleySubsetRounding.lean` then rounds
  to an actual subset sum with coordinate error at most \(dL_i\).
- `HooleyZonotopeRounding.lean` rounds the zonotope center to an integer
  vector, incurring at most an additional \(1/2\) in each coordinate.
  This provides an alternative to the parity deletion in §1.2.
- `HooleyLatticeRounding.lean` proves that a projected cube is a rounding
  cell. If the rounding error lies in \(B/4\), a real linear functional
  on \(B\) is bounded by twice its bound on the lattice points of \(B\).
- `HooleyZonotope.lean` constructs a support point \(x\in Z\) with
  \(\ell(x)=\frac12\sum_u|\ell(u)|\), in the form needed for
  coordinate first-moment bounds.
- `HooleyBoxMass.lean` proves the finite substitute for the volume lower
  bound: if \(A\subset\mathbb Z^d\), \(m=|A|>0\), \(d>0\), and
  \(m\le B_i\), \(\sum_{a\in A}|a_i|\le B_i\), then
  \[
    m^{d+1}\le2(9d)^d\prod_i B_i.
  \]
  The proof removes coordinate outliers and counts the remaining lattice
  points in a box. In combination with robust spanning and the support
  identity, this can replace the Brunn–Minkowski step in §1.4.
- `HooleyInnerBox.lean` constructs an actual inner GAP from the existing
  adapted **lattice basis**, with radii
  \(\lfloor b_i/\mathrm{scale}\rfloor\). It proves containment,
  properness, and homogeneity when the convex progression has those
  properties. The basis is a basis of the whole coefficient lattice;
  no unproved index inference is used.
- `HooleyWeakStability.lean` obtains a weakly deletion-stable subset for
  one high-fold sumset. Allowing a polynomial stability factor makes the
  number of deletion rounds constant. `HooleyHyperplaneCount.lean` and
  `HooleySpanningCriterion.lean` give the associated lattice-box criterion
  for full real span.
- `HooleyAdaptedMass.lean` bounds each adapted coordinate's first moment
  by \(4b_i/\delta\) when \(\delta Z_U\subseteq B\). Robust spanning
  gives \(|U|\le8b_i/\delta\). `HooleyInnerRadius.lean` explicitly
  handles the floors and ceilings needed to turn these into integer
  side-length bounds.
- `HooleyFullWidthBox.lean` and `HooleyConvexExtraction.lean` now combine
  these ingredients. For a proper convex progression of rank \(d>0\),
  a robustly spanning set \(U\) of size \(m>0\), a quarter-body rounding
  cell, and \(\delta Z_U\subseteq B\), assume
  \(16\cdot4^d\le\delta m\), an integral homogeneous center, and
  \(\mathrm{base}\le C\sum_{u\in U}\mathrm{eval}(u)\), with
  \(C\ge0\). Set
  \[
    K=\left\lceil32\cdot4^d/\delta\right\rceil,
    \qquad F=9dK.
  \]
  The extracted inner GAP \(Q\) is proper and homogeneous, has the same
  rank, and satisfies
  \[
    m\le F L_i,\qquad
    m^{d+1}\le2F^d|Q|,\qquad
    \max Q\le(CK+1)\operatorname{span}(Q).
  \]
  The last estimate is checked in `HooleyBasisSpan.lean`.
- `HooleyConvexBody.lean` derives full lattice span from radial fullness
  and a quarter-body rounding cell, and constructs the corresponding
  convex-progression record. This is the interface needed for shrunken
  quotient bodies.

All components above compile at default limits and pass the standard-axiom
audit. Quotient iteration and the combined geometric extraction are now
checked in §11.18. The arbitrary-set seed and final assembly remain.

### 11.18. Checked inner quotient iteration and combined extraction

`HooleyBodyDilate.lean` and `HooleyShrunkenQuotient.lean` construct actual
shrunk convex progressions. `HooleyShortKernel.lean` normalizes a short
kernel vector to a primitive vector without enlarging its gauge.
`HooleyInnerQuotient.lean` records the exact linear projection, evaluation
identity, body image, homogeneous-center preservation, and carrier
containment.

`HooleyQuotientIteration.lean` completes the finite rank induction. If a
surjective integral map projects the half-unit cube into
\(4^{-(d+2)}B\), the iteration gives a proper inner progression with
body
\[
  B'=c\,q_{\mathbb R}(B),\qquad 4^{-(d+1)}\le c\le1.
\]
It retains a quarter-body rounding cell and exact inner carrier
containment. `HooleyQuotientTransfer.lean` preserves robust spanning and
the zonotope under the accumulated quotient, and preserves cardinality
when evaluation is injective on the original vector set.

`HooleyRobustConvexExtraction.lean` combines the iteration with §11.17.
The starting convex progression need not be proper. With
\(\delta_0=\delta/4^{d+1}\),
\(K=\lceil32\cdot4^d/\delta_0\rceil\), and \(F=9dK\), the
output has rank between 1 and \(d\), the same side/cardinality/height
bounds as §11.17, and lies in the original carrier. Its size hypothesis
is \(16\cdot4^d\le\delta_0|U|\). Nonzero evaluation excludes
rank zero. These roots compile and pass the standard-axiom audit.

### 11.19. Checked seed-body and robust-model interfaces

`HooleyOneSidedCenter.lean` chooses an integral center \(c\) satisfying
\[
  \left|c_j-\frac12\sum_u u_j\right|\le\frac12,
  \qquad f(c)\le\frac12\sum_u f(u).
\]
The floor or ceiling of each half-integer coordinate is chosen according
to the sign of the evaluation map's coefficient. This avoids an
uncontrolled upward rounding error in the height bound.

`HooleySeedBody.lean` constructs the centered zonotope plus a rectangular
cushion. Its lattice decomposition expresses each point about \(c\)
as a genuine subset sum plus an integer error of coordinate size at most
\(R_j+dL_j+1/2\). `HooleySeedProgression.lean` turns a lattice seed
covering that error box, disjoint from the remaining elements, into an
actual convex subset-sum progression, including its base-mass estimate.

The stability input now also handles large relative deletions. The new
relative version in `HooleyWeakStability.lean` retains at least
\(3^{-(2b+2)}\) of the input, and is weakly stable under passage to
every subset containing at least a third of what remains. This relative
version, rather than a fixed deletion budget alone, supplies the robust
spanning requirement of the geometric stage.
`HooleyWeakHighFoldModel.lean` combines it with uniform high-fold
doubling: under its explicit power-scale inequalities, it constructs a
constant-rank coordinate model and proves finite coordinate-lattice
index, with full real span, for every such large subset.
`HooleyFiniteIndexSpan.lean` supplies the index-to-span implication.
All these roots compile and pass the standard-axiom audit.

The remaining seed assembly must connect the coarse coordinate seed,
residue completion, and adapted lattice coordinates described below,
including all width and deletion budgets. The final exponent-16 assembly
is still outstanding.

### 11.20. Checked coarse seed, residue reserve, and lattice coordinates

`HooleyCoordinateCover.lean` covers a coefficient box dilated by \(c\)
with at most \(c^d\) translates of the original box.
`HooleyCoordinateCoverFiber.lean` gives the finite-group fiber-counting argument.
`HooleyCoordinateFiber.lean` and `HooleyCoordinateBlocks.lean` combine
these with greedy growth to extract disjoint blocks of actual coefficient
vectors. Their translated dense fibers retain exact subset-sum provenance
in \(\mathbb Z^d\), not just after scalar evaluation.

`HooleyCoarseCoordinateSeed.lean` applies the existing polynomial-count
coordinate filling theorem. If
\[
 T=\prod_i(2hL_i+1),\quad c=2(\lfloor\log_2T\rfloor+1),
 \quad D=Mc^d,\quad q=\mathrm{denseBoxCount}(D,d),
\]
and the explicit robustness/deletion budget \(qch\le r\) holds, it
produces \(U\) of size at most \(qch\), a translation \(z\), and a
proper axis-aligned coefficient GAP \(P\), with
\[
 z+P\subseteq\Sigma(U),\qquad
 T\le\mathrm{nvDenseFactor}(D,d)|P|,\qquad
 |\ell_i P_{ij}|\le 2qhL_j.
\]
Individual seed-width bounds and the subsequent centered-box interface
are now checked in §11.21.

`HooleyResiduePool.lean` proves that a fixed pool of at most
\([\mathbb Z^d:\Delta]^2\) available indices suffices to supply every
generated residue class, with each correction using fewer than the index
many distinct elements. `HooleyResidueSeed.lean` fills the generated
lattice points of an inner box: it combines these corrections with a
coarse \(\Delta\)-seed, consuming only an index-times-coordinate-width
margin. The seed and correction pool are disjoint.

`HooleyLatticeCoordinates.lean` constructs coordinates on the entire
finite-index generated lattice, including the real linear equivalence.
`HooleyLatticePullback.lean` pulls back a convex body containing the index
multiples of the standard coordinate vectors. Its integer points span the
whole new ambient space. `HooleyLatticeModel.lean` applies the checked
adapted-basis theorem to obtain coordinate bounds \(b_i\ge0\) with
the synthesis guarantee
\[
 |u_i|\le t(b_i+1)
 \quad\Longrightarrow\quad
 \mathrm{synthesis}(u)\in t4^d B\qquad(t>0).
\]
Thus changing to the generated lattice does not assume its index is one.

`HooleyMassBalance.lean` proves the needed reserve-mass estimate. For a
nonnegative integer set of total sum at most \(2^L\), deleting at most
\(k(L+1)\) elements leaves \(B\) with
\(kb\le\sum B\) for every \(b\in B\). Taking \(k=4s\), every
reserve \(W\subseteq B\) of size at most \(s\) satisfies
\(3\sum W\le\sum(B\setminus W)\).
`HooleyStructuralCardinality.lean` separately checks the finite numerical
criterion excluding rank three from the full-width cardinality bound.

The combined geometric checkpoint builds successfully, and the complete
audit through these roots uses only standard Lean axioms. No resource
limits have been changed. The arbitrary-set seed theorem and final
\(N^{1/3}\operatorname{Log}_2(N)^{16}\) bound remain unassembled.

### 11.21. Checked full generated-lattice seed

`HooleyProductSides.lean` converts the coefficient product lower bound
and generator-excursion upper bounds into individual side estimates.
For \(F_0=\mathrm{nvDenseFactor}(D,d)\) and
\(F=F_0(q+1)^d\), it proves
\[
  2hL_i+1\le F(\ell_i+1).
\]
Once \(2F\le2hL_i\), the diagonal multipliers are nonzero and bounded
in absolute value by \(2qF\). `HooleyCenteredCoarseSeed.lean` centers
the coefficient progression and proves exact containment of the
corresponding symmetric coarse-lattice box, including negative
coordinate multipliers.

`HooleyLatticeSeed.lean` combines this with the fixed residue pool. Put
\(J=(2qF)^d\). Given the robust coefficient density and subgroup
deletion stability, if
\[
 qch+J^2\le r,\qquad
 2F(R_i+JL_i+1)\le2hL_i\quad\text{for every }i,
\]
it constructs \(S\subseteq A\), \(|S|\le qch+J^2\), and
\(z\in\Sigma(S)\) in the generated lattice \(\Gamma\), such that
\[
 z+\{x\in\Gamma:|x_i|\le R_i\}\subseteq\Sigma(S).
\]
It also proves that removing \(S\) preserves \(\Gamma\). The proof
uses distinct elements throughout. This theorem and the preceding width
lemmas compile and pass the standard-axiom audit.

What remains is to instantiate these seed budgets for the interval-set
model, connect the resulting seed to the adapted-coordinate convex-body
construction, and discharge the final exponent-16 bounds. The complete
upper-bound theorem is not yet assembled.

### 11.22. Checked adapted seed and polynomial budgets

`HooleyCoordinateTransfer.lean` and `HooleyLatticeModelMaps.lean` transfer
robust spanning and evaluation through the coordinates of the entire
generated lattice. `HooleyAdaptedSeed.lean` shows that a lattice seed in
\(K_d B\), where \(K_d=(4^{d+2}+d+1)4^d\), covers every adapted-coordinate
rounding error needed for the zonotope construction.

`HooleySeedToGAP.lean` constructs a proper homogeneous GAP from this
rounding-error seed and a robustly spanning remaining set. Its conclusion
includes the individual side bounds, the \(m^{r+1}\) cardinality lower
bound, and a height-to-span bound with constants depending only on the
initial rank and the seed-center mass ratio.

`HooleySeedCostBounds.lean` gives an explicit positive constant \(C_d\)
such that, if \(D>0\), \(c\le D\), \(I\le D^d\), and
\[
 C_dD^{32(d+1)^2}\le h,
\]
then the seed costs at most \(h^2\) elements and covers the required
radii \(R_i=K_d(I(L_i+1)+1)\), for all positive sides \(L_i\).
These interfaces pass the standard-axiom audit.

`HooleySeedDyadicBounds.lean` checks the uniform asymptotic budget: for
fixed \(a,p,d_0\) and \(b\ge32(d_0+1)^2+1\), eventually every
\(d\le d_0\) and \(0<D\le a2^t(t+1)^p\) satisfy
\(C_dD^{32(d+1)^2}\le2^{bt}\). It then supplies the full seed width and
deletion inequalities at that scale. This module compiles with the
default resource limits. Interval-set preprocessing and the final
exponent-16 theorem remain to be assembled.

### 11.23. Checked robust-model extraction and preprocessing

`HooleyGeneratedSeed.lean` connects a full generated-lattice seed to the
adapted-coordinate extraction theorem, preserving evaluation, cardinality,
and robust spanning. `HooleySeedBox.lean` provides the symmetric shape
with radii \(I(L_i+1)+1\), including its index-period containment and
dilation bounds. `HooleyStableSeed.lean` combines the seed construction,
coordinate change, and inner-quotient extraction. It keeps the spanning
threshold explicit, so subsequent deletions do not silently change that
hypothesis.

`HooleyCoefficientModel.lean` transfers density, subgroup stability,
spanning, reserve mass, and subset-sum provenance between an integer set
and its centered coefficient vectors. `HooleyModelExtraction.lean`
applies the combined extraction theorem directly to an integer model.

`HooleyPreprocessing.lean` combines mass balancing and subgroup
stabilization. For index bound \(I\), stabilization radius \(r\), and
reserve budget \(s\), the deletion cost is
\(4s(L+1)+Ir\); the reserve-mass conclusion remains valid after both
steps. `HooleyPreprocessingBudgets.lean` proves that with \(s=h^4\),
\(r=h^2\), \(I\le h\), and \(8(L+1)+1\le h\), preprocessing and the
seed together cost at most \(h^5\).

`HooleyRobustModelExtraction.lean` combines these results. Given a
coordinate model robust on every subset of at least one third of its
elements, the seed power bound, the preceding index/linear budgets, and
\(|A|\ge6h^5+6\), it constructs a proper homogeneous GAP in
\(\Sigma(A)\). Its full-width and cardinality estimates use
\(m=\lfloor |A|/2\rfloor\), provided \(m\) also exceeds the fixed
rank-dependent geometric threshold. The height is at most
\((3K_d/2+1)\) times the span, with
\(K_d=\lceil32\cdot4^d/(1/4^{d+1})\rceil\).

`HooleyModelBudget.lean` bounds the actual fiber logarithm of an interval
model linearly in its dyadic ambient exponent and supplies the resulting
polynomial density bound. `HooleyIntervalMass.lean` supplies the total
mass bound. The constants of the weak high-fold model are now chosen
uniformly before the secondary weak-stability parameter, avoiding a
circular parameter choice. These modules compile and pass the
standard-axiom audit. Uniform interval
parameter selection and the final exponent-16 assembly remain.

### 11.24. Completed uniform interval extraction

`HooleyExtractionConstants.lean` makes the rank-dependent constants
uniform over a fixed rank ceiling. `HooleyDyadicModel.lean` chooses
all parameters without circular dependencies. After fixing the uniform
high-fold doubling constant and its rank ceiling \(d_0\), put
\(b=32(d_0+1)^2+1\). The ambient and high-fold scales are
\[
 N_t=2^{1000bt},\qquad h=2^{3bt}.
\]
For all sufficiently large \(t\), the density, seed-width, lattice-index,
and preprocessing budgets hold uniformly. Every input of size at least
\(2^{20bt}\) yields a proper homogeneous GAP in its actual subset sums,
with size parameter a constant fraction of the input cardinality.

`HooleyIntervalExtraction.lean` removes the fixed-scale restriction.
It proves that there are positive absolute constants \(R,d_0,F,C\)
such that, for all sufficiently large \(N\), every
\(A\subseteq[1,N]\) with \(N\le |A|^3\) admits \(m>0\) and a
proper homogeneous GAP \(Q\subseteq\Sigma(A)\) satisfying
\[
 m\le |A|\le Rm,\quad 1\le r=\operatorname{rank}(Q)\le d_0,
 \quad m\le F\ell_i,\quad
 m^{r+1}\le 2F^r|Q|,\quad
 Q_{\max}\le C\operatorname{span}(Q).
\]
No logarithmic loss occurs in \(m\).

### 11.25. Completed unconditional exponent-16 bound

`HooleyCubicForcing.lean` combines the cardinality rank bound with the
checked log-log square locator. A single surplus
\[
 E N\Lambda^{44}\le m^3
\]
supplies all three terminal power budgets and excludes rank at least
three. Here \(E\) is an absolute constant determined by the extraction
constants, and \(\Lambda\) bounds the log-log of the progression height.

`HooleyFinalBudgets.lean` proves the remaining comparisons. For
\(N\ge\max(2,R)\), the height is at most \(RmN\le N^3\), so one may
take \(\Lambda=3\max(1,\log\log N)\). Since \(|A|\le Rm\), a
fixed multiple of \(N\max(1,\log\log N)^{48}\) below \(|A|^3\)
provides the required surplus and the fixed minimum-size condition.
`HooleyFinalForcing.lean` proves the resulting unconditional finite
square-forcing theorem.

Finally, `HooleyUpperBound.lean` applies that theorem to a maximizing
admissible set and proves:

```lean
theorem Erdos587.unconditional_loglog_upper_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (MaxNotSqSum N : ℝ) ≤ K * (N : ℝ) ^ (1 / 3 : ℝ) *
        (max 1 (Real.log (Real.log (N : ℝ)))) ^ 16
```

The final theorem module builds successfully. It has no conjectural
hypotheses and no resource-limit overrides. The old logarithmic upper
bound, lower bound, and \(N^{1/3+o(1)}\) consequence are preserved.
Earlier status notes in Section 11 are the historical checkpoints, not
outstanding obligations.

Final verification on 2026-08-27, with Lean/mathlib 4.33.0:

- `lake build ErdosProblems.Erdos587` succeeded (10,084 build jobs).
- The complete root audit, including
  `#print axioms Erdos587.unconditional_loglog_upper_bound` and the three
  existing public results, reported only `propext`, `Classical.choice`,
  and `Quot.sound`.
- All `Hooley*.lean` sources were checked for `sorry`, `admit`, `axiom`,
  and `set_option`; none occur. No computational-limit override was added.
- The Comparator setup now checks the log-log bound as
  `Erdos587.erdos_587.variants.loglog_upper_bound`, alongside the three
  existing public results. The permitted axioms are unchanged, and
  `enable_nanoda` remains true.
- Comparator accepted all four targets: the statements matched, the
  axiom check passed, and both Nanoda and Lean's default kernel accepted
  the solution. This check used Comparator's documented macOS development
  runner; Linux Landrun process isolation was not exercised.
