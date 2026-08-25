# Erdos237b: unconditional proof

## Status

The main theorem in `src/latest/ErdosProblems/Erdos237b.lean` is now
unconditional. Lean accepts both `Erdos237b.chen_ding_theorem` and
`Erdos237b.erdos_237`; their dependency audits report exactly
`[propext, Classical.choice, Quot.sound]`. No replacement axiom, placeholder,
or computational-limit override was added.

The proof avoids the quantitative `maynard_tao` theorem. It proves
a weaker qualitative prime-tuple theorem in `Erdos237b/Unconditional.lean`,
using the already-proved Bombieri–Vinogradov theorem and ordinary PNT from
the installed `BoundedGaps` dependency. The independent quantitative proof is
now in `Util/MaynardTao/Theorem.lean`, and the original Chen–Ding reduction
using it is preserved as `ErdosProblems/Erdos237.lean`.

## Why the alternative proof uses a weaker theorem

The former `maynard_tao` axiom stated a quantitative Maynard–Tao theorem for
arbitrary admissible finite sets of integers: if
`exp (8*m+4) < card B * log (card B)`, arbitrarily late translates contain
at least `m` primes. This matches Lemma 5 in
[Chen–Ding (2022)](https://www.numdam.org/item/CRMATH_2022__360_G9_971_0.pdf).
Thus neither the exponential threshold nor the integer formulation is an
accidental issue that would make the axiom easy to discharge.

The installed `BoundedGaps` dependency proves its public constant-600 theorem
without extra axioms. However,
`engelsmaSmallKCandidateNormalizedAsymptotics_of_primeLevel_and_pnt` has a
fixed 105-element tuple and a fixed polynomial candidate in its conclusion.
It cannot be instantiated with an arbitrary tuple or an arbitrary prime
count. Bombieri–Vinogradov and PNT themselves are already proved there.

## A much weaker sufficient target

`Erdos237b/Qualitative.lean` defines `QualitativePrimeTuples`:

```lean
∀ m : ℕ, ∃ k : ℕ, ∀ H : Finset ℕ, H.card = k →
  BoundedGaps.IsAdmissible H →
    ∃ n : ℕ, m ≤ BoundedGaps.primeShiftCount H n
```

Only one cardinality per requested count and one translate per tuple are
needed. The following reduction has been checked by Lean:

1. From a set with at least `k! * k` elements, select `k` elements in one
   residue class modulo `k!`.
2. Reflect them in their maximum: `H = {max B - a : a ∈ B}`.
3. For a prime `p ≤ k`, the reflected tuple occupies at most one residue
   class; for `p > k`, its cardinality is smaller than `p`. Hence it is
   admissible.
4. A prime shift `n + (max B - a)` gives a representation of `n + max B`.
5. Apply the finite conclusion to a sufficiently large subset of an infinite
   set.

This removes Mertens' theorem and all explicit logarithmic thresholds from
the reduction. `qualitativePrimeTuples_unconditional` supplies the remaining
prime-tuple input. The quantitative sieve helpers belong to the original
`Erdos237.lean` solution and are not imported by this alternative proof.

`Erdos237b/MaynardBridge.lean` also extends the library's positivity argument
from two primes to any count. The generic normalized-asymptotics interface
already in the dependency then suffices: positive scale, nonnegative weights,
an S1 limit, a convergent lower bound for normalized S2, and a strict margin
give arbitrarily late translates with at least `m+1` primes. A full S2 limit
is unnecessary.

## A coarse dyadic alternative to the sharp variational bound

The sharp estimate for Maynard's variational supremum is unnecessary. The
finite model in `ProductWeights.lean`, `BoxVariational.lean`,
`DyadicWeights.lean`, and `DyadicBox.lean` instead uses `L` intervals

\[
  [2^j,2^{j+1}]/(8Lk),\qquad 0\le j<L,
\]

of heights `2^(-j)`, with `k ≥ 2^L`. Write `length_j`, `height_j`, and
`upper_j` for their lengths, heights, and upper endpoints. Let

\[
  Z=\sum_{j<L}2^{-j},\quad
  \gamma=\sum_j height_j^2 length_j=Z/(8Lk),\quad
  \sigma=\sum_j height_j length_j=1/(8k).
\]

Lean proves `1 ≤ Z < 2`. Under the probability weights
`height_j² * length_j / γ`, the expected upper endpoint is
`1/(4*k*Z)`. Consequently, for at most `k` independent coordinates,
at least half the product mass has total upper endpoint at most `1/2`.
Every individual upper endpoint is at most `1/2`.

Keep the product boxes whose upper endpoints sum to at most one. Their
finite denominator `D` is positive and at most `γ^k`. The finite numerator
for a single omitted coordinate is at least `γ^(k-1) * σ² / 2`. Therefore

\[
  \frac{kJ}{D}\ \ge\ \frac{k\sigma^2}{2\gamma}
  =\frac{L}{16Z}\ >\frac{L}{32}.
\]

`exists_dyadic_box_ratio_gt` proves that this finite-sum ratio is
unbounded. The arithmetic transfer below works directly with finite boxes;
no identification with smooth Maynard integrals is required. This is a coarse version of the
product-weight argument in
[Maynard, Section 7](https://arxiv.org/html/1311.4600v3#S7), using a first
moment instead of the sharper concentration estimate.

## S1 arithmetic transfer

`SieveS1Limit.lean` now proves the full S1 asymptotic for the actual supported
dyadic weights in every fixed finite dimension, for `0 < alpha < 1/4`.
The auxiliary exponent is `alpha/2`; the limit is `D * (1/2)^k` under the
normalization `N/W * (phi(W)/W * log R)^k`. Its supporting modules prove:

- `FiniteBoxWeights.lean` and `DyadicSupport.lean`: disjoint rectangular
  shells, strict product support, uniform boundedness, and actual supported Y-weights.
- `SieveCollisionLimits.lean` and `SupportedWeights.lean`: removing shared-prime
  collisions leaves the diagonal limit unchanged, and the normalized S1 cross term vanishes.
- `DyadicDiagonal.lean`: the actual dyadic Y-diagonal limit.
- `YWeightBounds.lean` and `SieveScaleBounds.lean`: coefficient mass at most
  `R^4 * B^2 * (1+log R)^(6*k)`, negligible against the sieve scale for `alpha < 1/4`.
- `SieveDecomposition.lean`: the exact diagonal-minus-cross-plus-error identity.

## S2 lower bound with one extra coordinate

`S2ExtraCoordinate.lean` is the key simplification. Expand a squared
coordinate fiber into two inner variables, indexed by the distinguished
coordinate and one extra coordinate. A globally squarefree tuple on
`Option H` projects to two supported tuples on `H`. Its reciprocal-totient
weight is no larger than the corresponding S2 triple weight, because
`g(n) ≤ phi(n)` on squarefree arguments and the pre-sieve excludes 2.

For the lower bound, keep outer-coordinate boxes of total upper endpoint
at most `1/2`, and allow both inner coordinates to use every dyadic interval.
Each projection is an allowed original box. After the factor `1/2` in the
endpoints, the enlarged box has total upper endpoint at most `3/4 < 1`.
The same rectangular reciprocal-totient limit and collision removal used
for S1 therefore apply in dimension `k+1`.

`S2MixedDyadic.lean` gives the retained mass, with square masses on the
outer coordinates and linear masses on the two inner coordinates.
`S2DyadicLower.lean` composes the geometry and arithmetic limits. The
resulting lower constant for each coordinate is

\[
  C_2=\frac{\sigma^2\gamma^{k-1}}2\,2^{-(k+1)}.
\]

`S2TransformBounds.lean`, `S2SquareComparison.lean`, and `S2CrossLimit.lean`
show that replacing the true S2 arithmetic diagonal by this fiber lower
bound introduces a vanishing normalized error. This avoids proving a
uniform asymptotic formula for every individual fiber.

## Actual prime sums and the strict margin

`YSharpBounds.lean` extends the library's sharp logarithmic coefficient
bound to arbitrary supported Y-weights. `PrimeErrorEnvelope.lean` and
`PrimeSieveError.lean` use the unconditional Bombieri–Vinogradov theorem to
prove that the actual prime-progression error vanishes in every fixed
dimension. `ShiftedPrimeLimit.lean` obtains the factor `alpha` from ordinary
PNT for every fixed natural shift. `SieveS2Decomposition.lean` and
`SieveS2Lower.lean` assemble these results into a lower bound for actual S2.

Choose radius exponent `alpha = 1/8`, prime level `theta = 3/8`, and
`delta = 1/16`. With `C_1=D*2^(-k)`, `SieveConstants.lean` proves

\[
 L>512m\quad\Longrightarrow\quad
 \frac18 k C_2-mC_1>0.
\]

`Unconditional.lean` takes `L=512*(m+1)` and `k=2^L` symbolically and
deduces positive sieve excess for every admissible tuple of that cardinality.
This proves `QualitativePrimeTuples`, and hence the unchanged Erdős 237 statement.

For strict divisor-support inequalities, leave a fixed gap between the
exponent used for box endpoints and the exponent of the divisor cutoff.
There is no need to optimize it: any fixed positive prime-weight coefficient
can be overcome by increasing `L` symbolically.

## Verification

From `src/latest`:

```sh
lake build ErdosProblems.Erdos237b
lake env lean _scratch/Erdos237Audit.lean
lake env lean ComparatorChallenges/ErdosProblems/Erdos237b.lean
```

The solution and all supporting modules pass with unchanged limits. The audit
checks the extracted definition by `rfl` and prints the dependency axioms of
the final theorem and the major intermediate results. All audited results
use only `propext`, `Classical.choice`, and `Quot.sound`. The challenge
compiles with only its intentional placeholder warning.

The Comparator runner was attempted for both proof routes and stopped with:

```text
Comparator requires landrun in PATH or COMPARATOR_LANDRUN to be set.
```

No Comparator success is claimed. Both configurations permit only the three
standard logical axioms. The `Erdos237b` challenge copies the original
statement and `repCount` definition into the `Erdos237b` namespace; the
original `Erdos237` challenge is unchanged.
