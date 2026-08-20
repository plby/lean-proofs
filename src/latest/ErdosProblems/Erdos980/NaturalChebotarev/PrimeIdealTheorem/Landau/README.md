# Landau / prime-ideal-theorem interface audit

This directory records the part of the prime ideal theorem that follows from the
repository's effective ideal-counting theorem, and the remaining analytic chain needed for
a complete Lean proof.

## Checked effective count

`Interfaces.lean` type-checks the following specialization of
`Chebotarev.exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le` at modulus `1`:

```lean
Landau.exists_effective_nonzeroIdeal_count_residue
    (K : Type*) [Field K] [NumberField K] :
  ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |(Nat.card {I : (Ideal (𝒪 K))⁰ //
        Ideal.absNorm (I : Ideal (𝒪 K)) ≤ N} : ℝ)
        - NumberField.dedekindZeta_residue K * N|
      ≤ C * (N : ℝ) ^
        (1 - (Module.finrank ℚ K : ℝ)⁻¹)
```

The modulus-one residue condition is removed by an explicit subtype equivalence.  The
leading constant is identified rather than left existential: dividing the error estimate by
`N` gives a limit to the returned constant, while
`Chebotarev.tendsto_sum_idealNormMultiplicity_div` and the two cardinality bridges in
`PrimeIdealTheorem/IdealCounting.lean` give the same limit with value
`NumberField.dedekindZeta_residue K`.  Uniqueness of limits identifies the constants.
Positivity is already available as `NumberField.dedekindZeta_residue_pos K`.

The raw public interfaces used here are:

```lean
Chebotarev.exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le
Chebotarev.sum_idealNormMultiplicity_eq_card_norm_le
Chebotarev.card_nonzeroIdeal_norm_le_eq_card_nonZeroDivisor_norm_le
Chebotarev.tendsto_sum_idealNormMultiplicity_div
NumberField.Ideal.tendsto_norm_le_div_atTop₀
NumberField.dedekindZeta_residue_pos
```

For new finite-set code, use
`Ideal.finite_setOfPred_absNorm_eq`, `Ideal.finite_setOfPred_absNorm_le`, and
`Ideal.finite_setOfPred_absNorm_le₀`; the shorter `finite_setOf_absNorm_*` spellings are
deprecated aliases.  There is no canonical bounded-ideal `Finset` in Mathlib.  The supported
construction is `Set.Finite.toFinset`, with membership normalized by
`Set.Finite.mem_toFinset`.

## What the count does not prove by itself

A power-saving asymptotic for multiplicative coefficients is not, on its own, a prime number
theorem.  For a fixed rational prime `p`, the multiplicative function

```text
a(n) = 1 + p * 1_(p divides n)
```

satisfies `sum (n ≤ x) a(n) = 2x + O(1)`, but its Dirichlet series is

```text
zeta(s) * (1 + p^(1-s)),
```

which has a zero on `re s = 1`.  Thus the ideal count supplies coefficient growth and crude
counting estimates, but a zero-free argument using the actual prime-ideal Euler factors is
still essential.  A purely convolutional Selberg/Landau proof would additionally require a
large library of divisor-sum estimates that is not currently present.

For this repository the shortest fully formalizable route is therefore the classical
Landau--de la Vallée Poussin argument followed by the existing Wiener--Ikehara theorem.  It
uses the effective count for the elementary `O(x)` bounds needed in the final prime-power
tail, while using the exact Euler product for boundary nonvanishing.

## Concrete Lean theorem chain

### 1. Meromorphic continuation and boundary zero-freeness

`ContinuedZeta/Basic.lean` constructs
`ContinuedZeta.continuedDedekindZeta` from AINTLIB's completed entire zeta and proves that it
agrees with `NumberField.dedekindZeta` on `1 < s.re`.  It also constructs the holomorphic
one-pole regularization
`ContinuedZeta.continuedDedekindZetaOneRegularized`.

`PrimeIdealTheorem/ZeroFreeLine.lean` now supplies the two exact terminal lemmas:

```lean
continuedDedekindZeta_ne_zero_of_re_eq_one
continuedDedekindZeta_ne_zero_of_one_le_re
```

The proof is the `3-4-1` argument.  For `x > 0`, AINTLIB's Euler product gives

```text
1 ≤ ‖zeta_K(1+x)^3 zeta_K(1+x+it)^4 zeta_K(1+x+2it)‖.
```

If the continued zeta vanished at `1+it`, differentiability would make the middle factor
`O(x)`.  The pole factor is `O(x⁻¹)` and the last factor is `O(1)`, so the displayed
product would be `O(x)`, a contradiction as `x → 0+`.  The Lean proof uses the completed
zeta continuation, `Asymptotics.IsBigO`, and the prime-side Euler-product identities from
`DedekindResidue.ExplicitFormula.PrimeSide`.

### 2. Pole-subtracted continuous extension

`PrimeIdealTheorem/PoleSubtraction.lean` defines

```lean
PoleSubtraction.poleSubtractedDedekindLogDeriv K s =
  -logDeriv (ContinuedZeta.continuedDedekindZetaOneRegularized K) s
```

and exports:

```lean
PoleSubtraction.continuousOn_poleSubtractedDedekindLogDeriv
PoleSubtraction.poleSubtractedDedekindLogDeriv_eq
PoleSubtraction.exists_continuous_poleSubtractedDedekindLogDeriv
```

On `1 < s.re`, the last function equals

```text
-logDeriv (dedekindZeta K) s - 1 / (s - 1).
```

The nonvanishing hypothesis is discharged directly with
`continuedDedekindZeta_ne_zero_of_one_le_re`.

### 3. Group prime powers by their integer norm

Use `IdealMangoldt/Basic.lean` as the canonical coefficient definition:

```lean
IdealMangoldt.PrimeIdealPower K
IdealMangoldt.normFiber K n
IdealMangoldt.idealMangoldt K n
IdealMangoldt.idealMangoldt_nonneg K n
```

`IdealMangoldt/Analytic.lean` has already formalized the required absolutely convergent
regrouping.  Its main public interfaces are:

```lean
IdealMangoldt.summable_nterm_idealMangoldt
IdealMangoldt.LSeries_idealMangoldt_eq_neg_logDeriv
IdealMangoldt.LSeries_idealMangoldt_eq_neg_deriv_div
```

Internally it uses `Equiv.sigmaFiberEquiv` to regroup the prime-power series and
`DedekindResidue.neg_logDeriv_dedekindZeta_eq_tsum_prod` for the prime-side identity.

There is an older bounded-finset coefficient
`Chebotarev.primeIdealVonMangoldtCoeff` in `PrimeIdealTheorem/WeightedDefs.lean`.  Avoid
duplicating analytic work for it.  Either state the Tauberian theorem using the canonical
`IdealMangoldt.idealMangoldt`, or prove once that the two finite coefficients agree for every
`n` and rewrite the older cumulative definitions.

### 4. Wiener--Ikehara

`PrimeIdealTheorem/WienerBridge.lean` exports

```lean
wienerIkehara_cumsum_div_tendsto
wienerIkehara_sum_range_div_tendsto
wienerIkehara_strictCumulative_div_tendsto
```

Instantiate the bridge with

```text
f = IdealMangoldt.idealMangoldt K,
A = 1,
G = PoleSubtraction.poleSubtractedDedekindLogDeriv K.
```

The hypotheses match exactly:

1. coefficient nonnegativity is `IdealMangoldt.idealMangoldt_nonneg`;
2. real-line summability is `IdealMangoldt.summable_nterm_idealMangoldt`;
3. continuity is
   `PoleSubtraction.continuousOn_poleSubtractedDedekindLogDeriv`, after supplying the
   zero-free-line theorem;
4. on `1 < s.re`, rewrite the L-series by
   `IdealMangoldt.LSeries_idealMangoldt_eq_neg_logDeriv`, then use
   `PoleSubtraction.poleSubtractedDedekindLogDeriv_eq`.

This gives the prime-ideal Chebyshev limit

```text
(sum n < N, idealMangoldt K n) / N → 1.
```

### 5. Remove higher prime powers

Define

```text
theta_K(x) = sum_(N p ≤ x) log(N p).
```

The difference between the Mangoldt sum and `theta_K` has exponent at least two.  Every
such prime has norm at most `sqrt x`; each exponent is at most `log x / log 2`; and every
weight is at most `log x`.  Hence

```text
0 ≤ psi_K(x) - theta_K(x)
  ≤ A_K(floor(sqrt x)) * (log x / log 2 + 1) * log x,
```

where `A_K(y)` is the number of nonzero ideals of norm at most `y`.  The effective estimate
in `Interfaces.lean` implies `A_K(y) = O(y)`, so the right side is
`O(sqrt x * (log x)^2) = o(x)`.  Combine this with the Wiener--Ikehara limit to obtain
`theta_K(x) / x → 1`.

Lean helper lemmas needed for this stage should be kept elementary:

```text
card_primeIdeals_norm_le_le_card_nonzeroIdeals_norm_le
primePower_exponent_ge_two_absNorm_le_natSqrt
higherPrimePowerWeight_le_idealCount_mul_logSq
tendsto_natSqrt_mul_log_sq_div
theta_div_tendsto_one
```

The first inequality is an injection of bounded prime ideals into bounded nonzero ideals.
The square-root implication follows from `(N p)^m ≤ x`, `2 ≤ m`, and
`(N p)^2 ≤ (N p)^m`.  For limits, use the real cutoff obtained from `Nat.floor` or
`Nat.ceil`; the ICC theorem itself only needs natural cutoffs.

### 6. Partial summation to the prime-ideal count

Let `pi_K(x)` count nonzero prime ideals with norm at most `x`.  With
`y = x / (log x)^2`, monotonicity gives the standard sandwich

```text
theta_K(x) / log x ≤ pi_K(x)
pi_K(x) ≤ A_K(y) + theta_K(x) / log y.
```

The lower bound uses `log(N p) ≤ log x`.  In the upper bound, split primes at `y`; the
small primes are bounded by the all-ideal count and every remaining prime has weight at
least `log y`.  Since `A_K(y) = O(y)`, `log y / log x → 1`, and
`theta_K(x) / x → 1`, squeeze to obtain

```text
pi_K(x) / (x / log x) → 1.
```

This terminal estimate is the Dedekind prime ideal theorem needed by the natural-density
Chebotarev development.

## Validation

From `src/latest/`, the checked command is:

```text
/root/code/lean-4.33.0/bin/lake env lean \
  ErdosProblems/Erdos980/NaturalChebotarev/PrimeIdealTheorem/Landau/Interfaces.lean
```

It completes successfully.  This audit did not edit the shared aggregate modules.
