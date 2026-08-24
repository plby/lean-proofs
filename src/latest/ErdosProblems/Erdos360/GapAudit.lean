/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.StructuredCount
import ErdosProblems.Erdos360.FiniteSourceAssembly

/-!
# Exact lower-bound dependency audit for Erdős 360

This scratch module contains no residual principle disguised as a declaration.
Every declaration below is a proved connector between the public prime-counting
module and the public finite-source assembly.

The dependency graph exposed by the theorem types is:

```
primeStructuredTestSet
  |-- ratio_y_div_log_le_primeStructuredTestSet_card
  |-- primeStructuredTestSet_factorization_above
  `-- CFPRandomPreLevTestSetSourceCompletion
          |
          v
CFPPrimeRandomPreLevTestSetData
          |
          |  CFPLevHighMultiplicityPrinciple
          v
EventuallyCFPTestSetTheorem
          |
          v
EventuallyForcesResolutionFloor
          |
          v
Resolution
```

Thus, after `StructuredCount` and `FiniteSourceAssembly`, the two genuinely
mathematical inputs still required by the shortest exact chain are:

1. `CFPLevHighMultiplicityPrinciple`;
2. the eventual construction of `CFPRandomPreLevTestSetSourceCompletion` at
   the canonical prime-structured test set, including its integer parameter
   ledger.

The elementary conversion of the natural-number test set to the actual
coloring domain, its cardinality, its dyadic bounds, its large-prime
factorization, the finite package, the eventual package, and the final
resolution implication are all proved here.
-/

namespace Erdos360

open Filter

attribute [local instance] Classical.propDecidable

/-! ## The prime test set in the exact coloring domain -/

/-- The prime-only natural-number test set regarded as a finset in
`{1, ..., n-1}`. -/
noncomputable def primeStructuredBelowTarget
    (n y U : ℕ) (hy : 2 * y < n) : Finset (BelowTarget n) :=
  natFinsetBelowTarget n (primeStructuredTestSet n y U)
    (primeStructuredTestSet_subset_Ico hy)

@[simp] lemma mem_primeStructuredBelowTarget_iff
    {n y U : ℕ} {hy : 2 * y < n} {x : BelowTarget n} :
    x ∈ primeStructuredBelowTarget n y U hy ↔
      x.1 ∈ primeStructuredTestSet n y U := by
  simp [primeStructuredBelowTarget]

@[simp] lemma card_primeStructuredBelowTarget
    (n y U : ℕ) (hy : 2 * y < n) :
    (primeStructuredBelowTarget n y U hy).card =
      (primeStructuredTestSet n y U).card := by
  exact card_natFinsetBelowTarget n (primeStructuredTestSet n y U)
    (primeStructuredTestSet_subset_Ico hy)

lemma primeStructuredBelowTarget_dyadic
    {n y U : ℕ} {hy : 2 * y < n}
    {x : BelowTarget n} (hx : x ∈ primeStructuredBelowTarget n y U hy) :
    y < x.1 ∧ x.1 ≤ 2 * y := by
  have hx' := mem_primeStructuredBelowTarget_iff.mp hx
  exact ⟨primeStructuredTestSet_gt_scale hx',
    primeStructuredTestSet_le_two_mul hx'⟩

lemma primeStructuredBelowTarget_factorization_above
    {n y U B : ℕ} {hy : 2 * y < n}
    (hU : 0 < U) (hB : B ≤ y / U)
    {x : BelowTarget n} (hx : x ∈ primeStructuredBelowTarget n y U hy) :
    ∃ u q : ℕ, u ∣ n ∧ q.Prime ∧ B < q ∧ x.1 = u * q := by
  exact primeStructuredTestSet_factorization_above hU hB
    (mem_primeStructuredBelowTarget_iff.mp hx)

/-! ## Finite counted package -/

/-- The precise meeting point of the public structured count and the public
finite source assembly.  The first conjunct is the analytic cardinal lower
bound; the second is the exact finite datum consumed by
`resolution_of_primeRandomPreLev`. -/
theorem primeStructured_count_and_randomPreLev_data
    {n colors y U B L K T : ℕ}
    (hn : 0 < n) (hy : 2 * y < n) (hU : 0 < U)
    (hBpos : 0 < B) (hBcut : B ≤ y / U)
    (hPNT : ∀ X : ℕ, T ≤ X →
      (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ))
    (hscale : ∀ u ∈ boundedTargetDivisors n U, T ≤ y / u)
    (hsmall : ∀ u ∈ boundedTargetDivisors n U, 2 * u ≤ y)
    (htail : (n.divisors.card : ℝ) / (U + 1) ≤
      (1 / 8 : ℝ) * ((n : ℝ) / Nat.totient n))
    (herror : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (64 * Real.log (y : ℝ)))
    (hsource : CFPRandomPreLevTestSetSourceCompletion
      n colors y B L K (primeStructuredBelowTarget n y U hy)) :
    ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (64 * Real.log (y : ℝ)) ≤
        ((primeStructuredBelowTarget n y U hy).card : ℝ) ∧
      Nonempty (CFPPrimeRandomPreLevTestSetData n colors y) := by
  constructor
  · simpa using ratio_y_div_log_le_primeStructuredTestSet_card
      hn hU hPNT hscale hsmall htail herror
  · exact ⟨
      { Y := primeStructuredBelowTarget n y U hy
        B := B
        L := L
        K := K
        B_pos := hBpos
        dyadic := by
          intro x hx
          exact primeStructuredBelowTarget_dyadic hx
        large_prime_factor := by
          intro x hx
          exact primeStructuredBelowTarget_factorization_above hU hBcut hx
        source := hsource }⟩

/-! ## Eventual and final connectors -/

/-- A direct eventual construction at the prime-structured test set produces
the exact eventual package used by `FiniteSourceAssembly`. -/
theorem eventually_primeRandomPreLev_of_primeStructured_source
    {c : ℝ}
    (hsource : ∀ᶠ n : ℕ in atTop,
      let colors := lowerColorCount c n
      let y := initialLowerY n colors
      ∃ U B L K : ℕ,
        ∃ hy : 2 * y < n, 0 < U ∧ 0 < B ∧ B ≤ y / U ∧
        CFPRandomPreLevTestSetSourceCompletion n colors y B L K
          (primeStructuredBelowTarget n y U hy)) :
    EventuallyCFPPrimeRandomPreLevTheorem c := by
  filter_upwards [hsource] with n hn
  dsimp only at hn ⊢
  obtain ⟨U, B, L, K, hy, hU, hBpos, hBcut, hfinite⟩ := hn
  exact ⟨
    { Y := primeStructuredBelowTarget n
        (initialLowerY n (lowerColorCount c n)) U hy
      B := B
      L := L
      K := K
      B_pos := hBpos
      dyadic := by
        intro x hx
        exact primeStructuredBelowTarget_dyadic hx
      large_prime_factor := by
        intro x hx
        exact primeStructuredBelowTarget_factorization_above hU hBcut hx
      source := hfinite }⟩

/-- The shortest exact implication from the two remaining mathematical
inputs to the requested resolution theorem. -/
theorem resolution_of_primeStructured_source
    {c : ℝ} (hc : 0 < c)
    (hlev : CFPLevHighMultiplicityPrinciple)
    (hsource : ∀ᶠ n : ℕ in atTop,
      let colors := lowerColorCount c n
      let y := initialLowerY n colors
      ∃ U B L K : ℕ,
        ∃ hy : 2 * y < n, 0 < U ∧ 0 < B ∧ B ≤ y / U ∧
        CFPRandomPreLevTestSetSourceCompletion n colors y B L K
          (primeStructuredBelowTarget n y U hy)) :
    Resolution := by
  exact resolution_of_primeRandomPreLev hc hlev
    (eventually_primeRandomPreLev_of_primeStructured_source hsource)

end Erdos360

#print axioms Erdos360.primeStructured_count_and_randomPreLev_data
#print axioms Erdos360.resolution_of_primeStructured_source
