import ErdosProblems.Erdos520.CaichReduction
import ErdosProblems.Erdos520.LargestPrimeTestUnion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Caich-scale concentration from the exact stopped Hoeffding theorem

This file connects the exact finite-test union in
`LargestPrimeTestUnion` to the scalar exponent calculation already proved in
`CaichReduction`.  It removes `concentration_measure_le` as a genuinely
probabilistic input: once the deterministic threshold ratio and test-point
count are supplied, summability follows in Lean.
-/

/-- A lower bound for the stopped-Hoeffding exponent gives a common
one-point decay estimate. -/
theorem largestPrime_hoeffdingTerm_le_caichDecay
    (tests : ℕ → Finset ℕ) (u T : ℕ → ℕ → ℝ)
    {c q : ℝ}
    (hexponent : ∀ ell r, r ∈ tests ell →
      c * (ell : ℝ) ^ q ≤ (u ell r) ^ 2 / (2 * T ell r))
    {ell r : ℕ} (hr : r ∈ tests ell) :
    2 * Real.exp (-(u ell r) ^ 2 / (2 * T ell r)) ≤
      2 * Real.exp (-c * (ell : ℝ) ^ q) := by
  have hExp : -(u ell r) ^ 2 / (2 * T ell r) ≤
      -c * (ell : ℝ) ^ q := by
    rw [show -(u ell r) ^ 2 / (2 * T ell r) =
      -((u ell r) ^ 2 / (2 * T ell r)) by ring]
    simpa only [neg_mul] using! neg_le_neg (hexponent ell r hr)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) (by norm_num)

/-- The exact finite Hoeffding budget after inserting an exponential bound
for the number of test points. -/
theorem largestPrimeStoppedBudget_le_caichExponent
    (tests : ℕ → Finset ℕ) (u T : ℕ → ℕ → ℝ)
    {C c q : ℝ} {K : ℕ}
    (hcard : ∀ ell,
      ((tests ell).card : ℝ) ≤ Real.exp (C * (ell : ℝ) ^ (K : ℝ)))
    (hexponent : ∀ ell r, r ∈ tests ell →
      c * (ell : ℝ) ^ q ≤ (u ell r) ^ 2 / (2 * T ell r))
    (ell : ℕ) :
    largestPrimeStoppedBudget tests u T ell ≤
      2 * Real.exp
        (C * (ell : ℝ) ^ (K : ℝ) - c * (ell : ℝ) ^ q) := by
  have hone : largestPrimeStoppedBudget tests u T ell ≤
      (tests ell).card * (2 * Real.exp (-c * (ell : ℝ) ^ q)) := by
    apply largestPrimeStoppedBudget_le_card_mul
    intro e r hr
    exact largestPrime_hoeffdingTerm_le_caichDecay
      tests u T hexponent hr
  calc
    largestPrimeStoppedBudget tests u T ell ≤
        (tests ell).card * (2 * Real.exp (-c * (ell : ℝ) ^ q)) := hone
    _ ≤ Real.exp (C * (ell : ℝ) ^ (K : ℝ)) *
          (2 * Real.exp (-c * (ell : ℝ) ^ q)) := by
      exact mul_le_mul_of_nonneg_right (hcard ell) (by positivity)
    _ = 2 * Real.exp
          (C * (ell : ℝ) ^ (K : ℝ) - c * (ell : ℝ) ^ q) := by
      rw [show Real.exp (C * (ell : ℝ) ^ (K : ℝ)) *
          (2 * Real.exp (-c * (ell : ℝ) ^ q)) =
          2 * (Real.exp (C * (ell : ℝ) ^ (K : ℝ)) *
            Real.exp (-c * (ell : ℝ) ^ q)) by ring,
        ← Real.exp_add]
      congr 1
      ring_nf

/-- Caich's choice `10 < 2*K*eta` makes the exact stopped-Hoeffding budget
summable, including the finite test-point union. -/
theorem summable_largestPrimeStoppedBudget_of_caich
    (tests : ℕ → Finset ℕ) (u T : ℕ → ℕ → ℝ)
    {C c eta : ℝ} {K : ℕ} (hC : 0 ≤ C) (hc : 0 < c)
    (hK : 1 ≤ K) (hgap : 10 < 2 * (K : ℝ) * eta)
    (hcard : ∀ ell,
      ((tests ell).card : ℝ) ≤ Real.exp (C * (ell : ℝ) ^ (K : ℝ)))
    (hexponent : ∀ ell r, r ∈ tests ell →
      c * (ell : ℝ) ^
          ((K : ℝ) + 2 * (K : ℝ) * eta - 10) ≤
        (u ell r) ^ 2 / (2 * T ell r)) :
    Summable fun ell => largestPrimeStoppedBudget tests u T ell := by
  apply Summable.of_nonneg_of_le
  · intro ell
    unfold largestPrimeStoppedBudget
    positivity
  · intro ell
    exact largestPrimeStoppedBudget_le_caichExponent
      tests u T hcard hexponent ell
  · exact (summable_caich_concentration_budget hC hc hK hgap).mul_left 2

/-- Fully probabilistic Caich-scale concentration conclusion.  The remaining
inputs are deterministic: positivity of thresholds, test entropy, the scalar
threshold ratio, and the almost-sure quadratic-variation bound. -/
theorem ae_eventually_largestPrimeMain_lt_of_caich
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (u T : ℕ → ℕ → ℝ)
    {C c eta : ℝ} {K : ℕ} (hC : 0 ≤ C) (hc : 0 < c)
    (hK : 1 ≤ K) (hgap : 10 < 2 * (K : ℝ) * eta)
    (hu : ∀ ell r, r ∈ tests ell → 0 ≤ u ell r)
    (hT : ∀ ell r, r ∈ tests ell → 0 < T ell r)
    (hcard : ∀ ell,
      ((tests ell).card : ℝ) ≤ Real.exp (C * (ell : ℝ) ^ (K : ℝ)))
    (hexponent : ∀ ell r, r ∈ tests ell →
      c * (ell : ℝ) ^
          ((K : ℝ) + 2 * (K : ℝ) * eta - 10) ≤
        (u ell r) ^ 2 / (2 * T ell r))
    (hqv : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        largestPrimeQuadraticVariation omega
          (x ell r) (a ell r) (b ell r) ≤ T ell r) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |largestPrimeMain omega
          (x ell r) (a ell r) (b ell r)| < u ell r := by
  exact ae_eventually_largestPrimeMain_lt_of_qv_and_summable
    tests x a b u T hu hT
      (summable_largestPrimeStoppedBudget_of_caich
        tests u T hC hc hK hgap hcard hexponent)
      hqv

end Problem520
end Erdos
