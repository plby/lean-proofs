import ErdosProblems.Erdos520.LargestPrimeHoeffding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos
namespace Problem520

/-!
# Stopped Hoeffding simultaneously at finitely many test points

`LargestPrimeHoeffding` proves the exact stopped inequality at one integer
endpoint.  This file performs the finite union and Borel--Cantelli steps.
Consequently no probabilistic concentration assertion has to be retained as
an input: only deterministic choices of the thresholds and a summability
calculation remain.
-/

/-- At scale `ell`, failure of stopped Hoeffding at one of the selected test
indices.  The two cutoff functions describe the largest-prime block used at
that test point. -/
def largestPrimeStoppedFailure
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (u T : ℕ → ℕ → ℝ) (ell : ℕ) : Set Omega :=
  {omega |
    ∃ r ∈ tests ell,
      u ell r ≤ |largestPrimeMain omega (x ell r) (a ell r) (b ell r)| ∧
        largestPrimeQuadraticVariation omega
          (x ell r) (a ell r) (b ell r) ≤ T ell r}

/-- The exact finite-union Hoeffding budget at one scale. -/
noncomputable def largestPrimeStoppedBudget
    (tests : ℕ → Finset ℕ) (u T : ℕ → ℕ → ℝ) (ell : ℕ) : ℝ :=
  ∑ r ∈ tests ell,
    2 * Real.exp (-(u ell r) ^ 2 / (2 * T ell r))

/-- Union of the exact one-point stopped Hoeffding estimates. -/
theorem measureReal_largestPrimeStoppedFailure_le
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (u T : ℕ → ℕ → ℝ)
    (hu : ∀ ell r, r ∈ tests ell → 0 ≤ u ell r)
    (hT : ∀ ell r, r ∈ tests ell → 0 < T ell r)
    (ell : ℕ) :
    μ.real (largestPrimeStoppedFailure tests x a b u T ell) ≤
      largestPrimeStoppedBudget tests u T ell := by
  let point : ℕ → Set Omega := fun r =>
    {omega |
      u ell r ≤
          |largestPrimeMain omega (x ell r) (a ell r) (b ell r)| ∧
        largestPrimeQuadraticVariation omega
          (x ell r) (a ell r) (b ell r) ≤ T ell r}
  have hfailure :
      largestPrimeStoppedFailure tests x a b u T ell =
        ⋃ r ∈ tests ell, point r := by
    ext omega
    simp only [largestPrimeStoppedFailure, point, Set.mem_setOf_eq,
      Set.mem_iUnion, exists_prop]
  rw [hfailure]
  calc
    μ.real (⋃ r ∈ tests ell, point r)
        ≤ ∑ r ∈ tests ell, μ.real (point r) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ tests ell,
        2 * Real.exp (-(u ell r) ^ 2 / (2 * T ell r)) := by
      gcongr with r hr
      exact largestPrime_stoppedTail_measureReal_le
        (x ell r) (a ell r) (b ell r) (hu ell r hr) (hT ell r hr)
    _ = largestPrimeStoppedBudget tests u T ell := rfl

/-- A summable deterministic Hoeffding budget makes stopped failures
eventually absent almost surely. -/
theorem ae_eventually_not_largestPrimeStoppedFailure_of_summable
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (u T : ℕ → ℕ → ℝ)
    (hu : ∀ ell r, r ∈ tests ell → 0 ≤ u ell r)
    (hT : ∀ ell r, r ∈ tests ell → 0 < T ell r)
    (hbudget : Summable fun ell =>
      largestPrimeStoppedBudget tests u T ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      omega ∉ largestPrimeStoppedFailure tests x a b u T ell := by
  apply ae_eventually_notMem
  have hreal : Summable fun ell =>
      μ.real (largestPrimeStoppedFailure tests x a b u T ell) := by
    apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) _ hbudget
    intro ell
    exact measureReal_largestPrimeStoppedFailure_le
      tests x a b u T hu hT ell
  have heq :
      (fun ell => μ (largestPrimeStoppedFailure tests x a b u T ell)) =
        fun ell => ENNReal.ofReal
          (μ.real (largestPrimeStoppedFailure tests x a b u T ell)) := by
    funext ell
    exact (ofReal_measureReal
      (μ := μ)
      (s := largestPrimeStoppedFailure tests x a b u T ell)).symm
  rw [heq]
  exact hreal.tsum_ofReal_ne_top

/-- If one common stopped-Hoeffding budget works at every test point, the
finite union costs exactly the number of test points. -/
theorem largestPrimeStoppedBudget_le_card_mul
    (tests : ℕ → Finset ℕ) (u T : ℕ → ℕ → ℝ)
    (q : ℕ → ℝ)
    (hq : ∀ ell r, r ∈ tests ell →
      2 * Real.exp (-(u ell r) ^ 2 / (2 * T ell r)) ≤ q ell)
    (ell : ℕ) :
    largestPrimeStoppedBudget tests u T ell ≤
      (tests ell).card * q ell := by
  unfold largestPrimeStoppedBudget
  calc
    (∑ r ∈ tests ell,
        2 * Real.exp (-(u ell r) ^ 2 / (2 * T ell r)))
        ≤ ∑ _r ∈ tests ell, q ell := by
      gcongr with r hr
      exact hq ell r hr
    _ = (tests ell).card * q ell := by simp

/-- A summable cardinality-times-one-point budget is sufficient for the
simultaneous stopped estimate. -/
theorem ae_eventually_not_largestPrimeStoppedFailure_of_uniform
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (u T : ℕ → ℕ → ℝ) (q : ℕ → ℝ)
    (hu : ∀ ell r, r ∈ tests ell → 0 ≤ u ell r)
    (hT : ∀ ell r, r ∈ tests ell → 0 < T ell r)
    (hq : ∀ ell r, r ∈ tests ell →
      2 * Real.exp (-(u ell r) ^ 2 / (2 * T ell r)) ≤ q ell)
    (hsummable : Summable fun ell => (tests ell).card * q ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      omega ∉ largestPrimeStoppedFailure tests x a b u T ell := by
  apply ae_eventually_not_largestPrimeStoppedFailure_of_summable
    tests x a b u T hu hT
  apply Summable.of_nonneg_of_le
  · intro ell
    unfold largestPrimeStoppedBudget
    positivity
  · intro ell
    exact largestPrimeStoppedBudget_le_card_mul tests u T q hq ell
  · exact hsummable

/-- Outside the stopped-failure event, a deterministic quadratic-variation
bound forces the desired largest-prime bound at every selected test point. -/
theorem largestPrimeMain_lt_of_not_stoppedFailure
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (u T : ℕ → ℕ → ℝ) {omega : Omega} {ell r : ℕ}
    (hgood : omega ∉ largestPrimeStoppedFailure tests x a b u T ell)
    (hr : r ∈ tests ell)
    (hqv : largestPrimeQuadraticVariation omega
      (x ell r) (a ell r) (b ell r) ≤ T ell r) :
    |largestPrimeMain omega (x ell r) (a ell r) (b ell r)| < u ell r := by
  by_contra hnot
  apply hgood
  exact ⟨r, hr, le_of_not_gt hnot, hqv⟩

/-- Complete concentration conclusion from an almost-sure eventual
quadratic-variation estimate and a summable exact Hoeffding budget. -/
theorem ae_eventually_largestPrimeMain_lt_of_qv_and_summable
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (u T : ℕ → ℕ → ℝ)
    (hu : ∀ ell r, r ∈ tests ell → 0 ≤ u ell r)
    (hT : ∀ ell r, r ∈ tests ell → 0 < T ell r)
    (hbudget : Summable fun ell =>
      largestPrimeStoppedBudget tests u T ell)
    (hqv : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        largestPrimeQuadraticVariation omega
          (x ell r) (a ell r) (b ell r) ≤ T ell r) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |largestPrimeMain omega
          (x ell r) (a ell r) (b ell r)| < u ell r := by
  have hstop :=
    ae_eventually_not_largestPrimeStoppedFailure_of_summable
      tests x a b u T hu hT hbudget
  filter_upwards [hstop, hqv] with omega hstopOmega hqvOmega
  filter_upwards [hstopOmega, hqvOmega] with ell hstopEll hqvEll
  intro r hr
  exact largestPrimeMain_lt_of_not_stoppedFailure
    tests x a b u T hstopEll hr (hqvEll r hr)

end Problem520
end Erdos
