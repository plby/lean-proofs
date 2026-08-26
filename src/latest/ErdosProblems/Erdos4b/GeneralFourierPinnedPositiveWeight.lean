/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightExpansion

/-!
# The reduced pinned integer weight is a nonnegative real square

This holds even before the natural-base-point margin is imposed. It
justifies applying the weighted singular-factor inequality to the
literal reduced weight on every auxiliary prime.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

open Classical in
def pinnedSourceRealIntegerWeight {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (w m p₀ q : ℕ) (LD LE : ℝ) : ℝ :=
  (∑ d ∈ cutoffDivisorTupleSupport (PinnedShiftIndex h) P,
    ∑ e ∈ cutoffDivisorTupleSupport (PinnedShiftIndex h) P,
      if PinnedIntegerSingleCondition h w m p₀ q d e then
        sourceAnalyticSelbergCoefficient S F G LD LE
          (extendPinnedDivisorTuple h d) (extendPinnedDivisorTuple h e) else 0) ^ 2

theorem pinnedSourceRealIntegerWeight_nonneg
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (w m p₀ q : ℕ) (LD LE : ℝ) :
    0 ≤ pinnedSourceRealIntegerWeight S F G h P w m p₀ q LD LE := sq_nonneg _

theorem ofReal_pinnedSourceRealIntegerWeight
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (w m p₀ q : ℕ) (LD LE : ℝ) :
    (pinnedSourceRealIntegerWeight S F G h P w m p₀ q LD LE : ℂ) =
      pinnedSourceIntegerWeight S F G h P w m p₀ q LD LE := by
  classical
  unfold pinnedSourceRealIntegerWeight pinnedSourceIntegerWeight
  simp only [Complex.ofReal_pow, Complex.ofReal_sum, apply_ite Complex.ofReal,
    Complex.ofReal_zero, sourceAnalyticSelbergCoefficient_extend_eq_pinned]

theorem pinnedSourceIntegerWeight_re_nonneg
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (w m p₀ q : ℕ) (LD LE : ℝ) :
    0 ≤ (pinnedSourceIntegerWeight S F G h P w m p₀ q LD LE).re := by
  rw [← ofReal_pinnedSourceRealIntegerWeight, Complex.ofReal_re]
  exact pinnedSourceRealIntegerWeight_nonneg S F G h P w m p₀ q LD LE

end

end Erdos4b
