import Mathlib
import Mathlib.Data.Fintype.CardEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite factorial-count identities

These identities are the combinatorial layer behind the manuscript's
factorial-moment argument.  They are stated independently of probability so
that the later integration step cannot conceal any tuple-multiplicity or
diagonal convention.
-/

open Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- Multiplying a falling factorial by its base either marks one of the
existing positions or appends a new distinct position. -/
theorem mul_descFactorial_eq (n r : ℕ) :
    n * n.descFactorial r =
      r * n.descFactorial r + n.descFactorial (r + 1) := by
  by_cases hrn : r ≤ n
  · rw [Nat.descFactorial_succ, ← add_mul, Nat.add_sub_of_le hrn]
  · have hnr : n < r := Nat.lt_of_not_ge hrn
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hnr,
      Nat.descFactorial_eq_zero_iff_lt.mpr (hnr.trans_le (Nat.le_succ r))]
    simp

theorem descFactorial_mul_eq (n r : ℕ) :
    n.descFactorial r * n =
      r * n.descFactorial r + n.descFactorial (r + 1) := by
  rw [Nat.mul_comm, mul_descFactorial_eq]

/-- Ordinary powers are finite nonnegative linear combinations of falling
factorials, with Stirling numbers of the second kind as coefficients. -/
theorem pow_eq_sum_stirlingSecond_mul_descFactorial (n r : ℕ) :
    n ^ r =
      ∑ j ∈ range (r + 1), Nat.stirlingSecond r j * n.descFactorial j := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, ih, Finset.sum_mul]
      simp_rw [mul_assoc, descFactorial_mul_eq]
      simp_rw [mul_add]
      rw [sum_add_distrib]
      have hshift :
          (∑ j ∈ range (r + 1),
              Nat.stirlingSecond r j * (j * n.descFactorial j)) =
            ∑ j ∈ range (r + 1),
              ((j + 1) * Nat.stirlingSecond r (j + 1)) *
                n.descFactorial (j + 1) := by
        rw [sum_range_succ' _ r, sum_range_succ]
        simp only [mul_zero, Nat.stirlingSecond_eq_zero_of_lt
          (Nat.lt_succ_self r), zero_mul, add_zero]
        apply sum_congr rfl
        intro j _
        ring
      rw [hshift, ← sum_add_distrib]
      conv_rhs =>
        rw [sum_range_succ' _ (r + 1)]
      simp only [Nat.stirlingSecond_succ_zero, zero_mul, add_zero]
      apply sum_congr rfl
      intro j hj
      rw [Nat.stirlingSecond_succ_succ]
      ring

/-- Ordered distinct `r`-tuples selected from a finite set are embeddings
from `Fin r` into that set.  Their cardinal is the falling factorial. -/
theorem card_orderedDistinctTuples {I : Type*} [DecidableEq I]
    (s : Finset I) (r : ℕ) :
    Fintype.card (Fin r ↪ s) = s.card.descFactorial r := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]

/-- Integrated form of the Stirling identity.  Thus uniform bounds for all
falling-factorial moments up to order `r` imply a bound for the ordinary
`r`-th moment, with no informal appeal to uniform integrability. -/
theorem integral_count_pow_eq_sum_factorialMoments
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (X : Ω → ℕ) (r : ℕ)
    (hInt : ∀ j ∈ range (r + 1),
      MeasureTheory.Integrable
        (fun ω ↦ ((X ω).descFactorial j : ℝ)) μ) :
    ∫ ω, (X ω : ℝ) ^ r ∂μ =
      ∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) *
        ∫ ω, ((X ω).descFactorial j : ℝ) ∂μ := by
  have hpoint :
      (fun ω : Ω ↦ (X ω : ℝ) ^ r) =
        fun ω : Ω ↦
          ∑ j ∈ range (r + 1),
            (Nat.stirlingSecond r j : ℝ) *
              ((X ω).descFactorial j : ℝ) := by
    funext ω
    norm_cast
    exact pow_eq_sum_stirlingSecond_mul_descFactorial (X ω) r
  rw [hpoint, MeasureTheory.integral_finset_sum]
  · apply sum_congr rfl
    intro j _
    exact MeasureTheory.integral_const_mul _ _
  · intro j hj
    exact (hInt j hj).const_mul _

end

end Erdos1002
