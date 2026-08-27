/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsoluteKernel
import BoundedGaps.Maynard.MaynardArithmeticBounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# Product-radius assignment counts and their weighted square sum

Unique factorization injects the supported assignments into positive
integer tuples. The existing harmonic tuple count is uniform in the
dimension. For labels at least four, the square of the weight two per
selected prime is bounded by the selected-prime product itself.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

def assignmentProductSupport (k R : ℕ) (p : α → ℕ) : Finset (α → Option (Fin k)) :=
  Finset.univ.filter (fun r => assignmentPrimeProduct p r < R)

theorem mem_assignmentProductSupport {k R : ℕ} {p : α → ℕ}
    {r : α → Option (Fin k)} :
    r ∈ assignmentProductSupport k R p ↔ assignmentPrimeProduct p r < R := by
  simp only [assignmentProductSupport, Finset.mem_filter, Finset.mem_univ, true_and]

theorem assignmentPrimeTuple_mem_positiveProductTuples {k R : ℕ} {p : α → ℕ}
    (hp : ∀ q, 0 < p q) {r : α → Option (Fin k)}
    (hr : r ∈ assignmentProductSupport k R p) :
    assignmentPrimeTuple p r ∈ BoundedGaps.Maynard.positiveProductTuples (Fin k) R := by
  have hprod := (mem_assignmentProductSupport.mp hr).le
  have hpos := assignmentPrimeProduct_pos hp r
  apply BoundedGaps.Maynard.mem_positiveProductTuples_iff.mpr
  refine ⟨fun i => Finset.mem_Icc.mpr ⟨assignmentPrimeTuple_pos hp r i, ?_⟩, ?_⟩
  · apply (Nat.le_of_dvd hpos ?_).trans hprod
    rw [← prod_assignmentPrimeTuple]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  · simpa only [prod_assignmentPrimeTuple] using hprod

theorem card_assignmentProductSupport_le {k R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) :
    ((assignmentProductSupport k R p).card : ℝ) ≤
      (R : ℝ) * (1 + Real.log R) ^ k := by
  have hcard : (assignmentProductSupport k R p).card ≤
      (BoundedGaps.Maynard.positiveProductTuples (Fin k) R).card := by
    apply Finset.card_le_card_of_injOn (assignmentPrimeTuple p)
    · intro r hr
      exact assignmentPrimeTuple_mem_positiveProductTuples (fun q => (hp q).pos) hr
    · exact (assignmentPrimeTuple_injective hp hinj).injOn
  calc
    _ ≤ ((BoundedGaps.Maynard.positiveProductTuples (Fin k) R).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ _ := by
      simpa only [Fintype.card_fin] using
        BoundedGaps.Maynard.card_positiveProductTuples_le_one_add_log (Fin k) R

omit [DecidableEq α] in
theorem assignmentScalarWeight_two_sq_le_product {k : ℕ} {p : α → ℕ}
    (hp : ∀ q, 4 ≤ p q) (r : α → Option (Fin k)) :
    assignmentScalarWeight (fun _ => 2) r ^ 2 ≤ (assignmentPrimeProduct p r : ℝ) := by
  unfold assignmentScalarWeight assignmentPrimeProduct
  rw [← Finset.prod_pow, Nat.cast_prod]
  apply Finset.prod_le_prod
  · intro q _hq
    exact sq_nonneg _
  · intro q _hq
    by_cases hh : r q = none
    · simp only [if_pos hh, one_pow, Nat.cast_one, le_refl]
    · simp only [if_neg hh]
      norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
      exact_mod_cast hp q

theorem sum_two_weights_sq_le_radius_card {k R : ℕ} {p : α → ℕ}
    (hp : ∀ q, 4 ≤ p q) :
    (∑ r ∈ assignmentProductSupport k R p,
        assignmentScalarWeight (fun _ => 2) r) ^ 2 ≤
      (R : ℝ) * ((assignmentProductSupport k R p).card : ℝ) ^ 2 := by
  calc
    _ ≤ ((assignmentProductSupport k R p).card : ℝ) *
        ∑ r ∈ assignmentProductSupport k R p,
          assignmentScalarWeight (fun _ => 2) r ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ ((assignmentProductSupport k R p).card : ℝ) *
        ∑ _r ∈ assignmentProductSupport k R p, (R : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro r hr
      exact (assignmentScalarWeight_two_sq_le_product hp r).trans
        (by exact_mod_cast (mem_assignmentProductSupport.mp hr).le)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.card_assignmentProductSupport_le
#print axioms Erdos4b.FGKMT.sum_two_weights_sq_le_radius_card
