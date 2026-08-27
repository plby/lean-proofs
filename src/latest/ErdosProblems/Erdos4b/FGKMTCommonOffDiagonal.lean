/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentVariation
import ErdosProblems.Erdos4b.FGKMTAssignmentPairCode
import ErdosProblems.Erdos4b.FGKMTAssignmentEulerMoment

/-!
# A finite off-diagonal bound for the actual common coefficients

The exact error is bounded by a single absolute-kernel majorant sum
times the moved-prime logarithmic Euler moment. Its constant is uniform
in the dimension, scale, and finite prime universe.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

def commonKernelWeight (k : ℕ) (p : α → ℕ) (r : α → Option (Fin k)) : ℝ :=
  assignmentScalarWeight (fun q => ((p q : ℝ) - 1) / ((p q : ℝ) - k) ^ 2) r

def movedKernelWeight (k : ℕ) (p : α → ℕ) (r : α → Option (Fin k)) : ℝ :=
  assignmentScalarWeight (fun q => 1 / ((p q : ℝ) - k) ^ 2) r

def absoluteAssignmentMajorantSum (k R : ℕ) (p : α → ℕ) : ℝ :=
  ∑ r, primeAssignmentMajorant k R p r ^ 2 * commonKernelWeight k p r

def commonSieveVariationTerm (k R : ℕ) (p : α → ℕ)
    (r s : α → Option (Fin k)) : ℝ :=
  primeAssignmentProfile k R p r *
    (primeAssignmentProfile k R p s - primeAssignmentProfile k R p r) *
    assignmentQuadraticKernel (fun q => (p q : ℝ)) r s /
      (assignmentRowWeight (fun q => (p q : ℝ)) r * assignmentRowWeight (fun q => (p q : ℝ)) s)

open scoped Classical in
def pairVariationMajorant (k R : ℕ) (p : α → ℕ) (r s : α → Option (Fin k)) : ℝ :=
  if SamePrimeSupport r s then
    (primeAssignmentMajorant k R p (commonAssignment r s) ^ 2 *
      commonKernelWeight k p (commonAssignment r s)) * movedKernelWeight k p (movedAssignment r s) *
        Real.log (assignmentPrimeProduct p (movedAssignment r s))
  else 0

omit [DecidableEq α] in
theorem commonKernelWeight_nonneg (k : ℕ) {p : α → ℕ} (hp : ∀ q, 0 < p q)
    (r : α → Option (Fin k)) : 0 ≤ commonKernelWeight k p r := by
  apply assignmentScalarWeight_nonneg
  intro q
  exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hp q)) (sq_nonneg _)

omit [DecidableEq α] [Fintype α] in
theorem exists_commonSieveVariationTerm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : Type*) [DecidableEq β] [Fintype β],
      ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (R : ℕ) (p : β → ℕ), (∀ q, k < p q) → ∀ r s : β → Option (Fin k),
        |commonSieveVariationTerm k R p r s| ≤
          (C * sieveProfileScale k / Real.log R) * pairVariationMajorant k R p r s := by
  obtain ⟨C, hC, hbound⟩ := exists_primeAssignmentProfile_product_variation_bound
  refine ⟨C, hC, ?_⟩
  intro β _ _ k hk hlog R p hp r s
  classical
  have hp0 : ∀ q, 0 < p q := fun q => hk.trans (hp q)
  have hp1 : ∀ q, (1 : ℝ) ≤ p q := fun q => by exact_mod_cast hp0 q
  by_cases hrs : SamePrimeSupport r s
  · have hden := mul_pos (primeAssignmentRowWeight_pos hp r) (primeAssignmentRowWeight_pos hp s)
    have hweight : 0 ≤ commonKernelWeight k p (commonAssignment r s) *
        movedKernelWeight k p (movedAssignment r s) :=
      mul_nonneg (commonKernelWeight_nonneg k hp0 _)
        (assignmentScalarWeight_nonneg (fun q => div_nonneg zero_le_one (sq_nonneg _)) _)
    have hkernel := assignmentAbsoluteKernel_split hp1 hrs
    simp only [Fintype.card_fin] at hkernel
    change |assignmentQuadraticKernel _ r s| / (assignmentRowWeight _ r * assignmentRowWeight _ s) =
      commonKernelWeight k p (commonAssignment r s) * movedKernelWeight k p (movedAssignment r s)
      at hkernel
    rw [commonSieveVariationTerm, abs_div, abs_mul, abs_of_pos hden, mul_div_assoc,
      hkernel, pairVariationMajorant, if_pos hrs]
    calc
      _ ≤ ((C * sieveProfileScale k * primeAssignmentMajorant k R p (commonAssignment r s) ^ 2) *
          (Real.log (assignmentPrimeProduct p (movedAssignment r s)) / Real.log R)) *
          (commonKernelWeight k p (commonAssignment r s) *
            movedKernelWeight k p (movedAssignment r s)) :=
        mul_le_mul_of_nonneg_right (hbound β hk hlog R p hp0 r s hrs) hweight
      _ = _ := by ring
  · have hzero : assignmentQuadraticKernel (fun q => (p q : ℝ)) r s = 0 := by
      by_contra hne
      exact hrs (samePrimeSupport_of_kernel_ne_zero _ hne)
    simp [commonSieveVariationTerm, pairVariationMajorant, hrs, hzero]

theorem sum_pairVariationMajorant_le (k R : ℕ) {p : α → ℕ} (hp : ∀ q, 0 < p q) :
    (∑ r, ∑ s, pairVariationMajorant k R p r s) ≤
      absoluteAssignmentMajorantSum k R p *
        (Real.exp (∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2) *
          ∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2 * Real.log (p q)) := by
  classical
  let H := fun r : α → Option (Fin k) =>
    primeAssignmentMajorant k R p r ^ 2 * commonKernelWeight k p r
  have hH : ∀ r, 0 ≤ H r := fun r => mul_nonneg (sq_nonneg _) (commonKernelWeight_nonneg k hp r)
  have hb (q : α) : 0 ≤ 1 / ((p q : ℝ) - k) ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
  have hsum := sum_common_moved_weight_le_product H hH (fun q => 1 / ((p q : ℝ) - k) ^ 2) hb p
  have hmoment := sum_assignmentScalarWeight_logProduct_le (β := Fin k × Fin k) hp hb
  have hcard : (Fintype.card (Fin k × Fin k) : ℝ) = (k : ℝ) ^ 2 := by simp [pow_two]
  rw [hcard] at hmoment
  simp only [mul_one_div] at hmoment
  exact hsum.trans (mul_le_mul_of_nonneg_left hmoment (Finset.sum_nonneg fun r _hr => hH r))

omit [DecidableEq α] [Fintype α] in
theorem exists_commonSieveCoefficient_offDiagonal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : Type*) [DecidableEq β] [Fintype β],
      ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (R : ℕ) (p : β → ℕ), (∀ q, k < p q) →
        |finiteSieveQuadratic (fun q => (p q : ℝ)) (commonSieveCoefficient k R p) -
          ∑ r, primeAssignmentProfile k R p r ^ 2 / assignmentRowWeight (fun q => (p q : ℝ)) r| ≤
        (C * sieveProfileScale k / Real.log R) * absoluteAssignmentMajorantSum k R p *
          (Real.exp (∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2) *
            ∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2 * Real.log (p q)) := by
  obtain ⟨C, hC, hbound⟩ := exists_commonSieveVariationTerm_bound
  refine ⟨C, hC, ?_⟩
  intro β _ _ k hk hlog R p hp
  have hp0 : ∀ q, 0 < p q := fun q => hk.trans (hp q)
  have hv : ∀ q, (p q : ℝ) ≠ 0 := fun q => by exact_mod_cast (hp0 q).ne'
  have ha : 0 ≤ C * sieveProfileScale k / Real.log R :=
    div_nonneg (mul_nonneg hC.le (zero_le_one.trans (profile_scales_bounds hk hlog).1))
      (Real.log_natCast_nonneg _)
  rw [commonSieveCoefficient, normalizedCoefficientTransform_diagonal_error hv, add_sub_cancel_left]
  change |∑ r : β → Option (Fin k), ∑ s, commonSieveVariationTerm k R p r s| ≤ _
  calc
    _ ≤ ∑ r : β → Option (Fin k), |∑ s, commonSieveVariationTerm k R p r s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : β → Option (Fin k), ∑ s, |commonSieveVariationTerm k R p r s| :=
      Finset.sum_le_sum fun r _hr => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : β → Option (Fin k), ∑ s,
        (C * sieveProfileScale k / Real.log R) * pairVariationMajorant k R p r s :=
      Finset.sum_le_sum fun r _hr => Finset.sum_le_sum fun s _hs => hbound β hk hlog R p hp r s
    _ = (C * sieveProfileScale k / Real.log R) * ∑ r, ∑ s, pairVariationMajorant k R p r s := by
      simp only [Finset.mul_sum]
    _ ≤ (C * sieveProfileScale k / Real.log R) *
        (absoluteAssignmentMajorantSum k R p *
          (Real.exp (∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2) *
            ∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2 * Real.log (p q))) :=
      mul_le_mul_of_nonneg_left (sum_pairVariationMajorant_le k R hp0) ha
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonSieveVariationTerm_bound
#print axioms Erdos4b.FGKMT.exists_commonSieveCoefficient_offDiagonal_bound
