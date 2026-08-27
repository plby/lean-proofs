/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLocalInverse
import ErdosProblems.Erdos4b.FGKMTFiniteTransform

/-! # Two-sided inversion on the finite prime-assignment space -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

def assignmentInverseKernel (v : α → ℝ) (r d : α → Option ι) : ℝ :=
  ∏ q, localInverseCoeff (v q) (r q) (d q)

def finiteInverseCoefficientTransform (v : α → ℝ) (l : (α → Option ι) → ℝ)
    (r : α → Option ι) : ℝ :=
  ∑ d, assignmentInverseKernel v r d * l d

omit [DecidableEq α] [Fintype ι] in
theorem assignment_delta_product (r s : α → Option ι) :
    (∏ q, if r q = s q then (1 : ℝ) else 0) = if r = s then 1 else 0 := by
  by_cases h : r = s
  · subst s
    simp
  · rw [if_neg h]
    have hpoint : ∃ q, r q ≠ s q := by
      by_contra hn
      apply h
      funext q
      by_contra hq
      exact hn ⟨q, hq⟩
    obtain ⟨q, hq⟩ := hpoint
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

theorem assignmentCoeff_inverse_contraction {v : α → ℝ} (hv : ∀ q, v q ≠ 0)
    (d e : α → Option ι) :
    (∑ r, assignmentCoeffKernel v d r * assignmentInverseKernel v r e) =
      if d = e then 1 else 0 := by
  simp only [assignmentCoeffKernel, assignmentInverseKernel, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun q (r : Option ι) =>
    localDivisorCoeff (v q) (d q) r * localInverseCoeff (v q) r (e q))]
  simp only [localDivisor_inverse_contraction (hv _)]
  exact assignment_delta_product d e

theorem assignmentInverse_coeff_contraction {v : α → ℝ} (hv : ∀ q, v q ≠ 0)
    (r s : α → Option ι) :
    (∑ d, assignmentInverseKernel v r d * assignmentCoeffKernel v d s) =
      if r = s then 1 else 0 := by
  simp only [assignmentCoeffKernel, assignmentInverseKernel, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun q (d : Option ι) =>
    localInverseCoeff (v q) (r q) d * localDivisorCoeff (v q) d (s q))]
  simp only [localInverse_divisor_contraction (hv _)]
  exact assignment_delta_product r s

theorem finiteCoefficientTransform_inverse {v : α → ℝ} (hv : ∀ q, v q ≠ 0)
    (l : (α → Option ι) → ℝ) :
    finiteCoefficientTransform v (finiteInverseCoefficientTransform v l) = l := by
  funext d
  unfold finiteCoefficientTransform finiteInverseCoefficientTransform
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e, (∑ r, assignmentCoeffKernel v d r * assignmentInverseKernel v r e) * l e := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = l d := by simp [assignmentCoeff_inverse_contraction hv, ite_mul]

theorem finiteInverseCoefficientTransform_coeff {v : α → ℝ} (hv : ∀ q, v q ≠ 0)
    (Y : (α → Option ι) → ℝ) :
    finiteInverseCoefficientTransform v (finiteCoefficientTransform v Y) = Y := by
  funext r
  unfold finiteCoefficientTransform finiteInverseCoefficientTransform
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ s, (∑ d, assignmentInverseKernel v r d * assignmentCoeffKernel v d s) * Y s := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = Y r := by simp [assignmentInverse_coeff_contraction hv, ite_mul]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.finiteCoefficientTransform_inverse
#print axioms Erdos4b.FGKMT.finiteInverseCoefficientTransform_coeff
