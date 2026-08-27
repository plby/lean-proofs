/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsoluteKernel
import ErdosProblems.Erdos4b.FGKMTCommonCoefficients

/-!
# Absolute column sums of the common coefficient transform

Each present prime has absolute column sum `1 + p`. Dividing by the
row factor `p - k` costs at most two when `p >= 2*k + 1`.
All estimates are finite and keep the full coefficient vector.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

omit [DecidableEq α] [Fintype α] in
theorem sum_abs_localDivisorCoeff {v : ℝ} (hv : 0 ≤ v) (r : Option ι) :
    (∑ d, |localDivisorCoeff v d r|) = if r = none then 1 else 1 + v := by
  cases r with
  | none => simp [Fintype.sum_option, localDivisorCoeff]
  | some i =>
    simp [Fintype.sum_option, localDivisorCoeff, apply_ite abs, abs_of_nonneg hv]

theorem sum_abs_assignmentCoeffKernel {v : α → ℝ} (hv : ∀ q, 0 ≤ v q)
    (r : α → Option ι) :
    (∑ d, |assignmentCoeffKernel v d r|) =
      assignmentScalarWeight (fun q => 1 + v q) r := by
  simp only [assignmentCoeffKernel, Finset.abs_prod]
  rw [← Fintype.prod_sum (fun q d => |localDivisorCoeff (v q) d (r q)|)]
  simp only [sum_abs_localDivisorCoeff (hv _), assignmentScalarWeight]

theorem finiteCoefficientTransform_l1_le {v : α → ℝ} (hv : ∀ q, 0 ≤ v q)
    (Y : (α → Option ι) → ℝ) :
    (∑ d, |finiteCoefficientTransform v Y d|) ≤
      ∑ r, |Y r| * assignmentScalarWeight (fun q => 1 + v q) r := by
  calc
    _ ≤ ∑ d : α → Option ι, ∑ r : α → Option ι,
        |assignmentCoeffKernel v d r * Y r| := by
      exact Finset.sum_le_sum fun d _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r : α → Option ι, |Y r| * ∑ d : α → Option ι,
        |assignmentCoeffKernel v d r| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [abs_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      exact mul_comm _ _
    _ = _ := by simp only [sum_abs_assignmentCoeffKernel hv]

omit [DecidableEq α] in
theorem assignmentColumn_div_row_le_two {k : ℕ} {p : α → ℕ}
    (hp : ∀ q, 2 * k + 1 ≤ p q) (r : α → Option (Fin k)) :
    assignmentScalarWeight (fun q => 1 + (p q : ℝ)) r /
        assignmentRowWeight (fun q => (p q : ℝ)) r ≤
      assignmentScalarWeight (fun _ => 2) r := by
  unfold assignmentScalarWeight assignmentRowWeight
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro q _hq
    cases r q with
    | none => norm_num [localRowWeight]
    | some i =>
      simp only [Option.some_ne_none, if_false, localRowWeight, Fintype.card_fin]
      apply div_nonneg (by positivity)
      have hh : (k : ℝ) < p q := by exact_mod_cast (show k < p q by have := hp q; omega)
      exact sub_nonneg.mpr hh.le
  · intro q _hq
    cases r q with
    | none => norm_num [localRowWeight]
    | some i =>
      simp only [Option.some_ne_none, if_false, localRowWeight, Fintype.card_fin]
      have hh : 2 * (k : ℝ) + 1 ≤ p q := by exact_mod_cast hp q
      have hpos : 0 < (p q : ℝ) - k := by have := Nat.cast_nonneg (α := ℝ) k; linarith
      apply (div_le_iff₀ hpos).mpr
      linarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.finiteCoefficientTransform_l1_le
#print axioms Erdos4b.FGKMT.assignmentColumn_div_row_le_two
