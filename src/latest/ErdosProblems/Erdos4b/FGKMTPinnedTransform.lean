/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTInverseTransform
import ErdosProblems.Erdos4b.FGKMTPinnedLocal
import ErdosProblems.Erdos4b.FGKMTNormalizedTransform
import Mathlib.Algebra.BigOperators.Field

/-!
# Exact pinned transform of the original common coefficient vector

Restriction removes a coordinate from the divisor assignments, not from
the profile. The inverse with parameter `v-1` determines the new profile.
Its explicit finite product kernel will be estimated by the face mean.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι κ : Type*} [DecidableEq α] [Fintype α]
  [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype κ]

def mapPrimeAssignment (e : ι ↪ κ) (r : α → Option ι) : α → Option κ :=
  fun q => (r q).map e

def assignmentPinnedCoeffKernel (v : α → ℝ) (e : ι ↪ κ)
    (r : α → Option ι) (s : α → Option κ) : ℝ :=
  ∏ q, localPinnedCoeffKernel (v q) e (r q) (s q)

omit [Fintype κ] in
theorem assignmentPinnedCoeffKernel_eq_contraction {v : α → ℝ}
    (hv : ∀ q, v q - 1 ≠ 0) (e : ι ↪ κ)
    (r : α → Option ι) (s : α → Option κ) :
    (∑ d, assignmentInverseKernel (fun q => v q - 1) r d *
      assignmentCoeffKernel v (mapPrimeAssignment e d) s) =
        assignmentPinnedCoeffKernel v e r s := by
  simp only [assignmentInverseKernel, assignmentCoeffKernel, mapPrimeAssignment,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun q (d : Option ι) =>
    localInverseCoeff (v q - 1) (r q) d * localDivisorCoeff (v q) (d.map e) (s q))]
  simp only [localPinnedCoeffKernel_eq_contraction (hv _), assignmentPinnedCoeffKernel]

theorem finiteInverse_restrictedCoefficient {v : α → ℝ}
    (hv : ∀ q, v q - 1 ≠ 0) (e : ι ↪ κ) (Y : (α → Option κ) → ℝ)
    (r : α → Option ι) :
    finiteInverseCoefficientTransform (fun q => v q - 1)
        (fun d => finiteCoefficientTransform v Y (mapPrimeAssignment e d)) r =
      ∑ s, assignmentPinnedCoeffKernel v e r s * Y s := by
  unfold finiteInverseCoefficientTransform finiteCoefficientTransform
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ s, (∑ d, assignmentInverseKernel (fun q => v q - 1) r d *
        assignmentCoeffKernel v (mapPrimeAssignment e d) s) * Y s := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by simp only [assignmentPinnedCoeffKernel_eq_contraction hv]

def pinnedProfileTransform (v : α → ℝ) (e : ι ↪ κ) (F : (α → Option κ) → ℝ)
    (r : α → Option ι) : ℝ :=
  assignmentRowWeight (fun q => v q - 1) r *
    finiteInverseCoefficientTransform (fun q => v q - 1)
      (fun d => normalizedCoefficientTransform v F (mapPrimeAssignment e d)) r

theorem pinnedProfileTransform_eq_product {v : α → ℝ}
    (hv : ∀ q, v q - 1 ≠ 0) (e : ι ↪ κ) (F : (α → Option κ) → ℝ)
    (r : α → Option ι) :
    pinnedProfileTransform v e F r =
      ∑ s, (∏ q, localPinnedProfileKernel (v q) e (r q) (s q)) * F s := by
  unfold pinnedProfileTransform normalizedCoefficientTransform
  rw [finiteInverse_restrictedCoefficient hv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  simp only [localPinnedProfileKernel, assignmentRowWeight, assignmentPinnedCoeffKernel,
    Finset.prod_div_distrib, Finset.prod_mul_distrib]
  ring

theorem normalizedCoefficient_pinned_recovery {v : α → ℝ}
    (hv : ∀ q, v q - 1 ≠ 0)
    (hrow : ∀ r : α → Option ι, assignmentRowWeight (fun q => v q - 1) r ≠ 0)
    (e : ι ↪ κ) (F : (α → Option κ) → ℝ) :
    normalizedCoefficientTransform (fun q => v q - 1) (pinnedProfileTransform v e F) =
      fun d => normalizedCoefficientTransform v F (mapPrimeAssignment e d) := by
  have hcancel : (fun r => pinnedProfileTransform v e F r /
      assignmentRowWeight (fun q => v q - 1) r) =
      finiteInverseCoefficientTransform (fun q => v q - 1)
        (fun d => normalizedCoefficientTransform v F (mapPrimeAssignment e d)) := by
    funext r
    exact mul_div_cancel_left₀ _ (hrow r)
  unfold normalizedCoefficientTransform
  rw [hcancel]
  exact finiteCoefficientTransform_inverse hv _

theorem restrictedCoefficient_quadratic_decomposition {v : α → ℝ}
    (hv : ∀ q, v q - 1 ≠ 0)
    (hrow : ∀ r : α → Option ι, assignmentRowWeight (fun q => v q - 1) r ≠ 0)
    (e : ι ↪ κ) (F : (α → Option κ) → ℝ) :
    finiteSieveQuadratic (fun q => v q - 1)
        (fun d => normalizedCoefficientTransform v F (mapPrimeAssignment e d)) =
      (∑ r, (pinnedProfileTransform v e F r) ^ 2 /
        assignmentRowWeight (fun q => v q - 1) r) +
      ∑ r, ∑ s, pinnedProfileTransform v e F r *
        (pinnedProfileTransform v e F s - pinnedProfileTransform v e F r) *
          assignmentQuadraticKernel (fun q => v q - 1) r s /
            (assignmentRowWeight (fun q => v q - 1) r *
              assignmentRowWeight (fun q => v q - 1) s) := by
  rw [← normalizedCoefficient_pinned_recovery hv hrow e F]
  exact normalizedCoefficientTransform_diagonal_error hv _

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedProfileTransform_eq_product
#print axioms Erdos4b.FGKMT.normalizedCoefficient_pinned_recovery
#print axioms Erdos4b.FGKMT.restrictedCoefficient_quadratic_decomposition
