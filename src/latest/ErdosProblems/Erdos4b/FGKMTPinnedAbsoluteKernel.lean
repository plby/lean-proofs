/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsoluteFaceMajorant

/-! # The literal pinned common/moved kernel and full quadratic error identity -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem pinned_assignmentAbsoluteKernel_split {m : ℕ} {p : α → ℕ}
    (hp : ∀ q, 2 ≤ p q) {r s : α → Option (Fin m)} (hrs : SamePrimeSupport r s) :
    |assignmentQuadraticKernel (fun q => (p q : ℝ) - 1) r s| /
        (assignmentRowWeight (fun q => (p q : ℝ) - 1) r *
          assignmentRowWeight (fun q => (p q : ℝ) - 1) s) =
      pinnedCommonKernelWeight m p (commonAssignment r s) *
        pinnedMovedKernelWeight m p (movedAssignment r s) := by
  have hv (q : α) : (1 : ℝ) ≤ (p q : ℝ) - 1 := by
    have hq : (2 : ℝ) ≤ p q := by exact_mod_cast hp q
    linarith
  have h := assignmentAbsoluteKernel_split hv hrs
  simpa only [pinnedCommonKernelWeight, pinnedMovedKernelWeight, Fintype.card_fin,
    sub_sub, show (1 : ℝ) + 1 = 2 by norm_num, add_comm] using h

def pinnedSieveVariationTerm (m R : ℕ) (p : α → ℕ) (j : Fin (m + 1))
    (r s : α → Option (Fin m)) : ℝ :=
  commonPinnedProfile m R p j r * (commonPinnedProfile m R p j s - commonPinnedProfile m R p j r) *
    assignmentQuadraticKernel (fun q => (p q : ℝ) - 1) r s /
      (assignmentRowWeight (fun q => (p q : ℝ) - 1) r *
        assignmentRowWeight (fun q => (p q : ℝ) - 1) s)

theorem commonPinnedQuadratic_sub_diagonal {m M R : ℕ} (hm : 1 ≤ m)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M)
    (j : Fin (m + 1)) :
    commonPinnedQuadratic m M R j - commonPinnedDiagonal m M R j =
      ∑ r : commonPrimeUniverse M R → Option (Fin m), ∑ s,
        pinnedSieveVariationTerm m R (fun q => q.val) j r s := by
  have hlarge (q : commonPrimeUniverse M R) : m + 1 < q.val := by
    have h := commonPrimeUniverse_large hsmall q
    nlinarith
  rw [commonPinnedQuadratic, commonPinnedDiagonal_eq_row,
    commonPinnedCoefficient_quadratic_decomposition commonPrimeUniverse_prime hlarge,
    add_sub_cancel_left]
  rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinned_assignmentAbsoluteKernel_split
#print axioms Erdos4b.FGKMT.commonPinnedQuadratic_sub_diagonal
