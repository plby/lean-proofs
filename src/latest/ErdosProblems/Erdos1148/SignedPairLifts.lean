import ErdosProblems.Erdos1148.ClosePairImage
import ErdosProblems.Erdos1148.FlowStabilizer

/-! # Comparing close pairs with chosen real lifts of their forms -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma specialLinear_inv_neg (g : SL(2, ℝ)) : (-g)⁻¹ = -(g⁻¹) := by
  apply inv_eq_of_mul_eq_one_right
  rw [neg_mul_neg, mul_inv_cancel]

lemma relative_mul_flow (g h : SL(2, ℝ)) (s t : ℝ) :
    (g * diagonalFlow s)⁻¹ * (h * diagonalFlow t) =
      diagonalFlow (-s) * (g⁻¹ * h) * diagonalFlow t := by
  rw [mul_inv_rev, diagonalFlow_neg]
  simp only [mul_assoc]

lemma mem_signedCloseDiagonalFlowTimes_iff (g : SL(2, ℝ)) (η : ℝ) (s t : ℝ) :
    ![s, t] ∈ signedCloseDiagonalFlowTimes g η ↔
      EntryCloseOne η (diagonalFlow (-s) * g * diagonalFlow t) ∨
      EntryCloseOne η (-(diagonalFlow (-s) * g * diagonalFlow t)) := by
  simp only [signedCloseDiagonalFlowTimes, Set.mem_union, closeDiagonalFlowTimes,
    Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_neg, neg_mul]

theorem close_pair_mem_chosen_lift_image {g h g₀ h₀ : SL(2, ℝ)} {η : ℝ}
    (hg : formAction g₀ (splitForm ℝ) = formAction g (splitForm ℝ))
    (hh : formAction h₀ (splitForm ℝ) = formAction h (splitForm ℝ))
    (hclose : EntryCloseOne η (g⁻¹ * h)) :
    (modularMk g, modularMk h) ∈ finPairFlowCurve g₀ h₀ ''
      signedCloseDiagonalFlowTimes (g₀⁻¹ * h₀) η := by
  obtain ⟨s, hs⟩ := exists_signed_flow_of_formAction_eq hg
  obtain ⟨t, ht⟩ := exists_signed_flow_of_formAction_eq hh
  refine ⟨![s, t], ?_, ?_⟩
  · rw [mem_signedCloseDiagonalFlowTimes_iff]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Or.inl (by simpa only [relative_mul_flow] using hclose)
    · exact Or.inr (by simpa only [mul_neg, relative_mul_flow] using hclose)
    · exact Or.inr (by
        simpa only [specialLinear_inv_neg, neg_mul, relative_mul_flow] using hclose)
    · exact Or.inl (by
        simpa only [specialLinear_inv_neg, neg_mul_neg, relative_mul_flow] using hclose)
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp only [finPairFlowCurve, Matrix.cons_val_zero, Matrix.cons_val_one,
        modularFlowCurve, modularMk_neg]

lemma finPairFlowCurve_integral_mul (γ : SL(2, ℤ)) (g h : SL(2, ℝ)) :
    finPairFlowCurve ((γ : SL(2, ℝ)) * g) ((γ : SL(2, ℝ)) * h) = finPairFlowCurve g h := by
  funext x
  simp only [finPairFlowCurve, modularFlowCurve, mul_assoc, modularMk_integral_mul]

end Erdos1148.DukeArithmetic
