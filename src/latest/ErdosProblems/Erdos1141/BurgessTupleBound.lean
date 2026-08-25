import ErdosProblems.Erdos1141.BurgessStarWeights
import ErdosProblems.Erdos1141.RepeatedTuples

/-!
# An arbitrary-order moment bound from singleton correlation estimates
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem sum_tuple_correlations_le {α : Type*} [Fintype α] (r : ℕ)
    (corr : (Fin (2 * r) → α) → ℝ) (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) {B C T : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b : α, w a b ≤ T)
    (htrivial : ∀ v, corr v ≤ B)
    (hsingle : ∀ (v : Fin (2 * r) → α) (i : Fin (2 * r)),
      (∀ j, j ≠ i → v j ≠ v i) → corr v ≤ C * starWeight w v i) :
    (∑ v : Fin (2 * r) → α, corr v) ≤
      (Fintype.card α : ℝ) ^ r * (r : ℝ) ^ (2 * r) * B +
        C * (2 * r : ℕ) * (Fintype.card α : ℝ) * T ^ (2 * r - 1) := by
  classical
  have hpoint (v : Fin (2 * r) → α) :
      corr v ≤ (if RepeatedTuple v then B else 0) + C * ∑ i, starWeight w v i := by
    have hweight : 0 ≤ ∑ i, starWeight w v i :=
      Finset.sum_nonneg fun i _ => starWeight_nonneg w hw v i
    by_cases hv : RepeatedTuple v
    · rw [if_pos hv]
      exact (htrivial v).trans (le_add_of_nonneg_right (mul_nonneg hC hweight))
    · rw [if_neg hv, zero_add]
      have hsi : ∃ i : Fin (2 * r), ∀ j, j ≠ i → v j ≠ v i := by
        simpa only [RepeatedTuple, not_forall, not_exists, not_and] using hv
      obtain ⟨i, hi⟩ := hsi
      exact (hsingle v i hi).trans (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => starWeight_nonneg w hw v j) (Finset.mem_univ i)) hC)
  have hdiag : (∑ v : Fin (2 * r) → α, if RepeatedTuple v then B else 0) ≤
      (Fintype.card α : ℝ) ^ r * (r : ℝ) ^ (2 * r) * B := by
    rw [← Finset.sum_filter]
    change (∑ _v ∈ repeatedTuples α (2 * r), B) ≤ _
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hB
    exact_mod_cast repeatedTuples_card_le α r
  have hweights : (∑ v : Fin (2 * r) → α, ∑ i, starWeight w v i) ≤
      (2 * r : ℕ) * (Fintype.card α : ℝ) * T ^ (2 * r - 1) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i : Fin (2 * r), (Fintype.card α : ℝ) * T ^ (2 * r - 1) :=
        Finset.sum_le_sum fun i _ => sum_starWeight_le w hw hrow i
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ ∑ v : Fin (2 * r) → α,
        ((if RepeatedTuple v then B else 0) + C * ∑ i, starWeight w v i) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (∑ v : Fin (2 * r) → α, if RepeatedTuple v then B else 0) +
        C * ∑ v : Fin (2 * r) → α, ∑ i, starWeight w v i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
      have h := add_le_add hdiag (mul_le_mul_of_nonneg_left hweights hC)
      simpa only [mul_assoc] using h

end Pollack17.Burgess
