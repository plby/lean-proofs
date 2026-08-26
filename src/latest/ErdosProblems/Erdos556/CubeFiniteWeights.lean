import ErdosProblems.Erdos556.CubeWeights
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite weight estimates for the terminal cube configurations
-/

namespace Erdos556

open Finset

theorem sum_sq_bound_of_card_le {I : Type*} (S : Finset I) (f : I → ℝ)
    (m : ℕ) (hcard : S.card ≤ m) :
    (∑ i ∈ S, f i) ^ 2 ≤ (m : ℝ) * ∑ i ∈ S, f i ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq S f (fun _ => (1 : ℝ))
  have h' : (∑ i ∈ S, f i) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
    simpa only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one, mul_comm] using h
  apply h'.trans
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
  exact sum_nonneg fun i _ => sq_nonneg (f i)

theorem sum_weights_le_card {I : Type*} (S : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ S, f i ≤ 1) : (∑ i ∈ S, f i) ≤ S.card := by
  calc
    (∑ i ∈ S, f i) ≤ ∑ _i ∈ S, (1 : ℝ) := sum_le_sum hf
    _ = S.card := by simp

theorem weights_eq_one_of_maximal_sum {I : Type*} (S : Finset I) (f : I → ℝ)
    (m : ℕ) (hcard : S.card ≤ m) (hf : ∀ i ∈ S, f i ≤ 1)
    (hsum : ∑ i ∈ S, f i = (m : ℝ)) : S.card = m ∧ ∀ i ∈ S, f i = 1 := by
  have hcR : (m : ℝ) ≤ S.card := by rw [← hsum]; exact sum_weights_le_card S f hf
  have hc : S.card = m := by exact_mod_cast le_antisymm (by exact_mod_cast hcard) hcR
  refine ⟨hc, ?_⟩
  intro i hi
  by_contra hne
  have hlt : (∑ j ∈ S, f j) < ∑ _j ∈ S, (1 : ℝ) :=
    sum_lt_sum hf ⟨i, hi, lt_of_le_of_ne (hf i hi) hne⟩
  simpa only [hsum, sum_const, nsmul_eq_mul, mul_one, hc, lt_self_iff_false] using hlt

theorem IsCubeWeight.edge_sum_sq_bound {w : CubeProfile → ℝ} (hw : IsCubeWeight w) :
    (∑ p ∈ positiveEdgeProfiles w, w p) ^ 2 ≤ 4 * ∑ p ∈ positiveEdgeProfiles w, w p ^ 2 := by
  exact sum_sq_bound_of_card_le (positiveEdgeProfiles w) w 4 hw.positive_edges_card_le_four

#print axioms weights_eq_one_of_maximal_sum
#print axioms IsCubeWeight.edge_sum_sq_bound

end Erdos556
