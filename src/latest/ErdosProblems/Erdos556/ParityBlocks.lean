import ErdosProblems.Erdos556.NearbyPathVertices
import Mathlib.Combinatorics.Pigeonhole

/-!
# A prescribed number of same-parity positions in one bounded interval
-/

namespace Erdos556

open Finset

theorem exists_same_parity_block (S : Finset ℕ) (N Q L : ℕ) (hQ : 0 < Q)
    (hS : ∀ i ∈ S, i < N)
    (hc : 2 * (N / Q + 1) * (L - 1) < S.card) :
    ∃ T : Finset ℕ, T ⊆ S ∧ T.card = L ∧
      ∀ i ∈ T, ∀ j ∈ T, i % 2 = j % 2 ∧ j < i + Q := by
  let f (i : ℕ) := (i / Q, i % 2)
  let B := range (N / Q + 1) ×ˢ range 2
  have hf : ∀ i ∈ S, f i ∈ B := by
    intro i hi
    apply mem_product.mpr
    refine ⟨mem_range.mpr ?_, mem_range.mpr (Nat.mod_lt _ (by decide))⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (hS i hi).le)
  have hBc : B.card * (L - 1) < S.card := by
    simpa only [B, card_product, card_range, Nat.mul_comm (N / Q + 1) 2] using hc
  obtain ⟨b, _, hb⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hBc
  obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (show L ≤ (S.filter (fun i => f i = b)).card by omega)
  refine ⟨T, hT.trans (filter_subset _ _), hTc, ?_⟩
  intro i hi j hj
  have hi' := (mem_filter.mp (hT hi)).2
  have hj' := (mem_filter.mp (hT hj)).2
  have heq := hi'.trans hj'.symm
  have hdiv : i / Q = j / Q := congrArg Prod.fst heq
  have hpar : i % 2 = j % 2 := congrArg Prod.snd heq
  refine ⟨hpar, ?_⟩
  have hiq := Nat.div_add_mod i Q
  have hjq := Nat.div_add_mod j Q
  have him := Nat.mod_lt i hQ
  have hjm := Nat.mod_lt j hQ
  rw [hdiv] at hiq
  omega

theorem parity_block_count_bound (N K L : ℕ) (hK : 0 < K) (hL : 0 < L)
    (hN : 8 * K * L ≤ N) :
    2 * (N / (8 * K * L) + 1) * (L - 1) < N / (2 * K) := by
  have hQ : 0 < 8 * K * L := by positivity
  have hq : 1 ≤ N / (8 * K * L) := (Nat.le_div_iff_mul_le hQ).mpr (by omega)
  have hmul := Nat.div_mul_le_self N (8 * K * L)
  have hdiv : 4 * L * (N / (8 * K * L)) ≤ N / (2 * K) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    nlinarith only [hmul]
  have hsub : L - 1 + 1 = L := by omega
  have hprod : 0 ≤ (N / (8 * K * L) - 1) * (L - 1) := Nat.zero_le _
  have hqsub : N / (8 * K * L) - 1 + 1 = N / (8 * K * L) := by omega
  nlinarith

#print axioms exists_same_parity_block
#print axioms parity_block_count_bound

end Erdos556
