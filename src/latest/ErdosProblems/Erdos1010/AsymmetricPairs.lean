import ErdosProblems.Erdos1010.MissingPairs

/-! # Asymmetric pair rigidity at twice the maximum missing degree -/

open Finset

namespace Erdos1010

open Bipartite

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma asymmetric_pair_rigidity (M : Finset (A × B)) (k : ℤ) (U : Finset A) (Z : Finset B)
    (hU : U.card = 2) (hZ : Z.card = 2) (hD : (M.card : ℤ) = 2 * k)
    (hUp : k + 2 < ∑ a ∈ U, (leftDegree M a : ℤ))
    (hZp : k < ∑ b ∈ Z, (rightDegree M b : ℤ)) :
    (∑ a ∈ U, (leftDegree M a : ℤ)) = k + 3 ∧
    (∑ b ∈ Z, (rightDegree M b : ℤ)) = k + 1 ∧
    (∀ e ∈ M, e.1 ∈ U ∨ e.2 ∈ Z) := by
  have hn := degree_sums_le_card_add_product M U Z
  rw [hU, hZ] at hn
  have hi : (∑ a ∈ U, (leftDegree M a : ℤ)) + (∑ b ∈ Z, (rightDegree M b : ℤ)) ≤ M.card + 4 := by
    exact_mod_cast hn
  have hleft : (∑ a ∈ U, (leftDegree M a : ℤ)) = k + 3 := by omega
  have hright : (∑ b ∈ Z, (rightDegree M b : ℤ)) = k + 1 := by omega
  refine ⟨hleft, hright, degree_sums_equality_cover M U Z ?_⟩
  have heq : (∑ a ∈ U, (leftDegree M a : ℤ)) + (∑ b ∈ Z, (rightDegree M b : ℤ)) =
      (M.card : ℤ) + (U.card : ℤ) * Z.card := by rw [hU, hZ]; norm_num; omega
  exact_mod_cast heq

lemma asymmetric_left_pair_unique (M : Finset (A × B)) (k : ℤ) (U : Finset A) (Z : Finset B)
    (hU : U.card = 2) (hZ : Z.card = 2) (hD : (M.card : ℤ) = 2 * k)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k)
    (hUp : k + 2 < ∑ a ∈ U, (leftDegree M a : ℤ))
    (hZp : k < ∑ b ∈ Z, (rightDegree M b : ℤ)) :
    ∀ P : Finset A, P.card = 2 → k + 2 < ∑ a ∈ P, (leftDegree M a : ℤ) → P = U := by
  have hrig := asymmetric_pair_rigidity M k U Z hU hZ hD hUp hZp
  obtain ⟨u, v, huv, hUeq⟩ := card_eq_two.mp hU
  have hsum := hrig.1
  rw [hUeq, sum_pair huv] at hsum
  have hdu : 3 ≤ leftDegree M u := by have := hA v; omega
  have hdv : 3 ≤ leftDegree M v := by have := hA u; omega
  obtain ⟨b, hub, hbZ⟩ := exists_right_neighbor_outside M u Z (by omega)
  obtain ⟨c, hvc, hcZ⟩ := exists_right_neighbor_outside M v Z (by omega)
  intro P hP hPp
  have hcover := (asymmetric_pair_rigidity M k P Z hP hZ hD hPp hZp).2.2
  have huP : u ∈ P := (hcover (u, b) hub).resolve_right hbZ
  have hvP : v ∈ P := (hcover (v, c) hvc).resolve_right hcZ
  have hsub : U ⊆ P := by rw [hUeq]; simp [insert_subset_iff, huP, hvP]
  exact (eq_of_subset_of_card_le hsub (by omega)).symm

lemma asymmetric_pair_bound_large (M : Finset (A × B)) (k : ℤ) (hk : 4 ≤ k)
    (hD : (M.card : ℤ) = 2 * k) (hA : ∀ a, (leftDegree M a : ℤ) ≤ k)
    (hB : ∀ b, (rightDegree M b : ℤ) ≤ k) :
    pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) (k + 2) +
      pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) k ≤ k := by
  have hpa := pairExcess_le univ (fun a ↦ (leftDegree M a : ℤ)) k (by omega)
    (fun a _ ↦ ⟨Nat.cast_nonneg _, hA a⟩) (by rw [missing_left_sum, hD])
  have hpb := pairExcess_le univ (fun b ↦ (rightDegree M b : ℤ)) k (by omega)
    (fun b _ ↦ ⟨Nat.cast_nonneg _, hB b⟩) (by rw [missing_right_sum, hD])
  have hmono := pairExcess_threshold_antitone univ (fun a ↦ (leftDegree M a : ℤ))
    (show k ≤ k + 2 by omega)
  by_cases hzA : pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) (k + 2) = 0
  · rw [hzA, zero_add]
    exact hpb
  by_cases hzB : pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) k = 0
  · rw [hzB, add_zero]
    exact hmono.trans hpa
  obtain ⟨U, hUm, hUp⟩ := exists_positive_pair_of_ne_zero univ (fun a ↦ (leftDegree M a : ℤ)) (k + 2) hzA
  obtain ⟨Z, hZm, hZp⟩ := exists_positive_pair_of_ne_zero univ (fun b ↦ (rightDegree M b : ℤ)) k hzB
  have hU := (mem_powersetCard.mp hUm).2
  have hZ := (mem_powersetCard.mp hZm).2
  have hrig := asymmetric_pair_rigidity M k U Z hU hZ hD hUp hZp
  have hPA : pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) (k + 2) = 1 := by
    apply pairExcess_eq_one_of_unique univ _ (k + 2) U hUm (by linarith [hrig.1])
    intro P hPm hPp
    exact asymmetric_left_pair_unique M k U Z hU hZ hD hA hUp hZp P
      (mem_powersetCard.mp hPm).2 hPp
  have hlt : (∑ a ∈ U, leftDegree M a) < M.card := by
    have hsum : ((∑ a ∈ U, leftDegree M a : ℕ) : ℤ) = k + 3 := by simpa using hrig.1
    exact_mod_cast (show ((∑ a ∈ U, leftDegree M a : ℕ) : ℤ) < M.card by omega)
  obtain ⟨⟨a, w⟩, haw, haU⟩ := exists_edge_left_outside M U hlt
  have hBstrict : ∀ b, (rightDegree M b : ℤ) ≤ k - 1 := by
    intro b
    have hn := degree_sums_le_card_add_product M U {b}
    simp only [sum_singleton, card_singleton, mul_one, hU] at hn
    have hi : (∑ a ∈ U, (leftDegree M a : ℤ)) + rightDegree M b ≤ M.card + 2 := by exact_mod_cast hn
    have := hrig.1
    omega
  have hstar : ∀ b ∈ (univ : Finset B).erase w, ∀ c ∈ (univ : Finset B).erase w,
      b ≠ c → (rightDegree M b : ℤ) + rightDegree M c ≤ k := by
    intro b hb c hc hbc
    by_contra! hp
    have hPp : k < ∑ z ∈ ({b, c} : Finset B), (rightDegree M z : ℤ) := by rwa [sum_pair hbc]
    have hcover := (asymmetric_pair_rigidity M k U {b, c} hU (card_pair hbc) hD hUp hPp).2.2
    have hw : w ∈ ({b, c} : Finset B) := (hcover (a, w) haw).resolve_left haU
    rcases mem_insert.mp hw with h | h
    · exact (ne_of_mem_erase hb) h.symm
    · exact (ne_of_mem_erase hc) (mem_singleton.mp h).symm
  have hPB := pairExcess_star_le_center univ (fun b ↦ (rightDegree M b : ℤ)) k w (mem_univ _)
    (fun b _ ↦ ⟨Nat.cast_nonneg _, hB b⟩) (by rw [missing_right_sum, hD]) hstar
  rw [hPA]
  have := hBstrict w
  omega

lemma asymmetric_pair_bound_small (M : Finset (A × B)) (k : ℤ) (hk : 0 ≤ k) (hk2 : k ≤ 2)
    (hD : (M.card : ℤ) = 2 * k) (hA : ∀ a, (leftDegree M a : ℤ) ≤ k)
    (hB : ∀ b, (rightDegree M b : ℤ) ≤ k) :
    pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) (k + 2) +
      pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) k ≤ k := by
  have hz : pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) (k + 2) = 0 := by
    apply pairExcess_eq_zero_of_pair_le
    intro a ha b hb hab
    have := hA a
    have := hA b
    omega
  rw [hz, zero_add]
  exact pairExcess_le univ (fun b ↦ (rightDegree M b : ℤ)) k hk
    (fun b _ ↦ ⟨Nat.cast_nonneg _, hB b⟩) (by rw [missing_right_sum, hD])

/-- A coarse alternate-baseline estimate handles the whole maximum-degree-three
exception without classifying its precise bipartite graph. -/
lemma asymmetric_three_coarse (M : Finset (A × B)) (hD : (M.card : ℤ) = 6)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ 3)
    (hpos : pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) 5 ≠ 0) :
    pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) 4 +
      pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) 2 ≤ 9 := by
  obtain ⟨U, hUm, hUp⟩ := exists_positive_pair_of_ne_zero univ (fun a ↦ (leftDegree M a : ℤ)) 5 hpos
  have hU := (mem_powersetCard.mp hUm).2
  have hUsum_le : (∑ a ∈ U, (leftDegree M a : ℤ)) ≤ 6 := by
    calc
      _ ≤ ∑ _a ∈ U, (3 : ℤ) := sum_le_sum fun a _ ↦ hA a
      _ = 6 := by simp [hU]
  have hUsum : (∑ a ∈ U, (leftDegree M a : ℤ)) = 6 := by omega
  have hzero : ∀ a, a ∉ U → leftDegree M a = 0 := by
    intro a ha
    have hs := sum_le_sum_of_subset_of_nonneg (subset_univ (insert a U))
      (fun b _ _ ↦ Nat.cast_nonneg (α := ℤ) (leftDegree M b))
    rw [sum_insert ha, hUsum, missing_left_sum, hD] at hs
    omega
  have hB2 : ∀ b, (rightDegree M b : ℤ) ≤ 2 := by
    intro b
    have hn := degree_sums_le_card_add_product M U {b}
    simp only [sum_singleton, card_singleton, mul_one, hU] at hn
    have hi : (∑ a ∈ U, (leftDegree M a : ℤ)) + rightDegree M b ≤ M.card + 2 := by exact_mod_cast hn
    omega
  have hPA : pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) 4 = 2 := by
    rw [pairExcess_restrict univ U _ 4 (subset_univ _) (by
      intro a ha b hb haU
      rw [hzero a haU, Nat.cast_zero, zero_add]
      exact (hA b).trans (by omega))]
    unfold pairExcess
    rw [← hU, powersetCard_self, sum_singleton, hUsum]
    norm_num
  have hPB := pairExcess_quadratic_bound univ (fun b ↦ (rightDegree M b : ℤ)) 2
    (fun b _ ↦ ⟨Nat.cast_nonneg _, hB2 b⟩)
  rw [missing_right_sum, hD] at hPB
  have hsq : (6 : ℤ) ≤ ∑ b, (rightDegree M b : ℤ) ^ 2 := by
    have hsum : (∑ b, (rightDegree M b : ℤ)) ≤ ∑ b, (rightDegree M b : ℤ) ^ 2 :=
      sum_le_sum fun b _ ↦ Int.le_self_sq _
    rwa [missing_right_sum, hD] at hsum
  rw [hPA]
  omega

end Erdos1010
