import ErdosProblems.Erdos1010.SparseCharge

/-! # Coupled pair estimates for a missing-edge graph -/

open Finset

namespace Erdos1010

open Bipartite

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma missing_right_pair_sum_le (M : Finset (A × B)) (u : A) (k h : ℤ)
    (hu : (leftDegree M u : ℤ) = k) (hD : (M.card : ℤ) = k + h)
    (b c : B) (hbc : b ≠ c) : (rightDegree M b : ℤ) + rightDegree M c ≤ h + 2 := by
  have hres : ((eraseLeft M u).card : ℤ) = h := by
    have hcount : (leftDegree M u : ℤ) + (eraseLeft M u).card = M.card := by
      exact_mod_cast leftDegree_add_card_eraseLeft M u
    omega
  have hp := pair_weight_le_total univ (fun b ↦ (rightDegree (eraseLeft M u) b : ℤ))
    (fun _ _ ↦ Nat.cast_nonneg _) (mem_univ b) (mem_univ c) hbc
  rw [missing_right_sum, hres] at hp
  have hb := rightDegree_eraseLeft M u b
  have hc := rightDegree_eraseLeft M u c
  split_ifs at hb hc <;> omega

lemma missing_right_pairExcess_zero (M : Finset (A × B)) (u : A) (k h : ℤ)
    (hu : (leftDegree M u : ℤ) = k) (hD : (M.card : ℤ) = k + h) :
    pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) (h + 2) = 0 := by
  apply pairExcess_eq_zero_of_pair_le
  intro b hb c hc hbc
  exact missing_right_pair_sum_le M u k h hu hD b c hbc

lemma missing_right_pairExcess_two_supports (M : Finset (A × B)) (u a : A) (k h : ℤ)
    (hu : (leftDegree M u : ℤ) = k) (hD : (M.card : ℤ) = k + h)
    (ha : a ≠ u) (hdeg : 2 ≤ leftDegree M a) :
    pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) (h + 1) ≤ 1 := by
  let e : B → ℤ := fun b ↦ if (u, b) ∈ M then 1 else 0
  let g : B → ℤ := fun b ↦ rightDegree (eraseLeft M u) b
  have he : ∀ b ∈ (univ : Finset B), 0 ≤ e b ∧ e b ≤ 1 := by
    intro b hb
    dsimp [e]
    split_ifs <;> omega
  have hgs : (∑ b, g b) = h := by
    dsimp [g]
    rw [missing_right_sum]
    have hd : (leftDegree M u : ℤ) + (eraseLeft M u).card = M.card := by
      exact_mod_cast leftDegree_add_card_eraseLeft M u
    omega
  have hz : (fun b ↦ e b + g b) = (fun b ↦ (rightDegree M b : ℤ)) := by
    funext b
    dsimp [e, g]
    have hd := rightDegree_eraseLeft M u b
    exact_mod_cast hd.symm
  have hares : 2 ≤ leftDegree (eraseLeft M u) a := by rwa [leftDegree_eraseLeft_of_ne M ha]
  obtain ⟨b, c, hbc, hb, hc⟩ := exists_two_right_neighbors (eraseLeft M u) a hares
  have hgb : 0 < g b := by dsimp [g]; exact_mod_cast rightDegree_pos_of_mem _ hb
  have hgc : 0 < g c := by dsimp [g]; exact_mod_cast rightDegree_pos_of_mem _ hc
  have hp := pairExcess_unit_residual_two_supports univ e g h he (fun _ _ ↦ Nat.cast_nonneg _)
    hgs b c (mem_univ _) (mem_univ _) hbc hgb hgc
  rwa [hz] at hp

lemma missing_dominant_edge_pair_bound (M : Finset (A × B)) (u : A) (k : ℤ)
    (hk : 3 ≤ k) (hu : (leftDegree M u : ℤ) = k) (hD : (M.card : ℤ) = 2 * k - 2) :
    pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) (k + 1) +
      pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) (k - 1) ≤ k - 1 := by
  have hDeq : (M.card : ℤ) = k + (k - 2) := by omega
  by_cases hsmall : ∀ a, a ≠ u → (leftDegree M a : ℤ) ≤ 1
  · have hz : pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) (k + 1) = 0 := by
      apply pairExcess_eq_zero_of_pair_le
      intro a ha b hb hab
      by_cases hau : a = u
      · have hbu : b ≠ u := by intro h; exact hab (hau.trans h.symm)
        have := hsmall b hbu
        rw [hau, hu]
        omega
      · by_cases hbu : b = u
        · have := hsmall a hau
          rw [hbu, hu]
          omega
        · have := hsmall a hau
          have := hsmall b hbu
          omega
    have hp := missing_right_pairExcess_residual M u k (k - 2) (by omega) (by omega) hu hDeq
    have heq : k - 2 + 1 = k - 1 := by ring
    rw [heq] at hp
    rwa [hz, zero_add]
  · push Not at hsmall
    obtain ⟨a, ha, hbig⟩ := hsmall
    have hsa := missing_left_sum_erase M u k (k - 2) hu hDeq
    have hpa := pairExcess_above_hub_le univ (fun a ↦ (leftDegree M a : ℤ)) k (k - 2)
      u (mem_univ _) hu (fun _ _ ↦ Nat.cast_nonneg _) hsa (by omega) (by omega)
    have hpb := missing_right_pairExcess_two_supports M u a k (k - 2) hu hDeq ha (by omega)
    have heq : k - 2 + 1 = k - 1 := by ring
    rw [heq] at hpb
    omega

end Erdos1010
