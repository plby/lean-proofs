import ErdosProblems.Erdos19.SmallVolumeColoring
import ErdosProblems.Erdos19.BoundedRankLinear

/-! # Small-volume coloring with minimum edge size three

Split at a fixed rank. The bounded part uses the proved approximation
theorem; the unbounded part uses the elementary small-volume theorem.
-/

namespace Erdos19.SetHypergraph

theorem eventually_small_pair_volume_min_three (h : ℕ) (hh : 1 ≤ h) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 3 ≤ e.1.ncard) →
      (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
        (∑ e : H, e.1.ncard * (e.1.ncard - 1)) < n ^ 2 →
      ∃ q : ℕ, 2 * h * q ≤ (h + 6) * n ∧ H.EdgeColorable q := by
  classical
  have hhpos : 0 < h := by omega
  have hhR : (0 : ℝ) < h := by exact_mod_cast hhpos
  obtain ⟨N₀, hN₀⟩ := eventually_bounded_rank_approximate (4 * h) 3
    (by omega) (by norm_num) (2 / (h : ℝ)) (by positivity)
  refine ⟨max N₀ (5 * h), ?_⟩
  intro n hn H hlinear hmin hvolume
  let A : SetHypergraph (Fin n) := {e | e ∈ H ∧ e.ncard ≤ 4 * h}
  let B : SetHypergraph (Fin n) := {e | e ∈ H ∧ 4 * h < e.ncard}
  have hAH : A ⊆ H := fun _ he ↦ he.1
  have hBH : B ⊆ H := fun _ he ↦ he.1
  have hAlinear : A.IsLinear := hlinear.mono hAH
  have hBlinear : B.IsLinear := hlinear.mono hBH
  obtain ⟨p, _, hp, hpc⟩ := hN₀ n ((le_max_left _ _).trans hn) A hAlinear
    (fun e ↦ hmin ⟨e.1, e.2.1⟩) (fun e ↦ e.2.2)
  have hpNat : 2 * h * p ≤ (h + 2) * n := by
    have hdNat : 2 * ((n - 1) / 2) ≤ n :=
      (Nat.mul_div_le (n - 1) 2).trans (Nat.sub_le _ _)
    have hd : (2 : ℝ) * (((n - 1) / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hdNat
    have hpR : (2 : ℝ) * h * p ≤ (h + 2) * n := by
      calc
        (2 : ℝ) * h * p ≤ (2 : ℝ) * h *
            ((1 + 2 / (h : ℝ)) * (((n - 1) / 2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = (h + 2) * ((2 : ℝ) * (((n - 1) / 2 : ℕ) : ℝ)) := by
          field_simp
        _ ≤ (h + 2) * n := mul_le_mul_of_nonneg_left hd (by positivity)
    exact_mod_cast hpR
  have hBvolume : (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
      (∑ e : B, e.1.ncard * (e.1.ncard - 1)) < (Fintype.card (Fin n)) ^ 2 := by
    simpa only [Fintype.card_fin] using
      (Nat.mul_le_mul_left _ (sum_pair_weight_mono hBH)).trans_lt hvolume
  have hBc : B.EdgeColorable (2 * n / h) := by
    simpa only [Fintype.card_fin] using B.edgeColorable_of_small_pair_volume_le_two_div
      hBlinear h hh (by simpa only [Fintype.card_fin] using (le_max_right _ _).trans hn)
      (fun e ↦ by have := e.2.2; omega) hBvolume
  have hunion : A ∪ B = H := by
    ext e
    change ((e ∈ H ∧ e.ncard ≤ 4 * h) ∨ (e ∈ H ∧ 4 * h < e.ncard)) ↔ e ∈ H
    constructor
    · rintro (he | he) <;> exact he.1
    · intro he
      by_cases hsize : e.ncard ≤ 4 * h
      · exact Or.inl ⟨he, hsize⟩
      · exact Or.inr ⟨he, lt_of_not_ge hsize⟩
  refine ⟨p + 2 * n / h, ?_, ?_⟩
  · have hq := Nat.div_mul_le_self (2 * n) h
    nlinarith only [hpNat, hq]
  · rw [← hunion]
    exact edgeColorable_union A B hpc hBc

#print axioms eventually_small_pair_volume_min_three

end Erdos19.SetHypergraph
