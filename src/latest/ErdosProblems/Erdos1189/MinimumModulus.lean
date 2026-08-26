/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The smallest possible largest modulus, with the full range k >= 5.
Informal source: Section 6 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.QuantitativeConstruction
import ErdosProblems.Erdos1189.MaximumModulus

namespace Erdos1189

open Finset Filter

theorem minimumLargestModulus : MinimumLargestModulusClaim := by
  refine ⟨fun D hD => hD.card_add_one_le_largest, ?_⟩
  obtain ⟨K, hK, hevent⟩ := eventually_bounded_construction
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hevent
  let M : ℝ := 3 * 2 ^ k₀
  let H : ℝ := M / (Real.log 5) ^ 2
  let C : ℝ := max K H
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hM : 0 < M := by dsimp [M]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 < C := hK.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hlogk : Real.log 5 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  have hlogk0 : 0 ≤ Real.log k := hlog5.le.trans hlogk
  by_cases hkbig : k₀ ≤ k
  · obtain ⟨P, S, _, _, _, hS, hcard, hbound, _⟩ := hk₀ k hkbig
    refine ⟨S, ⟨hS, hcard⟩, ?_⟩
    intro d hd
    exact (hbound d hd).trans (by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right (le_max_left K H) (by positivity))
  · obtain ⟨S, hS, hcard, hmax⟩ := exists_irreducible_extremal hk
    refine ⟨S, ⟨hS, hcard⟩, ?_⟩
    intro d hd
    have hdmax : d ≤ 3 * 2 ^ (k - 3) := by
      rw [← hmax]
      exact le_sup (f := id) hd
    have hdpow : d ≤ 3 * 2 ^ k₀ := hdmax.trans
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide) (by omega)))
    have hdM : (d : ℝ) ≤ M := by
      dsimp [M]
      exact_mod_cast hdpow
    have hsquare : (Real.log 5) ^ 2 ≤ (Real.log k) ^ 2 := by nlinarith
    have hscale : (Real.log 5) ^ 2 ≤ (k : ℝ) * (Real.log k) ^ 2 :=
      hsquare.trans (le_mul_of_one_le_left (sq_nonneg _) hk1)
    calc
      (d : ℝ) ≤ M := hdM
      _ = H * (Real.log 5) ^ 2 := by dsimp [H]; field_simp
      _ ≤ H * ((k : ℝ) * (Real.log k) ^ 2) := mul_le_mul_of_nonneg_left hscale hH
      _ ≤ C * ((k : ℝ) * (Real.log k) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_max_right K H) (by positivity)
      _ = C * k * (Real.log k) ^ 2 := by ring

end Erdos1189
