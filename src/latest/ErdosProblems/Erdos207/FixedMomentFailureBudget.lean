/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGraphAllLocalDegrees
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Fixed moments retain, and control, the additive distribution error -/

namespace Erdos207

open Finset Filter
open scoped NNReal Topology

noncomputable section

theorem fixedMoment_power_ratio_le
    (t : ℝ≥0) (R s : ℕ) (ht : 1 ≤ t) (hs : 3 * R + 1 ≤ s) :
    t ^ (3 * R) / t ^ s ≤ 1 / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hpow : t ^ (3 * R + 1) ≤ t ^ s := pow_le_pow_right₀ ht hs
  calc
    _ ≤ t ^ (3 * R) / t ^ (3 * R + 1) :=
      div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) hpow
    _ = _ := by rw [pow_succ]; field_simp

theorem fixedMoment_failure_budget
    (N t R s D d : ℕ) (A M kappa K b B Q : ℝ≥0)
    (ht : 1 ≤ t) (hN : N ≤ t ^ R) (hs : 3 * R + 1 ≤ s)
    (hkappa : 0 < kappa) (hK : (t : ℝ≥0) * kappa ≤ K) (hK1 : 1 ≤ K)
    (hb : b ≤ B * (t : ℝ≥0) ^ D * (1 / 2 : ℝ≥0) ^ t)
    (W : ℝ≥0) (hW : W ≤ Q * (t : ℝ≥0) ^ d) :
    (N : ℝ≥0) ^ 3 * (A * (M * kappa / K) ^ s + A * b * (W / K) ^ s) ≤
      A * M ^ s / t +
        A * B * Q ^ s * (t : ℝ≥0) ^ (3 * R + D + d * s) * (1 / 2 : ℝ≥0) ^ t := by
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le ht1
  have hN3 : (N : ℝ≥0) ^ 3 ≤ (t : ℝ≥0) ^ (3 * R) := by
    have hNR : (N : ℝ≥0) ≤ (t : ℝ≥0) ^ R := by exact_mod_cast hN
    simpa only [← pow_mul, Nat.mul_comm R 3] using pow_le_pow_left₀ zero_le hNR 3
  have hratio : M * kappa / K ≤ M / t := by
    calc
      _ ≤ M * kappa / ((t : ℝ≥0) * kappa) :=
        div_le_div_of_nonneg_left zero_le (mul_pos ht0 hkappa) hK
      _ = _ := by field_simp
  have hWratio : W / K ≤ Q * (t : ℝ≥0) ^ d :=
    (div_le_self zero_le hK1).trans hW
  have hfirst : (N : ℝ≥0) ^ 3 * (A * (M * kappa / K) ^ s) ≤ A * M ^ s / t := by
    calc
      _ ≤ (t : ℝ≥0) ^ (3 * R) * (A * (M / t) ^ s) := by gcongr
      _ = (A * M ^ s) * ((t : ℝ≥0) ^ (3 * R) / (t : ℝ≥0) ^ s) := by
        rw [div_pow]; ring
      _ ≤ (A * M ^ s) * (1 / (t : ℝ≥0)) :=
        mul_le_mul_of_nonneg_left (fixedMoment_power_ratio_le t R s ht1 hs) zero_le
      _ = _ := by ring
  have hsecond : (N : ℝ≥0) ^ 3 * (A * b * (W / K) ^ s) ≤
      A * B * Q ^ s * (t : ℝ≥0) ^ (3 * R + D + d * s) * (1 / 2 : ℝ≥0) ^ t := by
    calc
      _ ≤ (t : ℝ≥0) ^ (3 * R) *
          (A * (B * (t : ℝ≥0) ^ D * (1 / 2 : ℝ≥0) ^ t) *
            (Q * (t : ℝ≥0) ^ d) ^ s) := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add, pow_add]; ring
  rw [mul_add]
  exact add_le_add hfirst hsecond

theorem eventually_fixedMoment_budget_lt
    (a b epsilon : ℝ≥0) (d : ℕ) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      a / t + b * (t : ℝ≥0) ^ d * (1 / 2 : ℝ≥0) ^ t < epsilon := by
  have hfirst := tendsto_const_div_atTop_nhds_zero_nat (a : ℝ)
  have hsecond := (tendsto_pow_const_mul_const_pow_of_lt_one d
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (b : ℝ)
  have hlim : Tendsto (fun t : ℕ ↦ (a : ℝ) / t +
      (b : ℝ) * (t : ℝ) ^ d * (1 / 2 : ℝ) ^ t) atTop (𝓝 0) := by
    simpa only [zero_add, mul_zero, mul_assoc] using hfirst.add hsecond
  have hepsR : (0 : ℝ) < epsilon := by exact_mod_cast hepsilon
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hepsR))
  refine ⟨max T 1, le_max_right _ _, fun t ht ↦ ?_⟩
  exact_mod_cast hT t ((le_max_left T 1).trans ht)

theorem eventually_fixedMoment_failure_lt
    (R s D d : ℕ) (A M B Q epsilon : ℝ≥0)
    (hs : 3 * R + 1 ≤ s) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ (N : ℕ) (kappa K b W : ℝ≥0),
      N ≤ t ^ R → 0 < kappa → (t : ℝ≥0) * kappa ≤ K → 1 ≤ K →
      b ≤ B * (t : ℝ≥0) ^ D * (1 / 2 : ℝ≥0) ^ t →
      W ≤ Q * (t : ℝ≥0) ^ d →
      (N : ℝ≥0) ^ 3 * (A * (M * kappa / K) ^ s + A * b * (W / K) ^ s) < epsilon := by
  obtain ⟨T, hT1, hT⟩ := eventually_fixedMoment_budget_lt (A * M ^ s)
    (A * B * Q ^ s) epsilon (3 * R + D + d * s) hepsilon
  refine ⟨T, hT1, fun t ht N kappa K b W hN hkappa hK hK1 hb hW ↦ ?_⟩
  exact (fixedMoment_failure_budget N t R s D d A M kappa K b B Q
    (hT1.trans ht) hN hs hkappa hK hK1 hb W hW).trans_lt (hT t ht)

end

end Erdos207
