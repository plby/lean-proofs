/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerConcentrationOptimization

/-! # Exponential optimization at the size of a vortex vertex set -/

namespace Erdos207

noncomputable section

def neighborConcentrationTheta (M t : ℝ) (s : ℕ) : ℝ := t ^ s / M

theorem neighbor_concentration_power_budget
    (N M t margin steps variance : ℝ) (s b : ℕ)
    (hN : 0 < N) (ht : 4 ≤ t) (hM : t ^ (2 * s + 2 * b + 3) ≤ M)
    (hsteps : steps ≤ N ^ 2) (hvariance0 : 0 ≤ variance)
    (hvariance : variance ≤ 64 * M / N ^ 2 * t ^ (2 * b))
    (hmargin : 8 * M * t / t ^ s ≤ margin) :
    0 < neighborConcentrationTheta M t s ∧ neighborConcentrationTheta M t s * 3 ≤ 1 ∧
      -neighborConcentrationTheta M t s * margin +
        neighborConcentrationTheta M t s ^ 2 * steps * variance ≤ -t := by
  have htpos : 0 < t := by linarith
  have hMpos : 0 < M := (pow_pos htpos _).trans_le hM
  have htheta : 0 < neighborConcentrationTheta M t s := by unfold neighborConcentrationTheta; positivity
  have hjump : neighborConcentrationTheta M t s * 3 ≤ 1 := by
    have hpower : 3 * t ^ s ≤ M :=
      (real_coeff_mul_pow_le_pow (by linarith) (by linarith : (3 : ℝ) ≤ t) (by omega)).trans hM
    unfold neighborConcentrationTheta
    calc
      _ = 3 * t ^ s / M := by ring
      _ ≤ 1 := (div_le_one hMpos).mpr hpower
  have hvar : neighborConcentrationTheta M t s ^ 2 * steps * variance ≤ 1 := by
    calc
      _ ≤ neighborConcentrationTheta M t s ^ 2 * N ^ 2 * (64 * M / N ^ 2 * t ^ (2 * b)) := by gcongr
      _ = 64 * t ^ (2 * s + 2 * b) / M := by
        unfold neighborConcentrationTheta
        rw [pow_add, pow_mul]
        field_simp
        ring
      _ ≤ 64 * t ^ (2 * s + 2 * b) / t ^ (2 * s + 2 * b + 3) :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos htpos _) hM
      _ = 64 / t ^ 3 := by simp only [pow_add]; field_simp
      _ ≤ 1 := by
        apply (div_le_one (pow_pos htpos 3)).mpr
        have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) ht 3
        norm_num at hpow
        exact hpow
  have hmar : 8 * t ≤ neighborConcentrationTheta M t s * margin := by
    calc
      _ = neighborConcentrationTheta M t s * (8 * M * t / t ^ s) := by
        unfold neighborConcentrationTheta
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmargin htheta.le
  exact ⟨htheta, hjump, by linarith only [hvar, hmar, ht]⟩

theorem neighbor_concentration_exponential_le_half
    (N M margin variance : ℝ) (steps t s b : ℕ)
    (hN : 0 < N) (ht : 4 ≤ t) (hM : (t : ℝ) ^ (2 * s + 2 * b + 3) ≤ M)
    (hsteps : (steps : ℝ) ≤ N ^ 2) (hvariance0 : 0 ≤ variance)
    (hvariance : variance ≤ 64 * M / N ^ 2 * (t : ℝ) ^ (2 * b))
    (hmargin : 8 * M * t / (t : ℝ) ^ s ≤ margin) :
    Real.exp (-neighborConcentrationTheta M t s * margin +
      neighborConcentrationTheta M t s ^ 2 * steps * variance) ≤ (1 / 2 : ℝ) ^ t := by
  have hbudget := neighbor_concentration_power_budget N M t margin steps variance s b hN
    (by exact_mod_cast ht) hM hsteps hvariance0 hvariance hmargin
  exact (Real.exp_le_exp.mpr hbudget.2.2).trans (exp_neg_nat_le_half_pow t)

end

end Erdos207
