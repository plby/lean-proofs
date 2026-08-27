/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerConcentrationOptimization

/-! # Exponential concentration at the localized pattern-jump scale -/

namespace Erdos207

noncomputable section

theorem relative_pattern_concentration_power_budget
    (N M J t steps jump variance margin : ℝ) (s b d : ℕ)
    (hN : 0 < N) (hJ : 0 < J) (ht : 1 ≤ t)
    (hsize : J * t ^ (2 * s + d + 2 * b + 1) ≤ M)
    (hsteps : steps ≤ N ^ 2) (hv0 : 0 ≤ variance)
    (hjump : jump ≤ t ^ (d + 1) * J / M)
    (hv : variance ≤ t ^ (d + 2 * b + 1) * J / (M * N ^ 2))
    (hmargin : 8 * t ^ 2 / t ^ s ≤ margin) :
    0 < t ^ s ∧ t ^ s * jump ≤ 1 ∧
      -(t ^ s) * margin + (t ^ s) ^ 2 * steps * variance ≤ -t := by
  have htpos : 0 < t := by linarith
  have hMpos : 0 < M := (mul_pos hJ (pow_pos htpos _)).trans_le hsize
  have htheta : 0 < t ^ s := pow_pos htpos _
  have hj : t ^ s * jump ≤ 1 := by
    calc
      _ ≤ t ^ s * (t ^ (d + 1) * J / M) := mul_le_mul_of_nonneg_left hjump htheta.le
      _ = J * t ^ (s + d + 1) / M := by simp only [pow_add]; ring
      _ ≤ J * t ^ (2 * s + d + 2 * b + 1) / M :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) hJ.le) hMpos.le
      _ ≤ 1 := (div_le_one hMpos).mpr hsize
  have hvar : (t ^ s) ^ 2 * steps * variance ≤ 1 := by
    calc
      _ ≤ (t ^ s) ^ 2 * N ^ 2 * (t ^ (d + 2 * b + 1) * J / (M * N ^ 2)) := by gcongr
      _ = J * t ^ (2 * s + d + 2 * b + 1) / M := by
        simp only [pow_add, pow_mul]
        field_simp
        ring
      _ ≤ 1 := (div_le_one hMpos).mpr hsize
  have hmar : 8 * t ^ 2 ≤ t ^ s * margin := by
    calc
      _ = t ^ s * (8 * t ^ 2 / t ^ s) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmargin htheta.le
  exact ⟨htheta, hj, by nlinarith only [hvar, hmar, ht]⟩

theorem relative_pattern_concentration_exponential_le_half
    (N M J jump variance margin : ℝ) (steps t s b d : ℕ)
    (hN : 0 < N) (hJ : 0 < J) (ht : 1 ≤ t)
    (hsize : J * (t : ℝ) ^ (2 * s + d + 2 * b + 1) ≤ M)
    (hsteps : (steps : ℝ) ≤ N ^ 2) (hv0 : 0 ≤ variance)
    (hjump : jump ≤ (t : ℝ) ^ (d + 1) * J / M)
    (hv : variance ≤ (t : ℝ) ^ (d + 2 * b + 1) * J / (M * N ^ 2))
    (hmargin : 8 * (t : ℝ) ^ 2 / (t : ℝ) ^ s ≤ margin) :
    Real.exp (-((t : ℝ) ^ s) * margin + ((t : ℝ) ^ s) ^ 2 * steps * variance) ≤
      (1 / 2 : ℝ) ^ t := by
  have h := relative_pattern_concentration_power_budget N M J t steps jump variance margin s b d
    hN hJ (by exact_mod_cast ht) hsize hsteps hv0 hjump hv hmargin
  exact (Real.exp_le_exp.mpr h.2.2).trans (exp_neg_nat_le_half_pow t)

end

end Erdos207
