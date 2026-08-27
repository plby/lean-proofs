/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ProperPatternExtensions
import ErdosProblems.Erdos207.KSSSPatternLowerBound

/-! # Exact multiplicative typicality from the proper relative statistic -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem withinMultiplicativeError_iff_abs
    (xi actual target : ℝ≥0) :
    WithinMultiplicativeError xi actual target ↔
      |(actual : ℝ) - target| ≤ (xi : ℝ) * target := by
  rw [WithinMultiplicativeError, tsub_mul, one_mul, tsub_le_iff_right]
  simp only [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one]
  rw [abs_le]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith only [hl, hu]

theorem relative_error_mul_target
    (Y f z : ℝ) (hf : 0 < f) (hband : |Y / f - 1| ≤ z) :
    |Y - f| ≤ z * f := by
  have heq : Y / f - 1 = (Y - f) / f := by field_simp
  rw [heq, abs_div, abs_of_pos hf] at hband
  exact (div_le_iff₀ hf).mp hband

theorem full_pattern_error_of_proper_relative_band
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V)
    (f z delta : ℝ) (hf : 0 < f)
    (hband : |((properPatternExtensions A Q U).card : ℝ) / f - 1| ≤ z)
    (hendpoints : ((graphSupportFinset Q).card : ℝ) ≤ delta * f) :
    |((iterationExtensionVertices A Q U).card : ℝ) - f| ≤ (z + delta) * f := by
  obtain ⟨hlo, hhi⟩ := properPatternExtensions_card_comparison A Q U
  have hloR : ((properPatternExtensions A Q U).card : ℝ) ≤ (iterationExtensionVertices A Q U).card :=
    by exact_mod_cast hlo
  have hhiR : ((iterationExtensionVertices A Q U).card : ℝ) ≤
      (properPatternExtensions A Q U).card + (graphSupportFinset Q).card := by exact_mod_cast hhi
  have hraw := abs_le.mp (relative_error_mul_target _ f z hf hband)
  have hendpoint0 : 0 ≤ (delta * f) := (Nat.cast_nonneg _).trans hendpoints
  rw [abs_le]
  constructor <;> nlinarith only [hloR, hhiR, hraw.1, hraw.2, hendpoints, hendpoint0]

theorem pattern_endpoint_power_budget
    (M f t : ℝ) (h d : ℕ) (ht : 1 ≤ t) (hh : (h : ℝ) ≤ t)
    (hsize : t ^ (d + 2) ≤ M) (hf : M / t ^ d ≤ f) :
    (h : ℝ) ≤ (1 / t) * f := by
  have htpos : 0 < t := by linarith
  have hmul : (h : ℝ) * t ^ (d + 1) ≤ M := by
    calc
      _ ≤ t * t ^ (d + 1) := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = t ^ (d + 2) := by rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]; ring
      _ ≤ M := hsize
  have hdiv := (le_div_iff₀ (pow_pos htpos (d + 1))).mpr hmul
  calc
    (h : ℝ) ≤ M / t ^ (d + 1) := hdiv
    _ = (1 / t) * (M / t ^ d) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

theorem ksssPatternTrajectory_eq_multiplicative_target
    (orders : Finset ℕ) (a : ℕ → ℝ) (E M time : ℝ) (h m : ℕ) :
    ksssPatternTrajectory orders a E M h m time =
      ksssEdgeDensity E time ^ h * Real.exp (-ksssPoissonExponent orders a time) ^ m * M := by
  rw [ksssPatternTrajectory, ← Real.exp_nat_mul]
  have heq : -(m : ℝ) * ksssPoissonExponent orders a time =
      (m : ℝ) * (-ksssPoissonExponent orders a time) := by ring
  rw [heq]
  ring

end

end Erdos207
