import ErdosProblems.Erdos421.CompleteMeanValue

/-! # Quantitative decay of the complete-system exponent defect -/

namespace Erdos421

theorem meanValueDefect_le_exp {k : ℕ} (hk : 0 < k) (r : ℕ) :
    meanValueDefect k r ≤ (meanValueTriangle k : ℝ) * Real.exp (-(r : ℝ) / k) := by
  have hq : 1 - (k : ℝ)⁻¹ ≤ Real.exp (-(k : ℝ)⁻¹) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(k : ℝ)⁻¹)
  have hp := pow_le_pow_left₀ (meanValue_contraction_mem_Icc hk).1 hq r
  rw [← Real.exp_nat_mul] at hp
  have he : (r : ℝ) * -(k : ℝ)⁻¹ = -(r : ℝ) / k := by ring
  rw [he] at hp
  exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)

theorem meanValueDefect_le_one_of_log {k r : ℕ} (hk : 0 < k)
    (hr : 2 * (k : ℝ) * Real.log k ≤ r) : meanValueDefect k r ≤ 1 := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have harg : -(r : ℝ) / k ≤ -(2 * Real.log k) := by
    apply (div_le_iff₀ hkR).mpr
    nlinarith
  have hexp : Real.exp (-(2 * Real.log k)) = ((k : ℝ) ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    simpa only [Nat.cast_ofNat, Real.exp_log hkR] using Real.exp_nat_mul (Real.log k) 2
  have ht : (meanValueTriangle k : ℝ) ≤ (k : ℝ) ^ 2 := by
    exact_mod_cast meanValueTriangle_le_square k
  calc
    _ ≤ (meanValueTriangle k : ℝ) * Real.exp (-(r : ℝ) / k) := meanValueDefect_le_exp hk r
    _ ≤ (meanValueTriangle k : ℝ) * Real.exp (-(2 * Real.log k)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (Nat.cast_nonneg _)
    _ = (meanValueTriangle k : ℝ) * ((k : ℝ) ^ 2)⁻¹ := by rw [hexp]
    _ ≤ (k : ℝ) ^ 2 * ((k : ℝ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right ht (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

noncomputable def meanValueIterationIndex (k : ℕ) : ℕ :=
  ⌈2 * (k : ℝ) * Real.log k⌉₊

theorem meanValueIterationIndex_lower (k : ℕ) :
    2 * (k : ℝ) * Real.log k ≤ meanValueIterationIndex k := Nat.le_ceil _

theorem meanValueIterationIndex_upper {k : ℕ} (hk : 0 < k) :
    (meanValueIterationIndex k : ℝ) < 2 * (k : ℝ) * Real.log k + 1 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact Nat.ceil_lt_add_one (mul_nonneg (by positivity) (Real.log_nonneg hkR))

theorem meanValueDefect_iterationIndex_le_one {k : ℕ} (hk : 0 < k) :
    meanValueDefect k (meanValueIterationIndex k) ≤ 1 :=
  meanValueDefect_le_one_of_log hk (meanValueIterationIndex_lower k)

theorem vinogradovCount_complete_meanValue_small_defect {k : ℕ} (hk : 2 ≤ k)
    (r N : ℕ) (hr : 2 * (k : ℝ) * Real.log k ≤ r) (hN : 0 < N) :
    (vinogradovCount ((r + 1) * k) k N : ℝ) ≤
      (2 : ℝ) ^ (32 * (k + 1) ^ 5 * (r + 1) ^ 3) *
        (N : ℝ) ^ (2 * (((r + 1) * k : ℕ) : ℝ) -
          ((k + meanValueTriangle k : ℕ) : ℝ) + 1) := by
  have he : meanValueExponent k r ≤
      2 * ((r + 1) * k : ℕ) - (k + meanValueTriangle k : ℕ) + (1 : ℝ) := by
    dsimp only [meanValueExponent]
    linarith [meanValueDefect_le_one_of_log (by omega : 0 < k) hr]
  exact (vinogradovCount_complete_meanValue hk r N).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) he) (by positivity))

end Erdos421
