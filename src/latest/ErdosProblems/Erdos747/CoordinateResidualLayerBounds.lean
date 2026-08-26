import ErdosProblems.Erdos747.CoordinateNumericalBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

lemma coordinate_residual_layer_mean_lower (n M j : ℕ)
    (hn : 200 ≤ n) (hmean : 1 ≤ (M : ℝ) / n)
    (hj : M - 3 * coordinateDegreeCeil n M ≤ j) :
    0 < M - 3 * coordinateDegreeCeil n M ∧
      ((M : ℝ) / n) / 2 ≤ (j : ℝ) / ((n - 1 : ℕ) : ℝ) := by
  let mu : ℝ := (M : ℝ) / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn200 : (200 : ℝ) ≤ n := by exact_mod_cast hn
  have hmu : 0 < mu := lt_of_lt_of_le zero_lt_one hmean
  have hmuId : mu * n = M := div_mul_cancel₀ _ hnR.ne'
  have hMpos : (0 : ℝ) < M := by rw [← hmuId]; positivity
  have hD := coordinateDegreeCeil_le n M hmean
  have hscaled := mul_le_mul_of_nonneg_left hn200 hmu.le
  have h3D : (3 : ℝ) * coordinateDegreeCeil n M ≤ (M : ℝ) / 2 := by
    nlinarith only [hD, hscaled, hmuId]
  have h3DM : 3 * coordinateDegreeCeil n M ≤ M := by
    have hR : (3 : ℝ) * coordinateDegreeCeil n M ≤ M := by linarith only [h3D, hMpos]
    exact_mod_cast hR
  have hleft : (M : ℝ) / 2 ≤ ((M - 3 * coordinateDegreeCeil n M : ℕ) : ℝ) := by
    rw [Nat.cast_sub h3DM, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [h3D]
  have hleftpos : (0 : ℝ) < ((M - 3 * coordinateDegreeCeil n M : ℕ) : ℝ) :=
    (half_pos hMpos).trans_le hleft
  have hjR : ((M - 3 * coordinateDegreeCeil n M : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
  have hk : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  refine ⟨by exact_mod_cast hleftpos, ?_⟩
  apply (le_div_iff₀ hk).mpr
  calc
    _ ≤ (mu / 2) * n := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le n 1) (half_pos hmu).le
    _ = (M : ℝ) / 2 := by nlinarith only [hmuId]
    _ ≤ _ := hleft.trans hjR

lemma coordinate_residual_layer_relative_cap (n M j cap : ℕ) (g : ℝ)
    (hn : 200 ≤ n) (hmean : 1 ≤ (M : ℝ) / n)
    (hj : M - 3 * coordinateDegreeCeil n M ≤ j)
    (hcap : (cap : ℝ) / ((M : ℝ) / n) ≤ g) :
    (cap : ℝ) / ((j : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ 2 * g := by
  have hmu : 0 < (M : ℝ) / n := lt_of_lt_of_le zero_lt_one hmean
  have hlower := (coordinate_residual_layer_mean_lower n M j hn hmean hj).2
  calc
    _ ≤ (cap : ℝ) / (((M : ℝ) / n) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (half_pos hmu) hlower
    _ = 2 * ((cap : ℝ) / ((M : ℝ) / n)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcap (by norm_num)

lemma coordinate_residual_layer_halfLogMean (n M j : ℕ)
    (hn : 200 ≤ n) (hmean : 1 ≤ (M : ℝ) / n)
    (hlogmean : Real.log ((3 * n : ℕ) : ℝ) ≤ (M : ℝ) / n)
    (hj : M - 3 * coordinateDegreeCeil n M ≤ j) :
    halfLogMean (n - 1) ≤ (j : ℝ) / ((n - 1 : ℕ) : ℝ) := by
  have hlog : Real.log ((3 * (n - 1) : ℕ) : ℝ) ≤ Real.log ((3 * n : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < 3 * (n - 1) by omega)
    · exact_mod_cast (show 3 * (n - 1) ≤ 3 * n by omega)
  exact (div_le_div_of_nonneg_right (hlog.trans hlogmean) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (coordinate_residual_layer_mean_lower n M j hn hmean hj).2

lemma coordinate_degree_lower_budget (n M cap : ℕ) (a g : ℝ)
    (ha : 0 ≤ a) (hcap : (cap : ℝ) / ((M : ℝ) / n) ≤ g)
    (hmean : 0 < (M : ℝ) / n) (hg : g ≤ a / 6) :
    ((coordinateDegreeFloor n M a + 3 * cap : ℕ) : ℝ) ≤ a * ((M : ℝ) / n) := by
  have hd : (coordinateDegreeFloor n M a : ℝ) ≤ a * ((M : ℝ) / n) / 2 := Nat.floor_le (by positivity)
  have hc := (div_le_iff₀ hmean).mp hcap
  have hgscaled := mul_le_mul_of_nonneg_right hg hmean.le
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hd, hc, hgscaled]

lemma coordinate_transfer_cutoff_budget (n M j : ℕ) (a L : ℝ)
    (hn : 2 ≤ n) (ha : 0 < a) (hL : 0 ≤ L) (hj : j ≤ M)
    (hlarge : 8 ≤ a * ((M : ℝ) / n)) :
    (a * L / 32) * j ≤ L * ((coordinateDegreeFloor n M a - coordinateTailFloor n M a : ℕ) : ℝ) *
      ((n - 1 : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkLower : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    linarith only [hn2]
  have hgap := (coordinate_degree_rounding_bounds n M a ha hlarge).2.1
  have hprod := mul_le_mul hgap hkLower (by positivity) (by positivity)
  have heq : (a * ((M : ℝ) / n) / 8) * ((n : ℝ) / 2) = a * M / 16 := by field_simp; ring
  rw [heq] at hprod
  have hscaled := mul_le_mul_of_nonneg_left hprod hL
  have hjR : (j : ℝ) ≤ M := by exact_mod_cast hj
  have hjscaled := mul_le_mul_of_nonneg_left hjR (show 0 ≤ a * L / 32 by positivity)
  have hpos : 0 ≤ a * L * M := by positivity
  nlinarith only [hscaled, hjscaled, hpos]

end

end Erdos747
