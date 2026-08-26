/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.RankinDyadicLogBounds

/-!
# A fixed explicit Rankin envelope on every dyadic ray

The bound loses only a constant depending on the already fixed ray a.
The multiplier D in the covering theorem is still completely arbitrary.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

theorem rankinFactor_dyadicIndexLog_le {a r : ℕ} (hr : 4 ≤ r) (ha : a + 1 ≤ r) :
    rankinFactor (dyadicIndexLog a r) ≤
      (2 * dyadicAmbientScale a r) * (3 * r) / ((2 : ℝ) ^ r / 4) ^ 2 := by
  have hV : 0 < dyadicAmbientScale a r :=
    lt_of_lt_of_le (by norm_num) (one_le_dyadicAmbientScale a r)
  have hp : (16 : ℝ) ≤ (2 : ℝ) ^ r := by
    have hh := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hr
    exact_mod_cast hh
  have hlog := log_dyadicIndexLog_lower (a := a) (by omega : 1 ≤ r)
  have hll : 0 ≤ Real.log (Real.log (dyadicIndexLog a r)) :=
    Real.log_nonneg (by linarith)
  have hnum := mul_le_mul (dyadicIndexLog_bounds (a := a) (by omega : 1 ≤ r)).2
    (loglog_dyadicIndexLog_upper hr ha) hll
    (mul_nonneg (by norm_num) (le_trans (by norm_num) (one_le_dyadicAmbientScale a r)))
  have hden : ((2 : ℝ) ^ r / 4) ^ 2 ≤ Real.log (dyadicIndexLog a r) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlog 2
  exact (div_le_div_of_nonneg_right hnum (sq_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)

theorem dyadic_rankin_envelope_le {a r : ℕ} (hr : 4 ≤ r) (ha : a + 1 ≤ r) :
    (3 * (primaryFrontier a r : ℝ)) * rankinFactor (dyadicIndexLog a r) ≤
      (288 * (2 : ℝ) ^ a) * (intervalLength a r : ℝ) := by
  have hX : (0 : ℝ) < primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have hcore : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hp : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hpow : (2 : ℝ) ^ (a + 2 * r) = (2 : ℝ) ^ a * ((2 : ℝ) ^ r) ^ 2 := by
    rw [pow_add, Nat.mul_comm 2 r, pow_mul]
  calc
    _ ≤ (3 * (primaryFrontier a r : ℝ)) *
        ((2 * dyadicAmbientScale a r) * (3 * r) / ((2 : ℝ) ^ r / 4) ^ 2) :=
      mul_le_mul_of_nonneg_left (rankinFactor_dyadicIndexLog_le hr ha) (by positivity)
    _ = (288 * (2 : ℝ) ^ a * primaryFrontier a r * core r * r) * Real.log 2 := by
      rw [dyadicAmbientScale_expand, hpow]
      field_simp
      <;> ring
    _ ≤ 288 * (2 : ℝ) ^ a * primaryFrontier a r * core r * r := by
      exact mul_le_of_le_one_right (by positivity) rankin_log_two_le_one
    _ = _ := by
      simp only [intervalLength, Nat.cast_mul]
      ring

end

end Erdos4b.SmoothParameters
