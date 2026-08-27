import ErdosProblems.Erdos4.FGKMTFiniteDistribution
import ErdosProblems.Erdos4.FGKMTLogarithmicAbsorption

/-! Scalar Vaughan-envelope bounds at a fixed positive power level. -/

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

theorem cubeRoot_sq_eq_two_thirds (x : ℕ) :
    vaughanCubeRoot x ^ 2 = (x : ℝ) ^ (2 / 3 : ℝ) := by
  unfold vaughanCubeRoot
  calc
    _ = ((x : ℝ) ^ (1 / 3 : ℝ)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
    _ = (x : ℝ) ^ ((1 / 3 : ℝ) * 2) := (Real.rpow_mul (Nat.cast_nonneg x) _ _).symm
    _ = _ := by norm_num

theorem sqrt_cubeRoot_eq_one_sixth (x : ℕ) :
    Real.sqrt (vaughanCubeRoot x) = (x : ℝ) ^ (1 / 6 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  change Real.rpow (Real.rpow (x : ℝ) (1 / 3 : ℝ)) (1 / 2 : ℝ) = _
  calc
    _ = Real.rpow (x : ℝ) ((1 / 3 : ℝ) * (1 / 2 : ℝ)) :=
      (Real.rpow_mul (Nat.cast_nonneg x) _ _).symm
    _ = _ := by norm_num

theorem sqrt_mul_cubeRoot_eq_five_sixths {x : ℕ} (hx : 1 ≤ x) :
    Real.sqrt (x : ℝ) * vaughanCubeRoot x = (x : ℝ) ^ (5 / 6 : ℝ) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  rw [Real.sqrt_eq_rpow]
  change Real.rpow (x : ℝ) (1 / 2 : ℝ) * Real.rpow (x : ℝ) (1 / 3 : ℝ) = _
  calc
    _ = Real.rpow (x : ℝ) ((1 / 2 : ℝ) + (1 / 3 : ℝ)) := (Real.rpow_add hxpos _ _).symm
    _ = _ := by norm_num

theorem cubeRoot_le_self {x : ℕ} (hx : 1 ≤ x) : vaughanCubeRoot x ≤ (x : ℝ) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  change (x : ℝ) ^ (1 / 3 : ℝ) ≤ (x : ℝ)
  exact (Real.rpow_le_rpow_of_exponent_le hx1
    (by norm_num : (1 / 3 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)

theorem vaughanEnvelope_power_level {x : ℕ} (hx : 1 ≤ x) {R Q : ℝ}
    (hR : 1 ≤ R) (hRQ : R ≤ Q) (hQ : Q ≤ vaughanCubeRoot x) :
    vaughanPrimitiveMeanAbelEnvelope x R Q ≤
      4 * (x : ℝ) / R + 27 * (x : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log (x : ℝ)) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hQ0 : 0 < Q := by linarith
  have hQx : Q ≤ (x : ℝ) := hQ.trans (cubeRoot_le_self hx)
  have hlogx := Real.log_natCast_nonneg x
  have hpow : 0 ≤ (x : ℝ) ^ (5 / 6 : ℝ) := Real.rpow_nonneg hxpos.le _
  have hroot : Real.sqrt (x : ℝ) * Q ≤ (x : ℝ) ^ (5 / 6 : ℝ) := by
    calc
      _ ≤ Real.sqrt (x : ℝ) * vaughanCubeRoot x :=
        mul_le_mul_of_nonneg_left hQ (Real.sqrt_nonneg _)
      _ = _ := sqrt_mul_cubeRoot_eq_five_sixths hx
  have hcube : vaughanCubeRoot x ^ 2 * Real.sqrt Q ≤ (x : ℝ) ^ (5 / 6 : ℝ) := by
    calc
      _ ≤ vaughanCubeRoot x ^ 2 * Real.sqrt (vaughanCubeRoot x) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQ) (sq_nonneg _)
      _ = (x : ℝ) ^ (5 / 6 : ℝ) := by
        rw [cubeRoot_sq_eq_two_thirds, sqrt_cubeRoot_eq_one_sixth, ← Real.rpow_add hxpos]
        norm_num
  have hlog : Real.log (Real.exp 1 * Q / R) ≤ 1 + Real.log (x : ℝ) := by
    have hQR : Q / R ≤ (x : ℝ) := (div_le_self hQ0.le hR).trans hQx
    calc
      _ ≤ Real.log (Real.exp 1 * (x : ℝ)) := by
        apply Real.log_le_log (by positivity)
        have hh := mul_le_mul_of_nonneg_left hQR (Real.exp_pos 1).le
        simpa only [mul_div_assoc] using hh
      _ = _ := by rw [Real.log_mul (Real.exp_pos 1).ne' hxpos.ne', Real.log_exp]
  have hlast : 5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
      Real.log (Real.exp 1 * Q / R) ≤ 5 * (x : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log (x : ℝ)) := by
    rw [sqrt_mul_cubeRoot_eq_five_sixths hx]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  unfold vaughanPrimitiveMeanAbelEnvelope
  nlinarith [mul_nonneg hpow hlogx]

theorem meanLogPower_eq_ninth_sqrtLog (x : ℕ) :
    vaughanPrimitiveMeanEquationOneTwoLogPower x = Real.sqrt (Real.log (x : ℝ)) ^ 9 := by
  unfold vaughanPrimitiveMeanEquationOneTwoLogPower
  rw [← Real.sq_sqrt (Real.log_natCast_nonneg x)]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
  ring

theorem progression_boundary_power_level {x Q : ℕ} (hx : 1 ≤ x) (hQ1 : 1 ≤ Q)
    (hQ : (Q : ℝ) ≤ vaughanCubeRoot x) :
    (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 ≤
      4 * (x : ℝ) ^ (1 / 3 : ℝ) * Real.sqrt (Real.log (x : ℝ)) ^ 4 := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hQx := hQ.trans (cubeRoot_le_self hx)
  have hlogQ := Real.log_le_log hQpos hQx
  have hlog0 := Real.log_natCast_nonneg (Q * x)
  have hlog : Real.log ((Q * x : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hQpos.ne' hxpos.ne']
    linarith
  have hsquare : Real.log ((Q * x : ℕ) : ℝ) ^ 2 ≤ 4 * Real.log (x : ℝ) ^ 2 := by
    exact (pow_le_pow_left₀ hlog0 hlog 2).trans_eq (by ring)
  calc
    _ ≤ vaughanCubeRoot x * (4 * Real.log (x : ℝ) ^ 2) :=
      mul_le_mul hQ hsquare (sq_nonneg _) (vaughanCubeRoot_nonneg x)
    _ = _ := by
      change (x : ℝ) ^ (1 / 3 : ℝ) * (4 * Real.log (x : ℝ) ^ 2) = _
      rw [← Real.sq_sqrt (Real.log_natCast_nonneg x)]
      simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
      ring

end Erdos4.FGKMT
