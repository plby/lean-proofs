import ErdosProblems.Erdos421.LogMomentPower

/-! # Extracting a power saving from the short-shift moment root -/

namespace Erdos421

theorem logarithmic_moment_root_identity {p : ℕ} (hp : 0 < p) {A M C : ℝ}
    (hA : 0 < A) (hM : 0 < M) (hC : 0 ≤ C) :
    (A ^ (p - 1) * (C * M ^ (p + 3))) ^ ((p : ℝ)⁻¹) / M =
      C ^ ((p : ℝ)⁻¹) * A ^ (1 - (p : ℝ)⁻¹) * M ^ (3 * (p : ℝ)⁻¹) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have heA : ((p - 1 : ℕ) : ℝ) * (p : ℝ)⁻¹ = 1 - (p : ℝ)⁻¹ := by
    rw [Nat.cast_sub hp, Nat.cast_one, sub_mul, mul_inv_cancel₀ hpR.ne', one_mul]
  have heM : ((p + 3 : ℕ) : ℝ) * (p : ℝ)⁻¹ = 1 + 3 * (p : ℝ)⁻¹ := by
    push_cast
    rw [add_mul, mul_inv_cancel₀ hpR.ne']
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC (by positivity),
    ← Real.rpow_natCast A (p - 1), ← Real.rpow_natCast M (p + 3),
    ← Real.rpow_mul hA.le, ← Real.rpow_mul hM.le, heA, heM,
    Real.rpow_add hM, Real.rpow_one]
  field_simp

theorem logarithmic_moment_root_power_bound {p : ℕ} (hp : 0 < p) {A M C : ℝ}
    (hA : 1 ≤ A) (hM : 0 < M) (hC : 0 ≤ C) (hMA : M ≤ A ^ (1 / 6 : ℝ)) :
    (A ^ (p - 1) * (C * M ^ (p + 3))) ^ ((p : ℝ)⁻¹) / M + 4 * M ≤
      (C ^ ((p : ℝ)⁻¹) + 4) * A ^ (1 - (p : ℝ)⁻¹ / 2) := by
  have hAp : 0 < A := by linarith
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hpR).mpr hpone
  have hmpow : M ^ (3 * (p : ℝ)⁻¹) ≤ A ^ ((p : ℝ)⁻¹ / 2) := by
    have h := Real.rpow_le_rpow hM.le hMA (by positivity : 0 ≤ 3 * (p : ℝ)⁻¹)
    rw [← Real.rpow_mul hAp.le, show (1 / 6 : ℝ) * (3 * (p : ℝ)⁻¹) =
      (p : ℝ)⁻¹ / 2 by ring] at h
    exact h
  have hMfinal : M ≤ A ^ (1 - (p : ℝ)⁻¹ / 2) :=
    hMA.trans (Real.rpow_le_rpow_of_exponent_le hA (by linarith))
  rw [logarithmic_moment_root_identity hp hAp hM hC]
  calc
    _ ≤ C ^ ((p : ℝ)⁻¹) * A ^ (1 - (p : ℝ)⁻¹) * A ^ ((p : ℝ)⁻¹ / 2) +
        4 * A ^ (1 - (p : ℝ)⁻¹ / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hmpow (by positivity))
        (mul_le_mul_of_nonneg_left hMfinal (by norm_num))
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hAp,
        show 1 - (p : ℝ)⁻¹ + (p : ℝ)⁻¹ / 2 = 1 - (p : ℝ)⁻¹ / 2 by ring]
      ring

end Erdos421
