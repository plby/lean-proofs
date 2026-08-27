import ErdosProblems.Erdos4.TiltedDensityParameters
import ErdosProblems.Erdos4.FGKMTGrowingDensityPowers

/-! The composite one-point scale is smaller than `1 / (log x (log₂ x)²)`. -/

namespace Erdos4.Tilted

open Filter FGKMT

noncomputable def compositeSurvivalBound (x : ℕ) : ℝ :=
  primeDensity x * (x : ℝ) ^ (-tiltExponent x)

theorem compositeSurvivalBound_nonneg (x : ℕ) : 0 ≤ compositeSurvivalBound x :=
  mul_nonneg (primeDensity_pos x).le (Real.rpow_nonneg (Nat.cast_nonneg x) _)

theorem compositeSurvivalBound_pos {x : ℕ} (hx : 0 < x) : 0 < compositeSurvivalBound x :=
  mul_pos (primeDensity_pos x) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hx) _)

theorem eventually_tiltScale_mul_le_log_two (C : ℝ) :
    ∀ᶠ x : ℕ in atTop, C * tiltScale x ≤ Real.log (Real.log (x : ℝ)) := by
  have hh := ((Real.isLittleO_log_id_atTop.const_mul_left (4 * C)).comp_tendsto log_two_tendsto).eventuallyLE
  filter_upwards [hh, log_two_tendsto.eventually (eventually_ge_atTop 0)] with x hh hl
  have he : |4 * C * Real.log (Real.log (Real.log (x : ℝ)))| ≤ Real.log (Real.log (x : ℝ)) := by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hl] using hh
  have hh' := (le_abs_self _).trans he
  dsimp [tiltScale]
  nlinarith

theorem base_tilt_eq_log_power {x : ℕ} (hx : 0 < x)
    (hl : 0 < Real.log (Real.log (x : ℝ))) :
    (x : ℝ) ^ (-tiltExponent x) = (Real.log (Real.log (x : ℝ)) ^ (4 : ℕ))⁻¹ := by
  let L := Real.log (x : ℝ)
  let l := Real.log L
  have hLpos : 0 < L := (Real.log_pos_iff (Real.log_natCast_nonneg x)).mp hl |>.trans' zero_lt_one
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  rw [Real.rpow_def_of_pos hxpos]
  have heq : Real.log (x : ℝ) * -tiltExponent x = -(4 * Real.log l) := by
    change L * -(4 * Real.log l / L) = _
    field_simp
  rw [heq, Real.exp_neg]
  have hlog : Real.log (l ^ (4 : ℕ)) = 4 * Real.log l := by rw [Real.log_pow]; norm_num
  rw [← hlog, Real.exp_log (pow_pos hl 4)]

theorem eventually_compositeSurvivalBound :
    ∀ᶠ x : ℕ in atTop, compositeSurvivalBound x ≤
      1 / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ (2 : ℕ)) := by
  obtain ⟨c, C, hc, hC, hdensity⟩ := exists_primeDensity_bounds
  filter_upwards [hdensity, eventually_outerScale_bounds,
    eventually_tiltScale_mul_le_log_two C, eventually_ge_atTop 1]
    with x hd hb ht hx
  let L := Real.log (x : ℝ)
  let l := Real.log L
  have hLpos : 0 < L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have hlpos : 0 < l := by have hh := hb.2.1; change 1 ≤ l at hh; linarith
  rw [compositeSurvivalBound, base_tilt_eq_log_power (by omega) hlpos]
  calc
    _ ≤ (C * tiltScale x * l / L) * (l ^ (4 : ℕ))⁻¹ :=
      mul_le_mul_of_nonneg_right hd.2 (inv_nonneg.mpr (pow_nonneg hlpos.le _))
    _ = (C * tiltScale x) / (L * l ^ 3) := by field_simp
    _ ≤ l / (L * l ^ 3) := div_le_div_of_nonneg_right ht (by positivity)
    _ = _ := by change l / (L * l ^ 3) = 1 / (L * l ^ 2); field_simp

theorem eventually_primeDensity_lower :
    ∀ᶠ x : ℕ in atTop, 1 / Real.log (x : ℝ) ^ (2 : ℕ) ≤ primeDensity x := by
  obtain ⟨c, C, hc, _, hdensity⟩ := exists_primeDensity_bounds
  filter_upwards [hdensity, eventually_outerScale_bounds,
    log_tendsto.eventually (eventually_ge_atTop (1 / c))] with x hd hb hL
  let L := Real.log (x : ℝ)
  let l := Real.log L
  have hLpos : 0 < L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have hl1 : 1 ≤ l := hb.2.1
  have hcL : 1 ≤ c * L := by
    have hh := (div_le_iff₀ hc).mp hL
    change 1 ≤ L * c at hh
    nlinarith
  calc
    _ ≤ c / L := by
      apply (div_le_div_iff₀ (pow_pos hLpos 2) hLpos).mpr
      nlinarith [mul_le_mul_of_nonneg_right hcL hLpos.le]
    _ ≤ c * l / L := div_le_div_of_nonneg_right (by nlinarith) hLpos.le
    _ ≤ _ := hd.1

theorem eventually_primeDensity_inverse_power {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop,
      1 / primeDensity x ^ (3 * sieveDimension (growingIndex x)) ≤ (x : ℝ) ^ a := by
  filter_upwards [eventually_primeDensity_lower, eventually_growing_log_dimension_power ha,
    log_tendsto.eventually (eventually_ge_atTop 1)] with x hA hpower hL
  let L := Real.log (x : ℝ)
  let k := sieveDimension (growingIndex x)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hinv : (primeDensity x)⁻¹ ≤ L ^ 2 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < 1 / L ^ 2) hA
    simpa only [one_div, inv_inv] using hh
  calc
    _ = ((primeDensity x)⁻¹) ^ (3 * k) := by simp only [one_div, inv_pow, k]
    _ ≤ (L ^ 2) ^ (3 * k) := pow_le_pow_left₀ (inv_nonneg.mpr (primeDensity_pos x).le) hinv _
    _ = L ^ (6 * k) := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := hpower

end Erdos4.Tilted
