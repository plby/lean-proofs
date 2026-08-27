import ErdosProblems.Erdos587.HooleyNearbyPowerScale
import ErdosProblems.Erdos587.CriticalScale

/-! # The log-log nearby mean at the critical terminal scale -/

open Filter
open scoped BigOperators SchwartzMap Topology

namespace Erdos587

theorem exists_delta_critical_nearby_mean_with_power_cutoff (f : 𝓢(ℝ, ℂ))
    (c₀ C₀ : ℝ) (p : ℕ) (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀)
    (δ : ℝ) (hδ : δ < 3 / 125) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a u v H M : ℕ, 0 < u → 0 < v → 0 < H → 0 < M →
      a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
      T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
      c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
      Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
      (v : ℝ) / H ≤ M →
      (M : ℝ) ≤ C₀ * ((v : ℝ) / H) * T ^ δ * (1 + Real.log T) ^ p →
      (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖) ≤
        C * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ (9 / 2 : ℝ) := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_nearby_mean_of_power_scales f
  refine ⟨C, hC, ?_⟩
  have hvlarge := eventually_rpow_le_const_mul_rpow
    (a := (7 / 10 : ℝ)) (b := (3 / 4 - 1 / 1000 : ℝ)) (by norm_num) hc₀
  have hloglarge := eventually_const_mul_one_add_log_pow_le_rpow C₀ p hC₀
    (s := (3 / 125 : ℝ) - δ) (sub_pos.mpr hδ)
  filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 1 / 40 by norm_num)).eventually_ge_atTop 256,
    eventually_ge_atTop (1 : ℝ), hvlarge, hloglarge] with T hx hT hvlarge hloglarge
  intro a u v H M hu hv hH _hM ha huv hav hu0 hu1 hv0 hv1 hH0 huH hM0 hM1
  let x := T ^ (1 / 40 : ℝ)
  have hTpos : 0 < T := by linarith
  have hxpos : 0 < x := Real.rpow_pos_of_pos hTpos _
  have hxpow (n : ℕ) : x ^ n = T ^ ((n : ℝ) / 40) := fortieth_root_pow hTpos.le n
  have hx20 : x ^ 20 = Real.sqrt T := by rw [hxpow, Real.sqrt_eq_rpow]; norm_num
  have hx40 : x ^ 40 = T := by rw [hxpow]; norm_num
  have hux0 : x ^ 2 ≤ (u : ℝ) := by
    apply le_trans _ hu0
    rw [hxpow]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hux1 : (u : ℝ) ≤ x ^ 22 := by
    apply hu1.trans
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hTpos, hxpow]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hvx0 : x ^ 28 ≤ (v : ℝ) := by
    apply le_trans _ (hvlarge.trans hv0)
    rw [hxpow]
    norm_num
  have hvx1 : (v : ℝ) ≤ x ^ 30 := by
    rw [hxpow]
    norm_num
    exact hv1
  have hMcut : (M : ℝ) * x ^ 19 ≤ v := by
    apply critical_scale_upper_cutoff v H M p hT hH
      (mul_nonneg hC₀ (Real.rpow_nonneg hTpos.le δ)) hH0
    · convert hM1 using 1
      ring
    · calc
        (C₀ * T ^ δ) * (1 + Real.log T) ^ p =
            (C₀ * (1 + Real.log T) ^ p) * T ^ δ := by ring
        _ ≤ T ^ ((3 / 125 : ℝ) - δ) * T ^ δ :=
          mul_le_mul_of_nonneg_right hloglarge (Real.rpow_nonneg hTpos.le δ)
        _ = T ^ (3 / 125 : ℝ) := by rw [← Real.rpow_add hTpos]; congr 1; ring
  have hMcutlo : (u : ℝ) * v ≤ M * x ^ 40 := by
    rw [hx40]
    exact critical_scale_lower_cutoff u v H M hH huH hM0
  have hbound := hmean a u v M hu hv ha huv hav x hx hux0 hux1 hvx0 hvx1 hMcut hMcutlo
  have hx10 : x ^ 10 = Real.sqrt (Real.sqrt T) := by
    rw [← hx20, show x ^ 20 = (x ^ 10) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  simpa only [hx20, hx10, hx40] using hbound

end Erdos587
