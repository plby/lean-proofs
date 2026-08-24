import ErdosProblems.Erdos587.PowerScales
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The nearby mean at the critical terminal scale

All thresholds below are uniform in the integral progression parameters.
The smooth function is fixed; the cutoff may contain any fixed logarithmic
power and a power enlargement strictly below `T^(3/125)`.
No assertion about a varying family of smooth functions is used.
-/

open Filter
open scoped BigOperators SchwartzMap Topology

namespace Erdos587

lemma eventually_const_mul_one_add_log_pow_le_rpow (C : ℝ) (p : ℕ)
    (hC : 0 ≤ C) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ T : ℝ in atTop, C * (1 + Real.log T) ^ p ≤ T ^ s := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (p : ℝ) hs).const_mul_left (C * 2 ^ p)
  filter_upwards [hsmall.def (show (0 : ℝ) < 1 by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)] with T hT hlog hpos
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hT0 : 0 ≤ T := by linarith
  simp only [Real.rpow_natCast, one_mul, Real.norm_of_nonneg (by positivity :
      0 ≤ C * 2 ^ p * Real.log T ^ p),
    Real.norm_of_nonneg (Real.rpow_nonneg hT0 s)] at hT
  calc
    C * (1 + Real.log T) ^ p ≤ C * (2 * Real.log T) ^ p := by gcongr; linarith
    _ = C * 2 ^ p * Real.log T ^ p := by rw [mul_pow]; ring
    _ ≤ T ^ s := hT

lemma eventually_rpow_le_const_mul_rpow {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, T ^ a ≤ c * T ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop (1 / c),
    eventually_ge_atTop (1 : ℝ)] with T hT hpos
  have hTpos : 0 < T := by linarith
  have h1 : 1 ≤ c * T ^ (b - a) := by
    have hh := mul_le_mul_of_nonneg_left hT hc.le
    simpa only [mul_one_div_cancel hc.ne'] using hh
  calc
    T ^ a = 1 * T ^ a := by ring
    _ ≤ (c * T ^ (b - a)) * T ^ a := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = c * T ^ b := by rw [mul_assoc, ← Real.rpow_add hTpos]; congr 2; ring

lemma fortieth_root_pow {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (T ^ (1 / 40 : ℝ)) ^ n = T ^ ((n : ℝ) / 40) := by
  rw [← Real.rpow_mul_natCast hT]
  congr 1
  ring

lemma critical_scale_lower_cutoff (u v H M : ℕ) {T : ℝ}
    (hH : 0 < H) (huH : (u : ℝ) * H ≤ T) (hM : (v : ℝ) / H ≤ M) :
    (u : ℝ) * v ≤ M * T := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hv := (div_le_iff₀ hHR).mp hM
  calc
    (u : ℝ) * v ≤ u * (M * H) := mul_le_mul_of_nonneg_left hv (by positivity)
    _ = M * ((u : ℝ) * H) := by ring
    _ ≤ M * T := mul_le_mul_of_nonneg_left huH (by positivity)

lemma critical_scale_upper_cutoff (v H M p : ℕ) {T C₀ : ℝ}
    (hT : 1 ≤ T) (hH : 0 < H) (hC₀ : 0 ≤ C₀)
    (hHlo : Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H)
    (hM : (M : ℝ) ≤ C₀ * ((v : ℝ) / H) * (1 + Real.log T) ^ p)
    (hlog : C₀ * (1 + Real.log T) ^ p ≤ T ^ (3 / 125 : ℝ)) :
    (M : ℝ) * (T ^ (1 / 40 : ℝ)) ^ 19 ≤ v := by
  have hTpos : 0 < T := by linarith
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hlog0 : 0 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
  have hHpower : T ^ (499 / 1000 : ℝ) ≤ H := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hTpos] at hHlo
    norm_num at hHlo
    exact hHlo
  have hweight : (C₀ * (1 + Real.log T) ^ p) * (T ^ (1 / 40 : ℝ)) ^ 19 ≤ H := by
    calc
      _ ≤ T ^ (3 / 125 : ℝ) * (T ^ (1 / 40 : ℝ)) ^ 19 := by gcongr
      _ = T ^ (499 / 1000 : ℝ) := by
        rw [fortieth_root_pow hTpos.le, ← Real.rpow_add hTpos]
        norm_num
      _ ≤ H := hHpower
  have hMH : (M : ℝ) * H ≤ C₀ * v * (1 + Real.log T) ^ p := by
    apply (le_div_iff₀ hHR).mp
    calc
      (M : ℝ) ≤ C₀ * ((v : ℝ) / H) * (1 + Real.log T) ^ p := hM
      _ = (C₀ * v * (1 + Real.log T) ^ p) / H := by ring
  apply (mul_le_mul_iff_left₀ hHR).mp
  calc
    _ = ((M : ℝ) * H) * (T ^ (1 / 40 : ℝ)) ^ 19 := by ring
    _ ≤ (C₀ * v * (1 + Real.log T) ^ p) * (T ^ (1 / 40 : ℝ)) ^ 19 := by gcongr
    _ = (v : ℝ) * ((C₀ * (1 + Real.log T) ^ p) * (T ^ (1 / 40 : ℝ)) ^ 19) := by ring
    _ ≤ v * H := mul_le_mul_of_nonneg_left hweight (by positivity)

theorem exists_critical_nearby_mean_bound_with_power_cutoff (f : 𝓢(ℝ, ℂ))
    (c₀ C₀ : ℝ) (p : ℕ) (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀)
    (δ : ℝ) (hδ : δ < 3 / 125) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (a u v H M : ℕ), 0 < u → 0 < v → 0 < H → 0 < M →
        a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
        T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
        c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
        Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
        (v : ℝ) / H ≤ M →
        (M : ℝ) ≤ C₀ * ((v : ℝ) / H) * T ^ δ * (1 + Real.log T) ^ p →
        (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖) ≤
          C * M * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_nearby_mean_bound_of_power_scales f
  refine ⟨C, hC, O, hO, ?_⟩
  have hvlarge := eventually_rpow_le_const_mul_rpow
    (a := (7 / 10 : ℝ)) (b := (3 / 4 - 1 / 1000 : ℝ)) (by norm_num) hc₀
  have hloglarge := eventually_const_mul_one_add_log_pow_le_rpow C₀ p hC₀
    (s := (3 / 125 : ℝ) - δ) (sub_pos.mpr hδ)
  filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 1 / 40 by norm_num)).eventually_ge_atTop 256,
    eventually_ge_atTop (1 : ℝ), hvlarge, hloglarge] with T hx hT hvlarge hloglarge
  intro a u v H M hu hv hH hM ha huv hav hu0 hu1 hv0 hv1 hH0 huH hM0 hM1
  let x := T ^ (1 / 40 : ℝ)
  have hTpos : 0 < T := by linarith
  have hxpos : 0 < x := Real.rpow_pos_of_pos hTpos _
  have hx1 : 1 ≤ x := by change 256 ≤ x at hx; linarith
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
    · convert hM1 using 1 <;> ring
    · calc
        (C₀ * T ^ δ) * (1 + Real.log T) ^ p =
            (C₀ * (1 + Real.log T) ^ p) * T ^ δ := by ring
        _ ≤ T ^ ((3 / 125 : ℝ) - δ) * T ^ δ :=
          mul_le_mul_of_nonneg_right hloglarge (Real.rpow_nonneg hTpos.le δ)
        _ = T ^ (3 / 125 : ℝ) := by rw [← Real.rpow_add hTpos]; congr 1; ring
  have hMcutlo : (u : ℝ) * v ≤ M * x ^ 40 := by
    rw [hx40]
    exact critical_scale_lower_cutoff u v H M hH huH hM0
  have hbound := hmean a u v M hu hv hM ha huv hav x hx hux0 hux1 hvx0 hvx1 hMcut hMcutlo
  have hx10 : x ^ 10 = Real.sqrt (Real.sqrt T) := by
    rw [← hx20, show x ^ 20 = (x ^ 10) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hx20, hx10] at hbound
  have hxT : x ≤ T := by
    change T ^ (1 / 40 : ℝ) ≤ T
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (1 / 40 : ℝ) ≤ 1 by norm_num)
  have hlogx : Real.log x ≤ Real.log T := Real.log_le_log hxpos hxT
  have hlogx0 : 0 ≤ 1 + Real.log x := by have := Real.log_nonneg hx1; linarith
  refine hbound.trans ?_
  gcongr

theorem exists_critical_nearby_mean_bound (f : 𝓢(ℝ, ℂ))
    (c₀ C₀ : ℝ) (p : ℕ) (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (a u v H M : ℕ), 0 < u → 0 < v → 0 < H → 0 < M →
        a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
        T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
        c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
        Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
        (v : ℝ) / H ≤ M → (M : ℝ) ≤ C₀ * ((v : ℝ) / H) * (1 + Real.log T) ^ p →
        (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖) ≤
          C * M * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
  simpa only [Real.rpow_zero, mul_one] using
    exists_critical_nearby_mean_bound_with_power_cutoff f c₀ C₀ p hc₀ hC₀ 0 (by norm_num)

end Erdos587
