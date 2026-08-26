/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceNormalization

/-!
# Growth of the source singular-product cutoff

When the companion logarithmic scale is `log Y`, the numerical source
conditions already imply all the extra truncation conditions: `Y` tends
to infinity, `w ≤ Y < q`, and `V / Y` tends to zero.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped Topology

theorem ambient_le_companion_scale_sq {V LE : ℝ}
    (hV : 1 ≤ V) (hLE : 2 * (V + 1) ^ (3 / 4 : ℝ) ≤ LE) : V ≤ LE ^ 2 := by
  have hr := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ V + 1)
    (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
  have hr0 : 0 ≤ (V + 1) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hsqrt : Real.sqrt (V + 1) ≤ LE := by
    rw [Real.sqrt_eq_rpow]
    linarith
  have hs := mul_self_le_mul_self (Real.sqrt_nonneg (V + 1)) hsqrt
  rw [← pow_two, ← pow_two, Real.sq_sqrt (by linarith)] at hs
  linarith

theorem tendsto_sourceCompanionScale_atTop
    {α : Type*} {l : Filter α} {V LE : α → ℝ}
    (hV : Tendsto V l atTop)
    (hLE : ∀ᶠ a in l, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ LE a) :
    Tendsto LE l atTop := by
  have hplus : Tendsto (fun a ↦ V a + 1) l atTop :=
    hV.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hr := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hplus).const_mul_atTop
    (by norm_num : (0 : ℝ) < 2)
  exact tendsto_atTop_mono' l hLE hr

theorem sourceNormalizationConditions_cutoff_comparison
    {K w m q T Y : ℕ} {V : ℝ} (hK : 0 < K) (hV : 1 ≤ V)
    (h : SourceNormalizationConditions K w m q T V (Real.log Y)) : w ≤ Y ∧ Y < q := by
  have hY1 : (1 : ℝ) < Y := (Real.log_pos_iff (Nat.cast_nonneg Y)).mp h.companion_scale_pos
  have hY0 : (0 : ℝ) < Y := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast h.auxiliary_prime.pos
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hLE := mul_le_mul_of_nonneg_right hKr h.companion_scale_pos.le
  have hlogq : Real.log Y < Real.log q := by
    linarith [h.companion_scale_small, h.half_ambient_le_log_auxiliary]
  constructor
  · have hYsq := ambient_le_companion_scale_sq hV h.companion_scale_lower
    have hlog : Real.log (V + 1) ≤ Y := by
      have hsqrt : Real.sqrt (V + 1) ≤ Real.log Y := by
        have hr := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ V + 1)
          (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
        have hr0 : 0 ≤ (V + 1) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
        rw [Real.sqrt_eq_rpow]
        linarith [h.companion_scale_lower]
      have hlogle : Real.log (V + 1) ≤ 2 * Real.sqrt (V + 1) := by
        have hpos : 0 < Real.sqrt (V + 1) := Real.sqrt_pos.mpr (by linarith)
        have hlogroot := Real.log_le_self hpos.le
        rw [Real.log_sqrt (by linarith)] at hlogroot
        linarith
      have hlogY : 2 * Real.log Y ≤ Y := by
        have ht := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hY0)
        rw [Real.log_sqrt hY0.le] at ht
        have hs := Real.sq_sqrt hY0.le
        nlinarith [sq_nonneg (Real.sqrt (Y : ℝ) - 2)]
      exact hlogle.trans ((mul_le_mul_of_nonneg_left hsqrt (by norm_num)).trans hlogY)
    exact_mod_cast h.cutoff_small.trans hlog
  · exact_mod_cast (Real.log_lt_log_iff hY0 hq0).mp hlogq

theorem tendsto_sourceCutoff_atTop_and_ambient_div_zero
    {α : Type*} {l : Filter α} (Y : α → ℕ) (V : α → ℝ)
    (hV : Tendsto V l atTop)
    (hscale : ∀ᶠ a in l, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ Real.log (Y a)) :
    Tendsto Y l atTop ∧ Tendsto (fun a ↦ V a / Y a) l (𝓝 0) := by
  have hlogY := tendsto_sourceCompanionScale_atTop hV hscale
  have hYreal : Tendsto (fun a ↦ (Y a : ℝ)) l atTop :=
    tendsto_atTop_mono (fun a ↦ Real.log_le_self (Nat.cast_nonneg (Y a))) hlogY
  have hY : Tendsto Y l atTop := tendsto_natCast_atTop_iff.mp hYreal
  refine ⟨hY, ?_⟩
  have hl : Tendsto (fun x : ℝ ↦ Real.log x ^ 2 / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlim := hl.comp hYreal
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hV.eventually_ge_atTop 1] with a ha
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  · filter_upwards [hV.eventually_ge_atTop 1, hscale] with a ha hsa
    exact div_le_div_of_nonneg_right (ambient_le_companion_scale_sq ha hsa) (Nat.cast_nonneg _)

end

end Erdos4b
