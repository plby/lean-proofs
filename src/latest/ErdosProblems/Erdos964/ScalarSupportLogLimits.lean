import ErdosProblems.Erdos964.ScalarPowerLogLimits
import ErdosProblems.Erdos964.LogConvolutionLimit

/-!
# Logarithmic endpoints of the concrete smaller-prime support
-/

namespace Erdos964

open Asymptotics BoundedGaps.Maynard Filter
open scoped Asymptotics Topology

theorem tendsto_log_nat_mul_div_log (K : ℕ) (hK : 0 < K) :
    Tendsto (fun t : ℕ => Real.log (K * t : ℕ) / Real.log t) atTop (𝓝 1) := by
  have hlog : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun t : ℕ => Real.log K / Real.log t + 1) atTop (𝓝 1) := by
    simpa only [zero_add] using (hlog.const_div_atTop (Real.log K)).add_const 1
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with t ht
  have hKt : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  have hlt : Real.log t ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < t by omega))).ne'
  rw [Nat.cast_mul, Real.log_mul hKt ht0]
  field_simp

theorem tendsto_log_nat_div_div_log (d : ℕ) (hd : 0 < d) :
    Tendsto (fun t : ℕ => Real.log (t / d : ℕ) / Real.log t) atTop (𝓝 1) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : Tendsto (fun t : ℕ => (t : ℝ) / d) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hdR
  have hf : (fun t : ℕ => ((t / d : ℕ) : ℝ)) ~[atTop]
      (fun t : ℕ => (t : ℝ) / d) := by
    simpa only [Function.comp_def, Nat.floor_div_natCast, Nat.floor_natCast] using
      (isEquivalent_nat_floor (R := ℝ)).comp_tendsto ht
  have hlog := (hf.log ht).div (IsEquivalent.refl (u := fun t : ℕ => Real.log t))
  have hmain : Tendsto (fun t : ℕ => Real.log ((t : ℝ) / d) / Real.log t) atTop (𝓝 1) := by
    simpa only [Function.comp_def] using
      (tendsto_log_div_fixed_ratio d hdR).comp tendsto_natCast_atTop_atTop
  exact hlog.symm.tendsto_nhds hmain

theorem tendsto_scalar_support_lower_log_ratio (K : ℕ) (hK : 0 < K)
    (η β : ℝ) (hβ : 0 < β) :
    Tendsto (fun t : ℕ => Real.log (Real.rpow (K * t : ℕ) η) /
      Real.log (modulusCutoff β t)) atTop (𝓝 (η / β)) := by
  have hlo : Tendsto (fun t : ℕ => Real.log (Real.rpow (K * t : ℕ) η) / Real.log t)
      atTop (𝓝 η) := by
    have h := (tendsto_log_nat_mul_div_log K hK).const_mul η
    simp only [mul_one] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with t ht
    have hKt : (0 : ℝ) < (K * t : ℕ) := by exact_mod_cast Nat.mul_pos hK ht
    rw [Real.rpow_eq_pow, Real.log_rpow hKt]
    ring
  have h := hlo.div (tendsto_log_scalar_power_radius_div_log β hβ) hβ.ne'
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_log_scalar_power_radius β hβ).eventually (eventually_gt_atTop 0)] with t ht hR
  have hlt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  simp only [Pi.div_apply]
  field_simp

theorem tendsto_scalar_support_upper_log_ratio (K : ℕ) (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun t : ℕ => Real.log (t / (K + 1) : ℕ) /
      Real.log (modulusCutoff β t)) atTop (𝓝 (1 / β)) := by
  have h := (tendsto_log_nat_div_div_log (K + 1) (Nat.succ_pos K)).div
    (tendsto_log_scalar_power_radius_div_log β hβ) hβ.ne'
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_log_scalar_power_radius β hβ).eventually (eventually_gt_atTop 0)] with t ht hR
  have hlt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  simp only [Pi.div_apply]
  field_simp

end Erdos964
