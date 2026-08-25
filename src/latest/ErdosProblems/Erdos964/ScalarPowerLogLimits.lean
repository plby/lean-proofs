import ErdosProblems.Erdos964.ScalarAffinePrimeSupport
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic limits of the concrete power radius
-/

namespace Erdos964

open Asymptotics BoundedGaps.Maynard Filter
open scoped Asymptotics Topology

theorem tendsto_scalar_power_radius (β : ℝ) (hβ : 0 < β) :
    Tendsto (modulusCutoff β) atTop atTop := by
  change Tendsto (fun t : ℕ => ⌊Real.rpow (t : ℝ) β⌋₊) atTop atTop
  have hp : Tendsto (fun t : ℕ => (t : ℝ) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  simpa only [modulusCutoff, Real.rpow_eq_pow, Function.comp_def] using
    tendsto_nat_floor_atTop.comp hp

theorem tendsto_log_scalar_power_radius (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun t : ℕ => Real.log (modulusCutoff β t)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_scalar_power_radius β hβ))

theorem tendsto_log_scalar_power_radius_div_log (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun t : ℕ => Real.log (modulusCutoff β t) / Real.log t) atTop (𝓝 β) := by
  have hp : Tendsto (fun t : ℕ => (t : ℝ) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  have hf : (fun t : ℕ => (modulusCutoff β t : ℝ)) ~[atTop]
      (fun t : ℕ => (t : ℝ) ^ β) := by
    simpa only [modulusCutoff, Real.rpow_eq_pow, Function.comp_def] using
      (isEquivalent_nat_floor (R := ℝ)).comp_tendsto hp
  have hlog := hf.log hp
  have htarget : Tendsto (fun t : ℕ => Real.log ((t : ℝ) ^ β) / Real.log t)
      atTop (𝓝 β) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 2] with t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    rw [Real.log_rpow htpos]
    field_simp
  have hdiv := hlog.div (IsEquivalent.refl (u := fun t : ℕ => Real.log t))
  exact hdiv.symm.tendsto_nhds htarget

theorem tendsto_log_scalar_power_radius_div_log_square (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun t : ℕ => Real.log (modulusCutoff β t) / Real.log (t ^ 2 : ℕ))
      atTop (𝓝 (β / 2)) := by
  have h := (tendsto_log_scalar_power_radius_div_log β hβ).div_const 2
  apply h.congr'
  filter_upwards [] with t
  rw [Nat.cast_pow, Real.log_pow]
  norm_num
  ring

end Erdos964
