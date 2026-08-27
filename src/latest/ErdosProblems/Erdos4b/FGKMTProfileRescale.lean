/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLongFactor

/-!
# Support-preserving rescaling of the long and short factors

Both factors are moved to the unit interval by evaluating them at
twice the argument. The exact half-mass identities retain the full
long support `[0,2]` and cancel the doubled logarithmic scale.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem sieveFactor_double_arg (T U t : ℝ) :
    sieveFactor T U (2 * t) = sieveFactor (2 * T) (U / 2) t := by
  have harg : (2 * t) / U = t / (U / 2) := by ring
  have hden : T * (2 * t) = (2 * T) * t := by ring
  simp only [sieveFactor, harg, hden]

theorem integral_double_arg (f : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..1, f (2 * t)) = (1 / 2) * (∫ t in (0 : ℝ)..2, f t) := by
  simpa only [mul_zero, mul_one, smul_eq_mul, one_div] using!
    intervalIntegral.integral_comp_mul_left f (a := 0) (b := 1) (by norm_num : (2 : ℝ) ≠ 0)

theorem dimensionProfileMass_eq_double_interval {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    (∫ t in (0 : ℝ)..2, dimensionProfileFactor k t ^ 2) = dimensionProfileMass k := by
  have hb := profile_scales_bounds hk hlog
  have hU1 : sieveProfileWidth k ≤ 1 := by linarith [hb.2.2.1]
  unfold dimensionProfileMass dimensionProfileFactor
  rw [sieveFactor_pow_integral_eq hb.2.1 (by linarith [hb.2.2.1]) (sieveProfileScale k) 1,
    sieveFactor_sq_unit_mass_eq hb.2.1 hU1]

theorem rescaled_short_mass {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    (∫ t in (0 : ℝ)..1, sieveFactor (2 * sieveProfileScale k) (sieveProfileWidth k / 2) t ^ 2) =
      dimensionProfileMass k / 2 := by
  simp_rw [← sieveFactor_double_arg]
  rw [integral_double_arg (fun t => sieveFactor (sieveProfileScale k) (sieveProfileWidth k) t ^ 2)]
  change (1 / 2) * (∫ t in (0 : ℝ)..2, dimensionProfileFactor k t ^ 2) = _
  rw [dimensionProfileMass_eq_double_interval hk hlog]
  ring

theorem rescaled_long_mass (k : ℕ) :
    (∫ t in (0 : ℝ)..1, sieveFactor (2 * sieveProfileScale k) 1 t ^ 2) =
      dimensionLongMass k / 2 := by
  have heq (t : ℝ) : sieveFactor (2 * sieveProfileScale k) 1 t =
      sieveFactor (sieveProfileScale k) 2 (2 * t) := by
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0)] using
      (sieveFactor_double_arg (sieveProfileScale k) 2 t).symm
  simp_rw [heq]
  rw [integral_double_arg (fun t => sieveFactor (sieveProfileScale k) 2 t ^ 2)]
  unfold dimensionLongMass dimensionLongFactor
  ring

theorem log_nat_sq (R : ℕ) : Real.log (R ^ 2 : ℕ) = 2 * Real.log R := by
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]

theorem rescaled_short_log_mass {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) (R : ℕ) :
    Real.log (R ^ 2 : ℕ) *
      (∫ t in (0 : ℝ)..1, sieveFactor (2 * sieveProfileScale k) (sieveProfileWidth k / 2) t ^ 2) =
      Real.log R * dimensionProfileMass k := by
  rw [rescaled_short_mass hk hlog, log_nat_sq]
  ring

theorem rescaled_long_log_mass (k R : ℕ) :
    Real.log (R ^ 2 : ℕ) *
      (∫ t in (0 : ℝ)..1, sieveFactor (2 * sieveProfileScale k) 1 t ^ 2) =
      Real.log R * dimensionLongMass k := by
  rw [rescaled_long_mass, log_nat_sq]
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.rescaled_short_log_mass
#print axioms Erdos4b.FGKMT.rescaled_long_log_mass
