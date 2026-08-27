import ErdosProblems.Erdos4.FGKMTGrowingRadius
import ErdosProblems.Erdos4.FGKMTHarmonicModulusSize

/-! The growing pre-sieve modulus and eight radius factors fit the proved level. -/

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

theorem eventually_harmonicModulus_log_small :
    ∀ᶠ x : ℕ in atTop, ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
      Real.log (harmonicModulus (growingPrecutoff x) B : ℝ) ≤ Real.log (x : ℝ) / 100 := by
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growingPrecutoff_bounds,
    sqrtLog_tendsto_atTop.eventually (eventually_ge_atTop (100 * (Real.log 4 + 1))),
    hlogTop.eventually (eventually_ge_atTop 1)] with x hD hlarge hlog
  let u := Real.sqrt (Real.log (x : ℝ))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u ^ 2 = Real.log (x : ℝ) := Real.sq_sqrt (Real.log_natCast_nonneg x)
  change 100 * (Real.log 4 + 1) ≤ u at hlarge
  have hDu : (growingPrecutoff x : ℝ) ≤ u := by
    apply hD.2.2.trans
    change Real.log (x : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ))
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  intro a ha B hB hBx
  have hh := harmonicModulus_log_le_excision (growingPrecutoff x) hB hBx
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hDmul := mul_le_mul_of_nonneg_left hDu hlog4
  have hamul := mul_le_mul_of_nonneg_right ha hu
  have hlargeMul := mul_le_mul_of_nonneg_right hlarge hu
  change Real.log (harmonicModulus (growingPrecutoff x) B : ℝ) ≤ Real.log 4 * (growingPrecutoff x : ℝ) + a * u at hh
  rw [← husq]
  nlinarith

theorem eventually_growing_modulus_level :
    ∀ᶠ x : ℕ in atTop, ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
      harmonicModulus (growingPrecutoff x) B * growingRadius x ^ 8 ≤ powerDistributionLevel x := by
  filter_upwards [eventually_harmonicModulus_log_small, eventually_growingRadius_bounds,
    eventually_ge_atTop 1] with x hW hR hx
  intro a ha B hB hBx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hRpos : (0 : ℝ) < growingRadius x := by exact_mod_cast (by omega : 0 < growingRadius x)
  have hWpos : (0 : ℝ) < harmonicModulus (growingPrecutoff x) B := by
    exact_mod_cast harmonicModulus_pos (growingPrecutoff x) hB
  have hRlog : Real.log (growingRadius x : ℝ) ≤ (1 / 50 : ℝ) * Real.log (x : ℝ) := by
    have hh := Real.log_le_log hRpos (growingRadius_upper x)
    simpa only [Real.log_rpow hxpos] using hh
  have hlogx := Real.log_natCast_nonneg x
  have hWlog := hW a ha B hB hBx
  have hlogProd : Real.log ((harmonicModulus (growingPrecutoff x) B * growingRadius x ^ 8 : ℕ) : ℝ) ≤
      Real.log (x : ℝ) * (1 / 3 : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hWpos.ne' (pow_ne_zero 8 hRpos.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  apply Nat.le_floor
  change ((harmonicModulus (growingPrecutoff x) B * growingRadius x ^ 8 : ℕ) : ℝ) ≤ vaughanCubeRoot x
  calc
    _ = Real.exp (Real.log ((harmonicModulus (growingPrecutoff x) B * growingRadius x ^ 8 : ℕ) : ℝ)) := by
      symm
      apply Real.exp_log
      rw [Nat.cast_mul, Nat.cast_pow]
      positivity
    _ ≤ Real.exp (Real.log (x : ℝ) * (1 / 3 : ℝ)) := Real.exp_le_exp.mpr hlogProd
    _ = _ := by
      change Real.exp (Real.log (x : ℝ) * (1 / 3 : ℝ)) = (x : ℝ) ^ (1 / 3 : ℝ)
      exact (Real.rpow_def_of_pos hxpos (1 / 3 : ℝ)).symm

end Erdos4.FGKMT
