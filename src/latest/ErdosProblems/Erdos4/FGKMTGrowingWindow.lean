import ErdosProblems.Erdos4.FGKMTGrowingDivisorLaw

/-! The growing small-prime cutoff lies below the sieve radius. -/

namespace Erdos4.FGKMT

open Filter Asymptotics

theorem eventually_growing_pre_le_radius :
    ∀ᶠ x : ℕ in atTop, growingPrecutoff x ≤ growingRadius x := by
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp_tendsto
    hlogTop).bound (by norm_num : (0 : ℝ) < 1 / 100)
  filter_upwards [hsmall, eventually_growingPrecutoff_bounds, eventually_growingRadius_bounds,
    hlogTop.eventually (eventually_ge_atTop 2)] with x hsmall hD hR hL
  let L := Real.log (x : ℝ)
  change 2 ≤ L at hL
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hsmall' : Real.log L ≤ L / 100 := by
    change ‖Real.log L‖ ≤ (1 / 100) * ‖L ^ (1 : ℝ)‖ at hsmall
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hlogL, abs_of_pos hLpos,
      one_div_mul_eq_div] using hsmall
  have hRpos : (0 : ℝ) < growingRadius x := by exact_mod_cast (by omega : 0 < growingRadius x)
  have hLleR : L ≤ (growingRadius x : ℝ) :=
    (Real.log_le_log_iff hLpos hRpos).mp (hsmall'.trans hR.2)
  have hDtoL : (growingPrecutoff x : ℝ) ≤ L := hD.2.2.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  exact_mod_cast hDtoL.trans hLleR

end Erdos4.FGKMT
