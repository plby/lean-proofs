import BoundedGaps.BombieriVinogradov.Analytic.QuadraticRealZeroGap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A coarse uniform effective exceptional gap

The effective quadratic real-zero estimate implies `1/Q ≤ 1-beta`
uniformly over all conductors at most `Q`, once `Q` is sufficiently large.
This is used only to absorb polynomially small truncation errors.
-/

namespace Linnik

open Filter BoundedGaps.Maynard
open scoped Topology

theorem eventually_quadratic_gap_denominator_le :
    ∀ᶠ Q : ℕ in atTop,
      (2 ^ 22 : ℝ) * Real.sqrt (Q : ℝ) * Real.log (Q : ℝ) ^ 4 ≤ Q := by
  have hlim := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall : ∀ᶠ Q : ℕ in atTop,
      Real.log (Q : ℝ) ^ 4 / Real.sqrt (Q : ℝ) < 1 / (2 ^ 22 : ℝ) := by
    have h := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2 ^ 22))
    simpa only [Function.comp_apply, Real.rpow_ofNat, Real.sqrt_eq_rpow] using h
  filter_upwards [hsmall, eventually_ge_atTop 1] with Q hsmall hQ
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hsqrt : 0 < Real.sqrt (Q : ℝ) := Real.sqrt_pos.mpr hQpos
  have h := (div_lt_iff₀ hsqrt).mp hsmall
  have hsquare := Real.sq_sqrt hQpos.le
  have hmul := mul_le_mul_of_nonneg_left h.le hsqrt.le
  nlinarith

theorem eventually_uniform_quadratic_real_zero_gap :
    ∀ᶠ Q : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q], 1 < q → q ≤ Q →
        ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 → chi ^ 2 = 1 →
          ∀ beta : ℝ, beta ≤ 1 → DirichletCharacter.LFunction chi (beta : ℂ) = 0 →
            1 / (Q : ℝ) ≤ 1 - beta := by
  filter_upwards [eventually_quadratic_gap_denominator_le, eventually_ge_atTop 2]
    with Q hden hQ
  intro q _ hq hqQ chi hchi hsquare beta hbeta hzero
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqpos : (0 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hlog : Real.log (q : ℝ) ≤ Real.log (Q : ℝ) := Real.log_le_log hqpos hqQR
  have hdenq : (2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ^ 4 ≤ Q := by
    apply le_trans _ hden
    gcongr
  apply le_trans _ (effectiveQuadraticRealZeroGap hq chi hchi hsquare hbeta hzero)
  exact one_div_le_one_div_of_le (by positivity) hdenq

end Linnik
