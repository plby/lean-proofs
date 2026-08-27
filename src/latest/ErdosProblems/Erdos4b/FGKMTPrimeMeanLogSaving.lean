/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedPrimeMeanDecay

/-! # Arbitrary log-log savings for the actual prime-mean error envelope -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_primeMeanErrorEnvelope_le_quarterPower {d : ℝ} (hd : 0 < d) :
    ∀ᶠ x : ℕ in atTop,
      primeMeanErrorEnvelope d x ≤ 2 * Real.log (x : ℝ) ^ (-1 / 4 : ℝ) := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_log_pow_le_exp_mul_sqrtLog 1 hd,
    hlogTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hL
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hexp : Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) ≤ 1 / Real.log (x : ℝ) := by
    simpa only [pow_one, neg_mul] using exp_neg_le_inv_of_le_exp hLpos (by simpa using hx)
  have hinv : 1 / Real.log (x : ℝ) ≤ Real.log (x : ℝ) ^ (-1 / 4 : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  dsimp only [primeMeanErrorEnvelope]
  linarith

theorem eventually_primeMeanErrorEnvelope_loglog_saving (J : ℕ) {d e : ℝ}
    (hd : 0 < d) (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop,
      primeMeanErrorEnvelope d x ≤ e / Real.log (Real.log (x : ℝ)) ^ J := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (J : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 4)).comp_tendsto hlogTop).def (by positivity : 0 < e / 2)
  filter_upwards [eventually_primeMeanErrorEnvelope_le_quarterPower hd, hsmall,
    hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp hlogTop).eventually (eventually_ge_atTop (1 : ℝ))] with
      x hx hsmall hL hlogL
  let L := Real.log (x : ℝ)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hlogLpos : 0 < Real.log L := by change 1 ≤ Real.log L at hlogL; linarith
  have hp : 0 < Real.log L ^ J := pow_pos hlogLpos J
  have hsmall' : Real.log L ^ J ≤ e / 2 * L ^ (1 / 4 : ℝ) := by
    change ‖Real.log L ^ (J : ℝ)‖ ≤ e / 2 * ‖L ^ (1 / 4 : ℝ)‖ at hsmall
    simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_of_pos hp,
      abs_of_pos (Real.rpow_pos_of_pos hLpos (1 / 4))] using hsmall
  have hpower : 2 * L ^ (-1 / 4 : ℝ) ≤ e / Real.log L ^ J := by
    apply (le_div_iff₀ hp).mpr
    have heq : L ^ (-1 / 4 : ℝ) = (L ^ (1 / 4 : ℝ))⁻¹ := by
      rw [show (-1 / 4 : ℝ) = -(1 / 4) by ring, Real.rpow_neg hLpos.le]
    rw [heq]
    have hprod := mul_le_mul_of_nonneg_left hsmall' (by positivity : 0 ≤ 2 / L ^ (1 / 4 : ℝ))
    have hcancel : (2 / L ^ (1 / 4 : ℝ)) * (e / 2 * L ^ (1 / 4 : ℝ)) = e := by
      field_simp
    rw [hcancel] at hprod
    simpa only [div_eq_mul_inv, mul_assoc] using hprod
  exact hx.trans hpower

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_primeMeanErrorEnvelope_le_quarterPower
#print axioms Erdos4b.FGKMT.eventually_primeMeanErrorEnvelope_loglog_saving
