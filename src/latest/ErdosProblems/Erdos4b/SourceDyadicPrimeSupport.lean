/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicArithmetic

/-!
# Prime support conditions for the dyadic global cover

The upper-half auxiliary range lies strictly beyond the initial sieve
frontier, and the smoothness frontier is eventually below that frontier.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

theorem one_lt_dyadicSmoothFrontier {r : ℕ} (hr : 0 < r) : 1 < smoothFrontier r := by
  unfold smoothFrontier
  apply one_lt_pow₀ (by norm_num)
  unfold smoothExponent
  exact (Nat.mul_pos hr (rankinDenominator_pos r)).ne'

theorem residualPrimeFrontier_le_primary (a r : ℕ) :
    residualPrimeFrontier a r ≤ primaryFrontier a r := by
  calc
    _ ≤ residualPrimeFrontier a r * 2 ^ r := Nat.le_mul_of_pos_right _ (by positivity)
    _ = _ := residualPrimeFrontier_mul_twoPow a r

theorem residualPrimeFrontier_lt_upperHalf {a r q : ℕ} (hr : 2 ≤ r)
    (hhalf : primaryFrontier a r ≤ 2 * q) : residualPrimeFrontier a r < q := by
  have hpow : 4 ≤ 2 ^ r := by
    simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using
      Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hr
  have hmul := Nat.mul_le_mul_left (residualPrimeFrontier a r) hpow
  rw [residualPrimeFrontier_mul_twoPow] at hmul
  have hz := residualPrimeFrontier_pos a r
  omega

theorem eventually_dyadicSmoothFrontier_le_residual (a : ℕ) :
    ∀ᶠ r in atTop, smoothFrontier r ≤ residualPrimeFrontier a r := by
  filter_upwards [eventually_dyadicCompanionScale_small a 1] with r hr
  have hV := one_le_dyadicAmbientScale a r
  have hzpos : (0 : ℝ) < residualPrimeFrontier a r :=
    by exact_mod_cast residualPrimeFrontier_pos a r
  have hypos : (0 : ℝ) < smoothFrontier r := by exact_mod_cast smoothFrontier_pos r
  have hzlog : dyadicAmbientScale a r / 2 ≤ Real.log (residualPrimeFrontier a r) :=
    (Real.le_log_iff_exp_le hzpos).mpr (exp_half_ambient_le_residualPrimeFrontier a r)
  have hlog : Real.log (smoothFrontier r) ≤ Real.log (residualPrimeFrontier a r) := by
    change dyadicCompanionScale r ≤ _
    simp only [Nat.cast_one, one_mul] at hr
    linarith
  exact_mod_cast (Real.log_le_log_iff hypos hzpos).mp hlog

end

end Erdos4b.SmoothParameters
