/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfiszScale

/-!
# Exponential absorption for the effective complete-zero envelope

Only scalar inequalities from the existing height analysis are reused.
There is no invocation of Siegel--Walfisz or any ineffective Siegel gap.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

theorem eventually_log_le_exp_mul_sqrtLog {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≤
      Real.exp (c * Real.sqrt (Real.log (x : ℝ))) := by
  have hL : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu := Real.tendsto_sqrt_atTop.comp hL
  have hdom := ((isLittleO_pow_exp_pos_mul_atTop 2 hc).comp_tendsto hu).eventuallyLE
  filter_upwards [hdom, hL.eventually (eventually_ge_atTop (0 : ℝ))] with x hx hlog
  simp only [Function.comp_apply, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (sq_nonneg (Real.sqrt (Real.log (x : ℝ)))),
    abs_of_pos (Real.exp_pos _)] at hx
  simpa only [Real.sq_sqrt hlog] using hx

theorem smallConductorZeroEnvelope_le (N A : ℕ) (hA : 2 ≤ A)
    {x q Q : ℕ} [NeZero q] (hQ : 2 ≤ Q) (hqQ : q ≤ Q)
    (hlog : 1 ≤ Real.log (x : ℝ))
    (hQheight : (Q : ℝ) ^ 2 ≤ siegelWalfiszHeight x)
    (hsquare : 16 * Real.sqrt (Real.log (x : ℝ)) ^ 2 ≤
      Real.exp (Real.sqrt (Real.log (x : ℝ)) / (8 * (A : ℝ) ^ 2)))
    (hlogAbsorb : Real.log (x : ℝ) ≤
      Real.exp ((1 / (16 * (A : ℝ) ^ 2)) * Real.sqrt (Real.log (x : ℝ)))) :
    32 * (N : ℝ) * (x : ℝ) ^ (1 - 1 / ((A : ℝ) ^ 2 *
        Real.log ((Q : ℝ) ^ 2 * (siegelWalfiszHeight x + 2)))) *
      Real.log (x : ℝ) * Real.log ((q : ℝ) * (siegelWalfiszHeight x + 2)) ^ 2 ≤
      96 * (N : ℝ) * ((x : ℝ) * Real.exp
        (-(1 / (16 * (A : ℝ) ^ 2)) * Real.sqrt (Real.log (x : ℝ)))) := by
  let : NeZero (Q ^ 2) := ⟨by positivity⟩
  have hqQsq : q ≤ Q ^ 2 := hqQ.trans (by nlinarith)
  have hqQsq' : (q : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast hqQsq
  have hqheight := hqQsq'.trans hQheight
  have hqlog := (log_modulus_mul_siegelWalfiszHeight_add_two_bounds hlog hqheight).1
  have hheightpos : 0 < siegelWalfiszHeight x + 2 := by
    unfold siegelWalfiszHeight
    positivity
  have hlogle : Real.log ((q : ℝ) * (siegelWalfiszHeight x + 2)) ≤
      Real.log ((Q : ℝ) ^ 2 * (siegelWalfiszHeight x + 2)) := by
    apply Real.log_le_log (mul_pos (by exact_mod_cast NeZero.pos q) hheightpos)
    exact mul_le_mul_of_nonneg_right hqQsq' hheightpos.le
  have hlogsq := pow_le_pow_left₀ hqlog.le hlogle 2
  have hbase := dirichletNonexceptionalSiegelWalfiszEnvelope_le N A hA
    (q := Q ^ 2) hlog (by simpa only [Nat.cast_pow] using hQheight) hsquare
  simp only [Nat.cast_pow] at hbase
  let u : ℝ := Real.sqrt (Real.log (x : ℝ))
  let P : ℝ := (x : ℝ) ^ (1 - 1 / ((A : ℝ) ^ 2 *
    Real.log ((Q : ℝ) ^ 2 * (siegelWalfiszHeight x + 2))))
  let V : ℝ := Real.log ((Q : ℝ) ^ 2 * (siegelWalfiszHeight x + 2))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hL : 0 ≤ Real.log (x : ℝ) := zero_le_one.trans hlog
  calc
    _ = (32 * (N : ℝ) * P *
        Real.log ((q : ℝ) * (siegelWalfiszHeight x + 2)) ^ 2) * Real.log (x : ℝ) := by
      dsimp [P]
      ring
    _ ≤ (96 * (N : ℝ) * P * V ^ 2) * Real.log (x : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hL
      apply mul_le_mul _ hlogsq (sq_nonneg _) (by positivity)
      gcongr
      norm_num
    _ ≤ (96 * (N : ℝ) * ((x : ℝ) * Real.exp (-(1 / (8 * (A : ℝ) ^ 2)) * u))) *
        Real.log (x : ℝ) := mul_le_mul_of_nonneg_right hbase hL
    _ ≤ (96 * (N : ℝ) * ((x : ℝ) * Real.exp (-(1 / (8 * (A : ℝ) ^ 2)) * u))) *
        Real.exp ((1 / (16 * (A : ℝ) ^ 2)) * u) :=
      mul_le_mul_of_nonneg_left hlogAbsorb (by positivity)
    _ = 96 * (N : ℝ) * ((x : ℝ) *
        (Real.exp (-(1 / (8 * (A : ℝ) ^ 2)) * u) *
          Real.exp ((1 / (16 * (A : ℝ) ^ 2)) * u))) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 3
      ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_log_le_exp_mul_sqrtLog
#print axioms Erdos4b.FGKMT.smallConductorZeroEnvelope_le
