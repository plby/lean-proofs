import Wikipedia.HopfProblem.RiemannSphereMobiusInverse
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Nonvanishing derivative of the actual corner-normalizing cross-ratio

The strict derivative is calculated from the rational formula.  For three
distinct normalization points it is nonzero away from the pole.  Thus
postcomposing an analytic corner germ with this cross-ratio preserves its
vanishing order relative to its value at the corner.
-/

noncomputable section

open Complex

namespace Wikipedia.HopfProblem.RiemannSphere.MobiusCircle

/-- The strict derivative of the cross-ratio, calculated from its rational formula. -/
theorem crossRatio_hasStrictDerivAt {a b c z : ℂ} (hzc : z ≠ c) :
    HasStrictDerivAt (crossRatio a b c)
      (coefficient a b c * (a - c) / (z - c) ^ 2) z := by
  have hn : HasStrictDerivAt (fun w : ℂ => w - a) 1 z :=
    (hasStrictDerivAt_id z).sub_const a
  have hd : HasStrictDerivAt (fun w : ℂ => w - c) 1 z :=
    (hasStrictDerivAt_id z).sub_const c
  have hq := HasStrictDerivAt.div hn hd (sub_ne_zero.mpr hzc)
  have h := HasStrictDerivAt.const_mul (coefficient a b c) hq
  have hf : crossRatio a b c = fun w => coefficient a b c * ((w - a) / (w - c)) :=
    funext (crossRatio_eq_coefficient a b c)
  have he : coefficient a b c * (a - c) / (z - c) ^ 2 =
      coefficient a b c * ((1 * (z - c) - (z - a) * 1) / (z - c) ^ 2) := by ring
  rw [hf, he]
  exact h

theorem crossRatio_hasDerivAt {a b c z : ℂ} (hzc : z ≠ c) :
    HasDerivAt (crossRatio a b c)
      (coefficient a b c * (a - c) / (z - c) ^ 2) z :=
  (crossRatio_hasStrictDerivAt hzc).hasDerivAt

theorem crossRatio_deriv {a b c z : ℂ} (hzc : z ≠ c) :
    deriv (crossRatio a b c) z = coefficient a b c * (a - c) / (z - c) ^ 2 :=
  (crossRatio_hasDerivAt hzc).deriv

/-- The explicit derivative coefficient cannot vanish for a distinct triple off the pole. -/
theorem crossRatio_derivCoefficient_ne_zero {a b c z : ℂ}
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hzc : z ≠ c) :
    coefficient a b c * (a - c) / (z - c) ^ 2 ≠ 0 :=
  div_ne_zero (mul_ne_zero (coefficient_ne_zero hba hbc) (sub_ne_zero.mpr hac))
    (pow_ne_zero 2 (sub_ne_zero.mpr hzc))

theorem crossRatio_deriv_ne_zero {a b c z : ℂ}
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hzc : z ≠ c) :
    deriv (crossRatio a b c) z ≠ 0 := by
  rw [crossRatio_deriv hzc]
  exact crossRatio_derivCoefficient_ne_zero hba hbc hac hzc

/-- Relative to its value at a nonpole, the cross-ratio has analytic order one. -/
theorem crossRatio_analyticOrderAt_sub {a b c z : ℂ}
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hzc : z ≠ c) :
    analyticOrderAt (fun w => crossRatio a b c w - crossRatio a b c z) z = 1 :=
  (crossRatio_analyticAt hba hzc).analyticOrderAt_sub_eq_one_of_deriv_ne_zero
    (crossRatio_deriv_ne_zero hba hbc hac hzc)

/-- Postcomposition with the actual cross-ratio preserves a corner germ's vanishing order. -/
theorem crossRatio_comp_analyticOrderAt {a b c x : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f x) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    (hfc : f x ≠ c) :
    analyticOrderAt (fun w => crossRatio a b c (f w) - crossRatio a b c (f x)) x =
      analyticOrderAt (fun w => f w - f x) x := by
  have ha : AnalyticAt ℂ (fun w => crossRatio a b c w - crossRatio a b c (f x)) (f x) :=
    (crossRatio_analyticAt hba hfc).sub analyticAt_const
  have hcomp := ha.analyticOrderAt_comp (g := f) (z₀ := x) hf
  rw [crossRatio_analyticOrderAt_sub hba hbc hac hfc, one_mul] at hcomp
  exact hcomp

end Wikipedia.HopfProblem.RiemannSphere.MobiusCircle
