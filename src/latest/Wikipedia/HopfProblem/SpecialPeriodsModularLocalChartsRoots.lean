import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Analytic roots of units and local power coordinates

A nonzero analytic germ has a local analytic `m`th root for every positive
integer `m`.  We construct the root by choosing an ordinary complex root at
the center and applying the analytic inverse theorem to the power map there.
No global branch of the logarithm or of the root is assumed.

Combining this with the actual order-of-vanishing factorization produces an
analytic coordinate with nonzero derivative in which a finite-order zero is
exactly a power.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- A nonvanishing analytic germ has an analytic root near its center. -/
theorem exists_analytic_unit_root {g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0) (hm : 0 < m) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧ r a ≠ 0 ∧
      ∀ᶠ w in 𝓝 a, r w ^ m = g w := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (g a) hm
  have hb0 : b ≠ 0 := by
    intro h
    apply hga
    rw [← hb, h, zero_pow hm.ne']
  have hpow : AnalyticAt ℂ (fun w : ℂ => w ^ m) b := analyticAt_id.pow m
  have hderiv : deriv (fun w : ℂ => w ^ m) b ≠ 0 := by
    rw [deriv_pow_field]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') (pow_ne_zero _ hb0)
  let R : ℂ → ℂ := hpow.hasStrictDerivAt.localInverse (fun w : ℂ => w ^ m) _ b hderiv
  have hRa : AnalyticAt ℂ R (g a) := by
    rw [← hb]
    exact hpow.analyticAt_localInverse hderiv
  have hRb : R (g a) = b := by
    rw [← hb]
    exact HasStrictFDerivAt.localInverse_apply_image ..
  have hRpow : ∀ᶠ y in 𝓝 (g a), R y ^ m = y := by
    rw [← hb]
    exact hpow.hasStrictDerivAt.eventually_right_inverse hderiv
  refine ⟨fun w => R (g w), hRa.comp hg, ?_, ?_⟩
  · change R (g a) ≠ 0
    rw [hRb]
    exact hb0
  · exact hg.continuousAt.tendsto.eventually hRpow

/-- A zero of finite positive order admits an actual analytic power
coordinate germ, whose derivative at the center is nonzero. -/
theorem exists_analytic_power_coordinate {F : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = m) (hm : 0 < m) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ h a = 0 ∧ deriv h a ≠ 0 ∧
      ∀ᶠ w in 𝓝 a, F w = h w ^ m := by
  obtain ⟨g, hg, hga, hFg⟩ := hF.analyticOrderAt_eq_natCast.mp horder
  obtain ⟨r, hr, hra, hrpow⟩ := exists_analytic_unit_root hg hga hm
  let h : ℂ → ℂ := fun w => (w - a) * r w
  have hh : AnalyticAt ℂ h a := (analyticAt_id.sub analyticAt_const).mul hr
  have hderiv : deriv h a = r a := by
    simpa only [h, id_eq, sub_self, zero_mul, one_mul, add_zero] using
      (((hasDerivAt_id a).sub_const a).fun_mul hr.differentiableAt.hasDerivAt).deriv
  refine ⟨h, hh, by simp [h], hderiv ▸ hra, ?_⟩
  filter_upwards [hFg, hrpow] with w hw hwr
  rw [hw, smul_eq_mul, ← hwr, ← mul_pow]

end Wikipedia.HopfProblem.SpecialPeriods
