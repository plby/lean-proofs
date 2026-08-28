import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.Basic

/-!
# Multipliers under a ramified analytic semiconjugacy

If a germ of order `k` intertwines two fixed-point germs, the target
multiplier is the `k`th power of the source multiplier.  The proof factors
the first nonzero analytic term and uses the continuous divided differences
of the two actions.  The actions themselves need only be differentiable.
-/

noncomputable section

open Function Set Filter Topology

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The multiplier identity for an actual analytic semiconjugacy germ.
No nonzero-multiplier or local-injectivity assumptions on the actions are
needed.  The finite order hypothesis, together with `τ a = b`, already
forces the order to be positive. -/
theorem analytic_semiconjugacy_multiplier
    (τ A B : ℂ → ℂ) (a b ξ η : ℂ) (k : ℕ)
    (hτ : AnalyticAt ℂ τ a) (hτa : τ a = b)
    (horder : analyticOrderAt (fun z => τ z - b) a = (k : ℕ∞))
    (hA : HasDerivAt A ξ a) (hAa : A a = a)
    (hB : HasDerivAt B η b) (hBb : B b = b)
    (hsem : τ ∘ A =ᶠ[𝓝 a] B ∘ τ) : η = ξ ^ k := by
  obtain ⟨u, hu, hu0, hfactor⟩ :=
    (hτ.sub analyticAt_const).analyticOrderAt_eq_natCast.mp horder
  have hf : ∀ᶠ z in 𝓝 a, τ z - b = (z - a) ^ k * u z := by
    simpa only [Pi.sub_apply, smul_eq_mul] using hfactor
  have hAt : Tendsto A (𝓝 a) (𝓝 a) := by
    simpa only [ContinuousAt, hAa] using hA.continuousAt
  have hfA : ∀ᶠ z in 𝓝 a, τ (A z) - b = (A z - a) ^ k * u (A z) :=
    hAt.eventually hf
  have he : (fun z => dslope A a z ^ k * u (A z)) =ᶠ[𝓝[≠] a]
      (fun z => u z * dslope B b (τ z)) := by
    filter_upwards [hf.filter_mono nhdsWithin_le_nhds, hfA.filter_mono nhdsWithin_le_nhds,
      hsem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hfz hfAz hsemz hza
    have hAz : A z - a = (z - a) * dslope A a z := by
      simpa only [smul_eq_mul, hAa] using (sub_smul_dslope A a z).symm
    have hBz : B (τ z) - b = (τ z - b) * dslope B b (τ z) := by
      simpa only [smul_eq_mul, hBb] using (sub_smul_dslope B b (τ z)).symm
    apply mul_left_cancel₀ (pow_ne_zero k (sub_ne_zero.mpr hza))
    calc
      (z - a) ^ k * (dslope A a z ^ k * u (A z)) =
          ((z - a) * dslope A a z) ^ k * u (A z) := by rw [mul_pow, mul_assoc]
      _ = (A z - a) ^ k * u (A z) := by rw [← hAz]
      _ = τ (A z) - b := hfAz.symm
      _ = B (τ z) - b := congrArg (fun w => w - b) hsemz
      _ = (τ z - b) * dslope B b (τ z) := hBz
      _ = (z - a) ^ k * (u z * dslope B b (τ z)) := by rw [hfz, mul_assoc]
  have hcL : ContinuousAt (fun z => dslope A a z ^ k * u (A z)) a :=
    ((continuousAt_dslope_same.mpr hA.differentiableAt).pow k).mul
      (hu.continuousAt.comp_of_eq hA.continuousAt hAa)
  have hcR : ContinuousAt (fun z => u z * dslope B b (τ z)) a :=
    hu.continuousAt.mul
      ((continuousAt_dslope_same.mpr hB.differentiableAt).comp_of_eq hτ.continuousAt hτa)
  have hcenter := tendsto_nhds_unique_of_eventuallyEq
    hcL.continuousWithinAt hcR.continuousWithinAt he
  have hcoeff : ξ ^ k * u a = u a * η := by
    simpa only [hAa, hτa, dslope_same, hA.deriv, hB.deriv] using hcenter
  apply mul_right_cancel₀ hu0
  rw [mul_comm η (u a)]
  exact hcoeff.symm

/-- Derivative-only form for analytic fixed-point germs. -/
theorem analytic_semiconjugacy_deriv_pow
    (τ A B : ℂ → ℂ) (a b : ℂ) (k : ℕ)
    (hτ : AnalyticAt ℂ τ a) (hτa : τ a = b)
    (horder : analyticOrderAt (fun z => τ z - b) a = (k : ℕ∞))
    (hA : AnalyticAt ℂ A a) (hAa : A a = a)
    (hB : AnalyticAt ℂ B b) (hBb : B b = b)
    (hsem : τ ∘ A =ᶠ[𝓝 a] B ∘ τ) : deriv B b = deriv A a ^ k :=
  analytic_semiconjugacy_multiplier τ A B a b (deriv A a) (deriv B b) k
    hτ hτa horder hA.differentiableAt.hasDerivAt hAa
    hB.differentiableAt.hasDerivAt hBb hsem

end Wikipedia.HopfProblem.SpecialPeriods
