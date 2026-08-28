import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorRootSigns
import Mathlib.Analysis.Analytic.Order

/-!
# The forced second generator sign of the Eisenstein square root

The actual order-four source generator has derivative `-I` at its fixed
point. Covariance sends this fixed point to `I`, so the weight-three factor
also has value `-I`. A holomorphic root with a simple zero cannot transform
with the opposite sign: differentiating would give opposite nonzero first
derivatives. This local calculation selects the positive global sign.
-/

noncomputable section

open UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The opposite order-four transformation sign is incompatible with a
simple zero at the actual order-four fixed point. -/
theorem holomorphic_simple_zero_not_generatorTwo_negative
    {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (horder : analyticOrderAt (r ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ¬ (∀ z, r (Triangle.generatorTwoSL • z) = -(τ z : ℂ) ^ 3 * r z) := by
  intro hneg
  let R : ℂ → ℂ := r ∘ ofComplex
  let T : ℂ → ℂ := fun z => (τ (ofComplex z) : ℂ)
  let B : ℂ → ℂ := fun z => ((Triangle.generatorTwoSL • ofComplex z : ℍ) : ℂ)
  let c : ℂ := (Triangle.centerTwo : ℂ)
  have hRA : AnalyticAt ℂ R c :=
    (UpperHalfPlane.contMDiffAt_iff.mp (hr Triangle.centerTwo)).analyticAt
  have hTA : AnalyticAt ℂ T c :=
    (UpperHalfPlane.contMDiffAt_iff.mp
      ((UpperHalfPlane.contMDiff_coe.comp hτ) Triangle.centerTwo)).analyticAt
  have hRorder : analyticOrderAt R c = 1 := horder
  have hRzero : R c = 0 :=
    apply_eq_zero_of_analyticOrderAt_ne_zero (by rw [hRorder]; exact one_ne_zero)
  have hdOrder : analyticOrderAt (deriv R) c = 0 :=
    analyticOrderAt_deriv_of_pos hRA (n := 0) (by simpa using hRorder)
  have hd : deriv R c ≠ 0 := hRA.deriv.analyticOrderAt_eq_zero.mp hdOrder
  have hBc : B c = c := by
    dsimp only [B, c]
    rw [ofComplex_apply, Triangle.generatorTwo_fix]
  have hTc : T c = Complex.I := by
    dsimp only [T, c]
    rw [ofComplex_apply, (tau_covariant_values hτc).2]
    rfl
  have hB : HasDerivAt B (-Complex.I) c :=
    Triangle.generatorTwo_hasStrictDerivAt.hasDerivAt
  have hRder : HasDerivAt R (deriv R c) (B c) := by
    rw [hBc]
    exact hRA.differentiableAt.hasDerivAt
  have hleft : HasDerivAt
      (fun z : ℂ => r (Triangle.generatorTwoSL • ofComplex z))
      (deriv R c * -Complex.I) c := by
    simpa only [Function.comp_def, R, B, ofComplex_apply] using hRder.comp c hB
  have hright : HasDerivAt (fun z : ℂ => -(T z) ^ 3 * R z) _ c :=
    ((hTA.differentiableAt.hasDerivAt.pow 3).neg).mul hRA.differentiableAt.hasDerivAt
  have hright' : HasDerivAt (fun z : ℂ => -(T z) ^ 3 * R z)
      (Complex.I * deriv R c) c := by
    simpa [hRzero, hTc, Complex.I_sq, pow_succ] using hright
  have hfun : (fun z : ℂ => r (Triangle.generatorTwoSL • ofComplex z)) =
      (fun z : ℂ => -(T z) ^ 3 * R z) := by
    funext z
    exact hneg (ofComplex z)
  rw [hfun] at hleft
  have heq := hleft.unique hright'
  have hI : -Complex.I = Complex.I := by
    apply mul_right_cancel₀ hd
    simpa only [mul_comm] using heq
  have him := congrArg Complex.im hI
  norm_num at him

/-- A holomorphic square root of the actual `E₆` pullback whose zero at
the second center is simple has the positive order-four generator sign. -/
theorem eisensteinSix_root_generatorTwo {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z))
    (horder : analyticOrderAt (r ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ∀ z, r (Triangle.generatorTwoSL • z) = (τ z : ℂ) ^ 3 * r z := by
  rcases eisensteinSix_root_generatorTwo_dichotomy hτ hτc hr hrsq with hpos | hneg
  · exact hpos
  · exact (holomorphic_simple_zero_not_generatorTwo_negative hτ hτc hr horder hneg).elim

end Wikipedia.HopfProblem.SpecialPeriods
