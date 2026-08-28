import Wikipedia.HopfProblem.SmoothMorseLemmaSymmetricTaylor
import Wikipedia.HopfProblem.SmoothMorseLemmaQuadraticChart
import Wikipedia.HopfProblem.SmoothMorseLemmaCongruence

/-!
# The smooth Morse lemma at the origin

The only hypotheses are smoothness, vanishing of the actual derivative,
and nondegeneracy of the actual Hessian. The integral Taylor factor and
its smooth congruence factor are constructed by the preceding proofs.
The resulting chart is a native `C∞` partial diffeomorphism for the
original function, and its derivative at the center is the identity.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual nondegenerate Hessian, with its genuine continuous linear inverse. -/
def hessianEquiv (f : E → ℝ) (a : E)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (fderiv ℝ (fderiv ℝ f) a).toLinearMap hn).toContinuousLinearEquiv

@[simp] theorem hessianEquiv_apply (f : E → ℝ) (a : E)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) (u v : E) :
    hessianEquiv f a hn u v = fderiv ℝ (fderiv ℝ f) a u v := rfl

@[simp] theorem hessianEquiv_toContinuousLinearMap (f : E → ℝ) (a : E)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    (hessianEquiv f a hn).toContinuousLinearMap = fderiv ℝ (fderiv ℝ f) a := by
  ext u v
  rfl

/-- The genuine smooth Morse lemma at zero, in the exact original Hessian
quadratic form. No local normal form or inverse is supplied as a hypothesis. -/
theorem exists_morse_chart_zero {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : fderiv ℝ f 0 = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ x ∈ e.source,
        f x = f 0 + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 (e x) (e x)) ∧
      (∀ y ∈ e.target,
        f (e.symm y) = f 0 + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 y y) := by
  let H := hessianEquiv f 0 hn
  have hH : ∀ u v, H u v = H v u := by
    intro u v
    have hs := (symmetricTaylorFactor f 0).property u v
    rw [symmetricTaylorFactor_zero hf] at hs
    exact hs
  obtain ⟨V, hV, hHV, L, hL, hL0, hcong⟩ := exists_smooth_congruence_factor H hH
  have hA0 : symmetricTaylorFactor f 0 = referenceSymmetricForm H hH := by
    apply Subtype.ext
    exact symmetricTaylorFactor_zero hf
  obtain ⟨e, he0, hezero, hederiv, hnormal, hinverse⟩ :=
    exists_quadratic_chart_of_smooth_congruence f (symmetricTaylorFactor f)
      (contDiff_symmetricTaylorFactor hf) (referenceSymmetricForm H hH) hA0
      (map_eq_add_symmetricTaylorFactor hf hc) V hV hHV L hL hL0 hcong
  exact ⟨e, he0, hezero, hederiv, hnormal, hinverse⟩

end Wikipedia.HopfProblem.SmoothMorseLemma
