import Wikipedia.NoExoticSixSphere.WeightedAffineCompositeDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# A nonnegative cutoff preserves the derivative on its zero set

A zero of a nonnegative smooth cutoff is a local minimum, so its derivative
vanishes there, including at boundary points of the zero set. The actual
weighted affine derivative formula then agrees with the zero-parameter jet.
-/

noncomputable section

namespace NoExoticSixSphere.WeightedAffineComposite

open AffinePerturbation

variable {X V E W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_composite_eq_zero_parameter_of_zero_cutoff
    (g : X → E) (i : X → V) (r : E → W) (a : X → ℝ)
    (p : Parameters V E) (x : X) (hg : DifferentiableAt ℝ g x)
    (hi : DifferentiableAt ℝ i x) (ha : DifferentiableAt ℝ a x)
    (hr : DifferentiableAt ℝ r (ambient g i a p x))
    (hn : ∀ z, 0 ≤ a z) (hx : a x = 0) :
    fderiv ℝ (composite g i r a p) x = fderiv ℝ (composite g i r a 0) x := by
  have hmin : IsLocalMin a x := Filter.Eventually.of_forall fun z ↦ by
    rw [hx]
    exact hn z
  have hd : fderiv ℝ a x = 0 := hmin.fderiv_eq_zero
  have hp : ambient g i a p x = g x := by simp only [ambient, hx, zero_smul, add_zero]
  have h0 : ambient g i a 0 x = g x := by simp only [ambient, hx, zero_smul, add_zero]
  have hr0 : DifferentiableAt ℝ r (ambient g i a 0 x) := (h0.trans hp.symm) ▸ hr
  rw [fderiv_composite g i r a p x hg hi ha hr,
    fderiv_composite g i r a 0 x hg hi ha hr0, hp, h0, hx, hd]
  simp

end NoExoticSixSphere.WeightedAffineComposite
