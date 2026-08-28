import Wikipedia.NoExoticSixSphere.StereographicAugmentedDifferential
import Wikipedia.NoExoticSixSphere.SphereLevelEquationsRadialZero
import Wikipedia.NoExoticSixSphere.SphereSuspensionEquationDerivative

/-!
# The full radial equation derivative in actual compactification coordinates

The augmented inverse stereographic differential separates the original
Euclidean directions from the new radial direction. The norm equation
has derivative twice the radial coordinate, and the radial extension
annihilates that direction. All derivatives are those of the actual maps.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.StereographicEquator

theorem norm_finiteAmbient (n : ℕ) (x : V n) : ‖finiteAmbient n x‖ = 1 := by
  exact ClosedHemisphere.unit_norm (euclideanOnePointSphere n (x : OnePoint (V n)))

theorem fderiv_normEquation_augmented (n : ℕ) (x w : V n) (t : ℝ) :
    fderiv ℝ (fun y : V (n + 1) ↦ ‖y‖ ^ 2 - 1) (finiteAmbient n x)
      (augmentedEquiv n x (w, t)) = 2 * t := by
  rw [((hasStrictFDerivAt_norm_sq (finiteAmbient n x)).hasFDerivAt.sub_const 1).fderiv,
    augmentedEquiv_apply]
  simp only [two_smul, add_apply, innerSL_apply_apply]
  rw [inner_add_right, inner_finiteAmbient_fderiv, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  simp only [norm_finiteAmbient, one_pow, mul_one, zero_add]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

local instance : Fact (Module.finrank ℝ (V (n + 1)) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem fderiv_equations_augmented (a : Sphere n) (g : Sphere n → F) (x : V n)
    (hg : ContMDiffAt (𝓡 n) 𝓘(ℝ, F) ∞ g
      (euclideanOnePointSphere n (x : OnePoint (V n))))
    (D : V n →L[ℝ] F)
    (hD : (fderiv ℝ (SphereLevelEquations.extend a g) (finiteAmbient n x)).comp
      (fderiv ℝ (finiteAmbient n) x) = D) (w : V n) (t : ℝ) :
    fderiv ℝ (SphereLevelEquations.equations a g) (finiteAmbient n x)
      (augmentedEquiv n x (w, t)) = WithLp.toLp 2 (2 * t, D w) := by
  have he := SphereLevelEquations.fderiv_equations_radial_components a g
    (euclideanOnePointSphere n (x : OnePoint (V n))) hg (augmentedEquiv n x (w, t))
  change fderiv ℝ (SphereLevelEquations.equations a g) (finiteAmbient n x)
    (augmentedEquiv n x (w, t)) = _ at he
  rw [he]
  change WithLp.toLp 2
    (fderiv ℝ (fun y : V (n + 1) ↦ ‖y‖ ^ 2 - 1) (finiteAmbient n x)
      (augmentedEquiv n x (w, t)),
      fderiv ℝ (SphereLevelEquations.extend a g) (finiteAmbient n x)
        (augmentedEquiv n x (w, t))) = _
  rw [fderiv_normEquation_augmented]
  congr 1
  apply Prod.ext
  · rfl
  rw [augmentedEquiv_apply, map_add, map_smul]
  have hz : fderiv ℝ (SphereLevelEquations.extend a g) (finiteAmbient n x)
      (finiteAmbient n x) = 0 :=
    SphereLevelEquations.fderiv_extend_radial_zero (m := n) a g
      (euclideanOnePointSphere n (x : OnePoint (V n))) hg
  rw [hz, smul_zero, add_zero]
  exact congrArg (fun L : V n →L[ℝ] F ↦ L w) hD

end NoExoticSixSphere.StereographicEquator
