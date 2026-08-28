import Wikipedia.NoExoticSixSphere.QuaternionicHopfRadialTail

/-!
# The radial sphere-level equations have the computed south-fiber normal frame

The source radial extension is the one used by the sphere-fiber construction.
At the actual south fiber its augmented derivative agrees exactly with the
previously computed norm/tail derivative, including the radial component.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def radialSouthEquations (a : Sphere 7) : V 8 → SouthNormalModel :=
  SphereLevelEquations.equations a (fun y : Sphere 7 ↦ tailCoordinates (sphereMap y))

theorem contDiffAt_radialSouthEquations (a x : Sphere 7) :
    ContDiffAt ℝ ∞ (radialSouthEquations a) x.val := by
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact SphereLevelEquations.contDiffAt_equations a
    ((contMDiff_tailCoordinates.comp contMDiff_sphereMap) x)

theorem radialSouthEquations_derivative (a x : Sphere 7) (hx : first x.val = 0) :
    fderiv ℝ (radialSouthEquations a) x.val = fderiv ℝ southNormalEquations x.val := by
  have h₁ := (hasStrictFDerivAt_norm_sq x.val).hasFDerivAt.sub_const 1
  have h₂ := ((contDiffAt_radialTailExtension a x).differentiableAt (by simp)).hasFDerivAt
  rw [radialTailExtension_derivative a x hx] at h₂
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ).symm.hasFDerivAt.comp x.val
    (h₁.prodMk h₂)
  change HasFDerivAt (𝕜 := ℝ) (radialSouthEquations a) _ x.val at h
  apply ContinuousLinearMap.ext
  intro v
  rw [h.fderiv, southNormalEquations_fderiv x.val hx]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat]
  rw [polynomial_fderiv_south x.val hx, tailQuaternion_join]
  rfl

theorem radialSouthEquations_orthogonalRightInverse (a x : Sphere 7) (hx : first x.val = 0) :
    orthogonalRightInverse (fderiv ℝ (radialSouthEquations a) x.val) =
      southNormalLift (second x.val) := by
  rw [radialSouthEquations_derivative a x hx]
  exact southNormalEquations_orthogonalRightInverse x hx

end NoExoticSixSphere.QuaternionicHopf
