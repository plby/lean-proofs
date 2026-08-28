import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry

/-!
# The actual sphere coordinate on the regular base

Restrict the constructed normalized sphere uniformization to the two
literal three-puncture complements. Both sides retain their existing
open-submanifold atlases, and the inverse is the restriction of the
original inverse uniformization.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace

/-- The original inverse uniformization maps exactly the regular
sphere patch to the actual regular compact-base patch. -/
@[simp] theorem sphereUniformization_symm_mem_regular_iff (b : RiemannSphere) :
    triangleSphereUniformization.symm b ∈ regularPatch ↔ b ∈ sphereRegularPatch := by
  simpa only [Diffeomorph.apply_symm_apply] using
    (sphereUniformization_mem_regular_iff (triangleSphereUniformization.symm b)).symm

/-- The genuine normalized sphere uniformization on the actual regular
patches, with both inherited complex structures unchanged. -/
def regularSphereBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) regularPatch sphereRegularPatch ω where
  toFun q := ⟨triangleSphereUniformization q.val,
    (sphereUniformization_mem_regular_iff q.val).mpr q.property⟩
  invFun b := ⟨triangleSphereUniformization.symm b.val,
    (sphereUniformization_symm_mem_regular_iff b.val).mpr b.property⟩
  left_inv q := Subtype.ext (triangleSphereUniformization.symm_apply_apply q.val)
  right_inv b := Subtype.ext (triangleSphereUniformization.apply_symm_apply b.val)
  contMDiff_toFun := by
    exact (isLocalDiffeomorph_restrictOpens 𝓘(ℂ) 𝓘(ℂ)
      triangleSphereUniformization.isLocalDiffeomorph regularPatch sphereRegularPatch
      (fun q hq => (sphereUniformization_mem_regular_iff q).mpr hq)).contMDiff
  contMDiff_invFun := by
    exact (isLocalDiffeomorph_restrictOpens 𝓘(ℂ) 𝓘(ℂ)
      triangleSphereUniformization.symm.isLocalDiffeomorph sphereRegularPatch regularPatch
      (fun b hb => (sphereUniformization_symm_mem_regular_iff b).mpr hb)).contMDiff

@[simp] theorem regularSphereBiholomorph_val (q : regularPatch) :
    (regularSphereBiholomorph q : RiemannSphere) =
      triangleSphereUniformization q.val := rfl

@[simp] theorem regularSphereBiholomorph_symm_val (b : sphereRegularPatch) :
    (regularSphereBiholomorph.symm b : TriangleCompactifiedOrbitSpace) =
      triangleSphereUniformization.symm b.val := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
