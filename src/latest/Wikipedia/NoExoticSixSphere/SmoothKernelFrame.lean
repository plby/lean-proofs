import Wikipedia.NoExoticSixSphere.CanonicalRightInverse
import Wikipedia.NoExoticSixSphere.SmoothFrameCoordinates

/-!
# Smooth frames of orthogonal kernel complements

The orthogonal right inverse varies smoothly on the surjective locus.
It supplies a genuine smooth range frame for the orthogonal complements
of the kernels, and the defining differential sends that frame to the
identity.
-/

open scoped Manifold ContDiff
open Function

namespace NoExoticSixSphere

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_orthogonalRightInverse {D : M → E →L[ℝ] F} {x : M}
    (hD : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ D x) (hsurj : Surjective (D x)) :
    ContMDiffAt I 𝓘(ℝ, F →L[ℝ] E) ∞ (fun y ↦ orthogonalRightInverse (D y)) x := by
  have hadj : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] E) ∞ (fun y ↦ (D y).adjoint) x :=
    realAdjoint.contDiff.contMDiff.contMDiffAt.comp x hD
  have hgram : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞
      (fun y ↦ gramOperator (D y).adjoint) x := by
    simpa only [gramOperator, ContinuousLinearMap.adjoint_adjoint] using hD.clm_comp hadj
  have hinv : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞
      (fun y ↦ (gramOperator (D y).adjoint).inverse) x :=
    ContDiffAt.comp_contMDiffAt (f := fun y ↦ gramOperator (D y).adjoint) (x := x)
      (gramOperator_isInvertible (D x).adjoint
        (adjoint_injective_of_surjective (D x) hsurj)).contDiffAt_map_inverse hgram
  exact hadj.clm_comp hinv

noncomputable def orthogonalKernelFrame (D : M → E →L[ℝ] F)
    (hD : ContMDiff I 𝓘(ℝ, E →L[ℝ] F) ∞ D) (hsurj : ∀ x, Surjective (D x)) :
    SmoothRangeFrame I (fun x ↦ (D x).kerᗮ.starProjection) F := by
  let R := fun x ↦ orthogonalRightInverse (D x)
  have hrange (x : M) : (R x).range = ((D x).kerᗮ.starProjection).range := by
    rw [Submodule.range_starProjection]
    exact range_orthogonalRightInverse (D x) (hsurj x)
  let e (x : M) : F ≃L[ℝ] ((D x).kerᗮ.starProjection).range :=
    (LinearEquiv.ofInjective (R x).toLinearMap
      (orthogonalRightInverse_injective (D x) (hsurj x))).toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.ofEq _ _ (hrange x))
  refine ⟨e, ?_⟩
  have heq : (fun x ↦ ((D x).kerᗮ.starProjection).range.subtypeL.comp
      (e x).toContinuousLinearMap) = R := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [heq]
  exact fun x ↦ contMDiffAt_orthogonalRightInverse (hD x) (hsurj x)

theorem orthogonalKernelFrame_ambient (D : M → E →L[ℝ] F)
    (hD : ContMDiff I 𝓘(ℝ, E →L[ℝ] F) ∞ D) (hsurj : ∀ x, Surjective (D x)) (x : M) :
    (orthogonalKernelFrame D hD hsurj).ambient x = orthogonalRightInverse (D x) := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem orthogonalKernelFrame_comp (D : M → E →L[ℝ] F)
    (hD : ContMDiff I 𝓘(ℝ, E →L[ℝ] F) ∞ D) (hsurj : ∀ x, Surjective (D x)) (x : M) :
    (D x).comp ((orthogonalKernelFrame D hD hsurj).ambient x) =
      ContinuousLinearMap.id ℝ F := by
  rw [orthogonalKernelFrame_ambient]
  exact comp_orthogonalRightInverse (D x) (hsurj x)

end NoExoticSixSphere
