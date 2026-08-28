import Wikipedia.NoExoticSixSphere.SphereGluedFrameReparametrization
import Wikipedia.NoExoticSixSphere.HemisphereFrameCoordinates
import Wikipedia.NoExoticSixSphere.ImmersedFrameDerivativeComparison

/-!
# Parity-preserving cancellation of the actual source Jacobian on a closed cap

A sphere homeomorphism need only be a local diffeomorphism on the given cap.
Its inverse block Jacobian there extends to a global coordinate field through
the contracted hemisphere retraction. The resulting global operator map keeps
the original frame parity and exactly cancels the cap reparametrization.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace HemisphereSourceCoordinates

open GLOrthonormalization SphereThreeTangentFrame SphereHemisphereRetraction

variable (k : ℕ) (u ρ : Sphere 3 ≃ₜ Sphere 3)
  (hu : ∀ x : North, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u (ρ x.val))

def inverseJacobian (x : North) : Vector (k + 3) ≃L[ℝ] Vector (k + 3) :=
  (sourceBlockJacobianEquiv k u (ρ x.val) (hu x)).symm

theorem continuous_inverseJacobian :
    Continuous (fun x ↦ (inverseJacobian k u ρ hu x).toContinuousLinearMap) := by
  have hρ : Continuous (fun x : North ↦ ρ x.val) :=
    ρ.continuous.comp continuous_subtype_val
  have hJ : Continuous (fun x : North ↦ sourceJacobian u (ρ x.val)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (continuousAt_sourceJacobian u (ρ x.val) (hu x).contMDiffAt).comp
      (f := fun y : North ↦ ρ y.val) hρ.continuousAt
  have hB : Continuous (fun x : North ↦ sourceBlockJacobian k u (ρ x.val)) :=
    FrameBlockCoordinates.continuous_identityBlockOperator k _ hJ
  have he (x : North) : (inverseJacobian k u ρ hu x).toContinuousLinearMap =
      (sourceBlockJacobian k u (ρ x.val)).inverse := by
    rw [← sourceBlockJacobianEquiv_toContinuousLinearMap k u (ρ x.val) (hu x)]
    exact (ContinuousLinearMap.inverse_equiv
      (sourceBlockJacobianEquiv k u (ρ x.val) (hu x))).symm
  simp_rw [he]
  rw [continuous_iff_continuousAt]
  intro x
  have hi : (sourceBlockJacobian k u (ρ x.val)).IsInvertible :=
    ⟨sourceBlockJacobianEquiv k u (ρ x.val) (hu x),
      sourceBlockJacobianEquiv_toContinuousLinearMap k u (ρ x.val) (hu x)⟩
  exact (hi.contDiffAt_map_inverse (n := ∞)).continuousAt.comp
    (f := fun y : North ↦ sourceBlockJacobian k u (ρ y.val)) hB.continuousAt

end HemisphereSourceCoordinates

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SphereThreeTangentFrame SphereHemisphereRetraction
open HemisphereSourceCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (K : C(Sphere 3, M)) (hK : ContMDiff (𝓡 3) (𝓡 6) ∞ K)
  (hKi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x))
  (u ρ : Sphere 3 ≃ₜ Sphere 3)
  (hu : ∀ x : North, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u (ρ x.val))

def capSourceNormalizedFrameMap :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) :=
  Monomorphism.hemisphereRecoordinateAlong
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector e.ambientDimension))
    (inverseJacobian (e.ambientDimension - 6) u ρ hu) continuous_const
    (continuous_inverseJacobian (e.ambientDimension - 6) u ρ hu) ρ
    (e.sphereFrameOperatorMap ν K hK hKi)

theorem capSourceNormalizedFrameMap_cap (f : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hgerm : ∀ x : North, (K : Sphere 3 → M) =ᶠ[𝓝 (ρ x.val)] f ∘ u) (x : North) :
    (e.capSourceNormalizedFrameMap ν K hK hKi u ρ hu (ρ x.val)).val =
      e.sphereFrameOperator ν f (u (ρ x.val)) := by
  change (Monomorphism.hemisphereRecoordinateAlong _ _ _ _ ρ _ (ρ x.val)).val = _
  rw [Monomorphism.hemisphereRecoordinateAlong_cap]
  change (e.sphereFrameOperator ν K (ρ x.val)).comp
    (sourceBlockJacobianEquiv (e.ambientDimension - 6) u
      (ρ x.val) (hu x)).symm.toContinuousLinearMap
      = e.sphereFrameOperator ν f (u (ρ x.val))
  rw [e.sphereFrameOperator_eq_of_germ ν (hgerm x)]
  exact e.sphereFrameOperator_comp_cancel ν f u (ρ x.val)
    (hf.mdifferentiableAt (by simp)) (hu x)

theorem capSourceNormalizedFrameMap_parity :
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
      (by have h := e.dimension_le_ambient (K (Stiefel.pole 3)); omega) (by omega)
      (e.capSourceNormalizedFrameMap ν K hK hKi u ρ hu) =
      e.sphereDerivativeParity ν K hK hKi := by
  unfold sphereDerivativeParity
  exact Monomorphism.sphereParityOfDimension_hemisphereRecoordinateAlong
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector e.ambientDimension))
    (inverseJacobian (e.ambientDimension - 6) u ρ hu) continuous_const
    (continuous_inverseJacobian (e.ambientDimension - 6) u ρ hu)
    ((e.ambientDimension - 6) + 1) ((e.ambientDimension - 6) + 1)
    (by have h := e.dimension_le_ambient (K (Stiefel.pole 3)); omega) (by omega)
    (by have h := e.dimension_le_ambient (K (Stiefel.pole 3)); omega) (by omega)
    ρ (e.sphereFrameOperatorMap ν K hK hKi)

theorem capSourceNormalizedFrameMap_agrees (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hfi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (hgerm : ∀ x : North, (K : Sphere 3 → M) =ᶠ[𝓝 (ρ x.val)] f ∘ u) (x : North) :
    e.capSourceNormalizedFrameMap ν K hK hKi u ρ hu (ρ x.val) =
      ((e.sphereFrameOperatorMap ν f hf hfi).comp (u : C(Sphere 3, Sphere 3))) (ρ x.val) :=
  Subtype.ext (e.capSourceNormalizedFrameMap_cap ν K hK hKi u ρ hu f hf hgerm x)

theorem sphereFrameOperatorMap_precomp_homeomorph_parity :
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
      (by have h := e.dimension_le_ambient (K (Stiefel.pole 3)); omega) (by omega)
      ((e.sphereFrameOperatorMap ν K hK hKi).comp (u : C(Sphere 3, Sphere 3))) =
      e.sphereDerivativeParity ν K hK hKi :=
  Monomorphism.sphereParityOfDimension_precomp_homeomorph _ _ _ _ u

end EuclideanEmbedding
end NoExoticSixSphere
