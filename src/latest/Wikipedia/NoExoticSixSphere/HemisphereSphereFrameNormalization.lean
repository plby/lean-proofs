import Wikipedia.NoExoticSixSphere.HemisphereFrameCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldFrameBlockCoordinates
import Wikipedia.NoExoticSixSphere.ImmersedFrameDerivativeComparison

/-!
# A parity-preserving global frame map in exact cap chart coordinates

The original normal-chart and source-chart coordinate changes are continuous
on the entire closed cap. Hemisphere retraction extends their inverses to
the whole sphere without changing derivative-frame parity. On the cap the
result is exactly the chart derivative with identity normal columns. The
cap may be transported by any actual sphere homeomorphism. Paired values
are also compared with the original source-twisted frame obstruction.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace HemisphereChartCoordinates

open GLOrthonormalization ManifoldAffineSphereFamily SphereHemisphereRetraction

def sourcePoints (ρ : Sphere 3 ≃ₜ Sphere 3) (s : SourceChart)
    (hs : ∀ x : North, ρ x.val ∈ s.source) : C(North, s.source) :=
  ⟨fun x ↦ ⟨ρ x.val, hs x⟩, (ρ.continuous.comp continuous_subtype_val).subtype_mk _⟩

def targetPoints {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
    (f : C(Sphere 3, M)) (ρ : Sphere 3 ≃ₜ Sphere 3) (c : TargetChart 6 M)
    (hc : ∀ x : North, f (ρ x.val) ∈ c.source) :
    C(North, c.source) :=
  ⟨fun x ↦ ⟨f (ρ x.val), hc x⟩,
    (f.continuous.comp (ρ.continuous.comp continuous_subtype_val)).subtype_mk _⟩

end HemisphereChartCoordinates

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel ManifoldAffineSphereFamily FrameBlockCoordinates
open SphereHemisphereRetraction HemisphereChartCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
  (ρ : Sphere 3 ≃ₜ Sphere 3) (s : SourceChart) (c : TargetChart 6 M)
  (hs : ∀ x : North, ρ x.val ∈ s.source) (hc : ∀ x : North, f (ρ x.val) ∈ c.source)

def hemisphereTargetInverse (x : North) :
    Vector e.ambientDimension ≃L[ℝ] Vector ((e.ambientDimension - 6) + 6) :=
  (e.normalChartCoordinates ν c (targetPoints f ρ c hc x)).symm

def hemisphereSourceInverse (x : North) :
    Vector ((e.ambientDimension - 6) + 3) ≃L[ℝ] Vector ((e.ambientDimension - 6) + 3) :=
  (sourceCoordinates (e.ambientDimension - 6) s (sourcePoints ρ s hs x)).symm

theorem continuous_hemisphereTargetInverse :
    Continuous (fun x ↦ (e.hemisphereTargetInverse ν f ρ c hc x).toContinuousLinearMap) :=
  (e.continuous_inverse_normalChartCoordinates ν c).comp (targetPoints f ρ c hc).continuous

theorem continuous_hemisphereSourceInverse :
    Continuous (fun x ↦ (e.hemisphereSourceInverse ρ s hs x).toContinuousLinearMap) :=
  (continuous_inverse_sourceCoordinates (e.ambientDimension - 6) s).comp
    (sourcePoints ρ s hs).continuous

def hemisphereNormalizedFrameMap :
    C(Sphere 3, Monomorphism.Space ((e.ambientDimension - 6) + 6)
      ((e.ambientDimension - 6) + 3)) :=
  Monomorphism.hemisphereRecoordinateAlong (e.hemisphereTargetInverse ν f ρ c hc)
    (e.hemisphereSourceInverse ρ s hs) (e.continuous_hemisphereTargetInverse ν f ρ c hc)
    (e.continuous_hemisphereSourceInverse ρ s hs) ρ (e.sphereFrameOperatorMap ν f hf hi)

theorem hemisphereNormalizedFrameMap_cap (x : North) :
    (e.hemisphereNormalizedFrameMap ν f hf hi ρ s c hs hc (ρ x.val)).val =
      identityBlockOperator (e.ambientDimension - 6)
        (fderiv ℝ (fun z ↦ c (f (s.symm z))) (s (ρ x.val))) := by
  let T := e.normalChartCoordinates ν c (targetPoints f ρ c hc x)
  let S := sourceCoordinates (e.ambientDimension - 6) s (sourcePoints ρ s hs x)
  let D := fderiv ℝ (fun z ↦ c (f (s.symm z))) (s (ρ x.val))
  have he : e.sphereFrameOperator ν f (ρ x.val) = T.toContinuousLinearMap.comp
      ((identityBlockOperator (e.ambientDimension - 6) D).comp S.toContinuousLinearMap) :=
    e.normalSpatialOperator_in_charts ν (fun _ : ℝ ↦ f)
      (hf.comp contMDiff_snd) s c (0, ρ x.val) (hs x) (hc x)
  change (Monomorphism.hemisphereRecoordinateAlong _ _ _ _ ρ _ (ρ x.val)).val = _
  rw [Monomorphism.hemisphereRecoordinateAlong_cap]
  change (T.symm.toContinuousLinearMap.comp
    ((e.sphereFrameOperator ν f (ρ x.val)).comp S.symm.toContinuousLinearMap)) = _
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  change T.symm (T (identityBlockOperator (e.ambientDimension - 6) D (S (S.symm v)))) =
    identityBlockOperator (e.ambientDimension - 6) D v
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem hemisphereNormalizedFrameMap_parity :
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
      (by omega) (by omega) (e.hemisphereNormalizedFrameMap ν f hf hi ρ s c hs hc) =
      e.sphereDerivativeParity ν f hf hi := by
  unfold sphereDerivativeParity
  exact Monomorphism.sphereParityOfDimension_hemisphereRecoordinateAlong
    (e.hemisphereTargetInverse ν f ρ c hc) (e.hemisphereSourceInverse ρ s hs)
    (e.continuous_hemisphereTargetInverse ν f ρ c hc)
    (e.continuous_hemisphereSourceInverse ρ s hs)
    ((e.ambientDimension - 6) + 1) ((e.ambientDimension - 6) + 1)
    (by have h := e.dimension_le_ambient (f (Stiefel.pole 3)); omega)
    (by omega) (by omega) (by omega) ρ (e.sphereFrameOperatorMap ν f hf hi)

theorem hemisphereNormalizedFrameMap_sum_eq_twisted
    (g : C(Sphere 3, M)) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hgi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x))
    (τ : Sphere 3 ≃ₜ Sphere 3) (s' : SourceChart) (c' : TargetChart 6 M)
    (hs' : ∀ x : North, τ x.val ∈ s'.source) (hc' : ∀ x : North, g (τ x.val) ∈ c'.source) :
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
        (by omega) (by omega) (e.hemisphereNormalizedFrameMap ν f hf hi ρ s c hs hc) +
      Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
        (by omega) (by omega) (e.hemisphereNormalizedFrameMap ν g hg hgi τ s' c' hs' hc') =
      e.immersedSphereFrameParity ν f hf hi + e.immersedSphereFrameParity ν g hg hgi := by
  rw [hemisphereNormalizedFrameMap_parity, hemisphereNormalizedFrameMap_parity]
  exact (e.immersedSphereFrameParity_sum_eq_derivativeParity ν f g hf hg hi hgi).symm

end EuclideanEmbedding
end NoExoticSixSphere
