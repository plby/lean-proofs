import Wikipedia.NoExoticSixSphere.NormalFrameSourceCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldRawSphereFrame
import Wikipedia.NoExoticSixSphere.OrthonormalRangeFrame

/-!
# Fixed normal-model coordinates and normalization preserve geometric sphere parity

The actual raw normal-and-tangent operator is reparametrized only on its
normal block. The checked source-twist identity transports disk extensions
both ways. Thus every fixed invertible normal-coordinate change preserves
the original mod-two sphere parity, without a determinant or path condition.
Gram--Schmidt normalization also preserves it, in either order relative
to the fixed coordinate change. No commutation of those operations is used.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates DiskBoundary

namespace SmoothRangeFrame

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] {N k k' : ℕ}
  {P : M → Vector N →L[ℝ] Vector N}

def recoordinateModel (a : SmoothRangeFrame I P (Vector k)) (Q : Vector k' ≃L[ℝ] Vector k) :
    SmoothRangeFrame I P (Vector k') where
  equiv x := Q.trans (a.equiv x)
  smooth := by
    change ContMDiff I 𝓘(ℝ, Vector k' →L[ℝ] Vector N) ∞
      (fun x ↦ (a.ambient x).comp Q.toContinuousLinearMap)
    exact a.smooth.clm_comp contMDiff_const

theorem recoordinateModel_ambient (a : SmoothRangeFrame I P (Vector k))
    (Q : Vector k' ≃L[ℝ] Vector k) (x : M) :
    (a.recoordinateModel Q).ambient x = (a.ambient x).comp Q.toContinuousLinearMap := rfl

end SmoothRangeFrame

namespace EuclideanEmbedding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a b : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (Q : Vector (e.ambientDimension - 6) ≃L[ℝ] Vector (e.ambientDimension - 6))
  (he : ∀ x, b.ambient x = (a.ambient x).comp Q.toContinuousLinearMap)

include he in
theorem rawSphereFrameOperatorMap_normal_coordinates
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    e.rawSphereFrameOperatorMap b f hf hd =
      (NormalFrameSourceCoordinates.sourceChange Q).comp
        (e.rawSphereFrameOperatorMap a f hf hd) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  change OperatorSum.operator (b.ambient (f s))
      (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s) =
    (OperatorSum.operator (a.ambient (f s))
      (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s)).comp
        (NormalFrameSourceCoordinates.block Q 3).toContinuousLinearMap
  rw [he, NormalFrameSourceCoordinates.operatorSum_comp_block]

include he in
theorem sphereParity_eq_of_normal_coordinates
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    e.sphereParity a f hf hi hd = e.sphereParity b f hf hi hd := by
  apply zmodTwo_eq_of_zero_iff
  rw [e.sphereParity_zero_iff_raw_twisted_extension a f hf hd hi,
    e.sphereParity_zero_iff_raw_twisted_extension b f hf hd hi,
    e.rawSphereFrameOperatorMap_normal_coordinates a b Q he f hf hd]
  exact (NormalFrameSourceCoordinates.extends_twisted_sourceChange_iff Q
    (e.rawSphereFrameOperatorMap a f hf hd)).symm

theorem sphereParity_recoordinateModel
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    e.sphereParity (a.recoordinateModel Q) f hf hi hd = e.sphereParity a f hf hi hd :=
  (e.sphereParity_eq_of_normal_coordinates a (a.recoordinateModel Q) Q
    (a.recoordinateModel_ambient Q) f hf hi hd).symm

theorem sphereParity_normalized
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    e.sphereParity a.normalized f hf hi hd = e.sphereParity a f hf hi hd := by
  apply zmodTwo_eq_of_zero_iff
  rw [e.sphereParity_zero_iff_raw_twisted_extension a.normalized f hf hd hi,
    e.sphereParity_zero_iff_twisted_extension a f hf hd hi]
  have h : e.rawSphereFrameOperatorMap a.normalized f hf hd =
      e.sphereFrameOperatorMap a f hf hd := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    rfl
  rw [h]

theorem sphereParity_normalized_recoordinateModel
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    e.sphereParity (a.recoordinateModel Q).normalized f hf hi hd =
      e.sphereParity a f hf hi hd :=
  (e.sphereParity_normalized (a.recoordinateModel Q) f hf hi hd).trans
    (e.sphereParity_recoordinateModel a Q f hf hi hd)

end EuclideanEmbedding
end NoExoticSixSphere
