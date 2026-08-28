import Wikipedia.NoExoticSixSphere.AffineStabilizedFramedDiffeomorph
import Wikipedia.NoExoticSixSphere.SphereFramedDerivativeAffineComposition
import Wikipedia.NoExoticSixSphere.DiffeomorphSphereComposition
import Wikipedia.NoExoticSixSphere.StabilizedSphereFrameComparison

/-!
# Original raw sphere operators under an affine stabilized framed comparison

The actual embedding equality is affine. Its derivative has the proved
linear part; the given full normal-frame identity then compares every
column of the original raw operator, with its original moving source twist.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.AffineStabilizedFramedDiffeomorph

open GLOrthonormalization Stiefel NormalFrameSourceCoordinates DiffeomorphSphereComposition

variable {M M' : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [TopologicalSpace M'] [ChartedSpace (Vector 6) M']
  {e : EuclideanEmbedding 6 M} {e' : EuclideanEmbedding 6 M'}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 6) e'.normalProjection e'.NormalModel}
  (F : AffineStabilizedFramedDiffeomorph e a e' a')
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)

include hf in
theorem sphere_framedDerivative (s : Sphere 3) :
    SphereThreeTangentFrame.framedDerivative (e'.toFun ∘ (F.diffeomorph ∘ f)) s =
      F.ambient.toContinuousLinearMap.comp ((appendZeroMap e.ambientDimension F.extra).comp
        (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s)) := by
  let L := F.ambient.toContinuousLinearMap.comp (appendZeroMap e.ambientDimension F.extra)
  have he : e'.toFun ∘ (F.diffeomorph ∘ f) =
      fun s ↦ F.offset + L ((e.toFun ∘ f) s) := funext (fun s ↦ F.embedding_eq (f s))
  rw [he, SphereThreeTangentFrame.framedDerivative_postcomp_affine L F.offset _ (e.smooth.comp hf)]
  exact ContinuousLinearMap.comp_assoc _ _ _

omit f hf in
theorem normal_ambient_comp (x : M) :
    (a'.ambient (F.diffeomorph x)).comp F.normal.toContinuousLinearMap =
      F.ambient.toContinuousLinearMap.comp (BlockSum.operator F.extra (a.ambient x)) :=
  ContinuousLinearMap.ext (F.frame_eq x)

include hf in
theorem rawSphereFrameOperator_comp (s : Sphere 3) :
    (e'.rawSphereFrameOperator a' (F.diffeomorph ∘ f) s).comp
        (block F.normal.toContinuousLinearEquiv 3).toContinuousLinearMap =
      F.ambient.toContinuousLinearMap.comp
        (NormalFrameStabilization.operator F.extra (e.rawSphereFrameOperator a f s)) := by
  unfold EuclideanEmbedding.rawSphereFrameOperator
  rw [operatorSum_comp_block, F.sphere_framedDerivative f hf s,
    NormalFrameStabilization.operator_sum]
  change OperatorSum.operator
    ((a'.ambient (F.diffeomorph (f s))).comp F.normal.toContinuousLinearMap) _ = _
  rw [F.normal_ambient_comp]
  apply ContinuousLinearMap.ext
  intro v
  simp only [OperatorSum.operator_apply, ContinuousLinearMap.comp_apply, map_add]

theorem rawSphereFrameOperatorMap_comp
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    (sourceChange F.normal.toContinuousLinearEquiv).comp
        (e'.rawSphereFrameOperatorMap a' (F.diffeomorph ∘ f)
          (smooth F.diffeomorph f hf) (mfderiv_injective F.diffeomorph f hf hd)) =
      (NormalFrameAmbientCoordinates.targetChange F.ambient.toContinuousLinearEquiv).comp
        ((NormalFrameStabilization.map F.extra).comp (e.rawSphereFrameOperatorMap a f hf hd)) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, sourceChange_value,
    NormalFrameAmbientCoordinates.targetChange_value, NormalFrameStabilization.map_value]
  exact F.rawSphereFrameOperator_comp f hf s

end NoExoticSixSphere.AffineStabilizedFramedDiffeomorph
