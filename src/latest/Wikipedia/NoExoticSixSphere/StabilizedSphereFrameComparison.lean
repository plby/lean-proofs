import Wikipedia.NoExoticSixSphere.StabilizedFramedDiffeomorph
import Wikipedia.NoExoticSixSphere.FramedEmbeddingReparametrization
import Wikipedia.NoExoticSixSphere.ManifoldRawSphereFrame
import Wikipedia.NoExoticSixSphere.SphereFramedDerivativeLinearMap
import Wikipedia.NoExoticSixSphere.TwistedNormalStabilization
import Wikipedia.NoExoticSixSphere.NormalFrameAmbientCoordinates

/-!
# The original sphere operator under a stabilized framed diffeomorphism

Differentiate the actual embedding identity in the original quaternionic
sphere frame. The given normal-column identity then identifies the full
raw operators after fixed source and target changes. Both native atlases
and the original sphere-dependent source twist are retained.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedFramedDiffeomorph

open GLOrthonormalization Stiefel NormalFrameSourceCoordinates

variable {M M' : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [TopologicalSpace M'] [ChartedSpace (Vector 6) M']
  {e : EuclideanEmbedding 6 M} {e' : EuclideanEmbedding 6 M'}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 6) e'.normalProjection e'.NormalModel}
  (F : StabilizedFramedDiffeomorph e a e' a')
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)

include hf in
theorem sphere_comp_smooth : ContMDiff (𝓡 3) (𝓡 6) ∞ (F.diffeomorph ∘ f) :=
  F.diffeomorph.contMDiff.comp hf

theorem sphere_comp_injective (hi : Injective f) : Injective (F.diffeomorph ∘ f) :=
  F.diffeomorph.injective.comp hi

include hf in
theorem sphere_comp_mfderiv_injective
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) (s : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (F.diffeomorph ∘ f) s) := by
  rw [mfderiv_comp s (F.diffeomorph.contMDiff.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  exact ((F.diffeomorph.isLocalDiffeomorph (f s)).mfderivToContinuousLinearEquiv
    (by simp)).injective.comp (hd s)

include hf in
theorem sphere_framedDerivative (s : Sphere 3) :
    SphereThreeTangentFrame.framedDerivative (e'.toFun ∘ (F.diffeomorph ∘ f)) s =
      F.ambient.toContinuousLinearMap.comp ((appendZeroMap e.ambientDimension F.extra).comp
        (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s)) := by
  have he : e'.toFun ∘ (F.diffeomorph ∘ f) =
      (F.ambient.toContinuousLinearMap.comp (appendZeroMap e.ambientDimension F.extra)) ∘
        (e.toFun ∘ f) := funext (fun s ↦ F.embedding_eq (f s))
  rw [he, SphereThreeTangentFrame.framedDerivative_postcomp_clm _ _ (e.smooth.comp hf)]
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
          (F.sphere_comp_smooth f hf) (F.sphere_comp_mfderiv_injective f hf hd)) =
      (NormalFrameAmbientCoordinates.targetChange F.ambient.toContinuousLinearEquiv).comp
        ((NormalFrameStabilization.map F.extra).comp (e.rawSphereFrameOperatorMap a f hf hd)) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, sourceChange_value,
    NormalFrameAmbientCoordinates.targetChange_value, NormalFrameStabilization.map_value]
  exact F.rawSphereFrameOperator_comp f hf s

end NoExoticSixSphere.StabilizedFramedDiffeomorph
