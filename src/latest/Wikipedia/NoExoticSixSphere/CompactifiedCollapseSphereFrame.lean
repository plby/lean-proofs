import Wikipedia.NoExoticSixSphere.CompactifiedCollapseFrameComparison
import Wikipedia.NoExoticSixSphere.DiffeomorphSphereComposition
import Wikipedia.NoExoticSixSphere.ManifoldRawSphereFrame
import Wikipedia.NoExoticSixSphere.SphereFramedDerivativeComposition
import Wikipedia.NoExoticSixSphere.TwistedNormalStabilization

/-!
# The actual raw sphere frame under collapse compactification

Differentiate the original finite compactification and combine its tangent
identity with the prescribed normal-frame identity. This gives the full
raw operator after the fixed normal-coordinate change, with the original
three quaternionic tangent columns and ordinary normal stabilization.
-/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StereographicEquator

open GLOrthonormalization Stiefel NormalFrameSourceCoordinates

theorem rawFrame_block {N k k' : ℕ} (x : Vector N)
    (A : Vector k →L[ℝ] Vector N) (T : Vector 3 →L[ℝ] Vector N)
    (A' : Vector k' →L[ℝ] Vector (N + 1)) (T' : Vector 3 →L[ℝ] Vector (N + 1))
    (Q : Vector (k + 1) ≃L[ℝ] Vector k')
    (hA : A'.comp Q.toContinuousLinearMap =
      (augmentedCoordinates N x).toContinuousLinearMap.comp (BlockSum.operator 1 A))
    (hT : T' = (augmentedCoordinates N x).toContinuousLinearMap.comp
      ((appendZeroMap N 1).comp T)) :
    (OperatorSum.operator A' T').comp (block Q 3).toContinuousLinearMap =
      (augmentedCoordinates N x).toContinuousLinearMap.comp
        (NormalFrameStabilization.operator 1 (OperatorSum.operator A T)) := by
  rw [operatorSum_comp_block, hA, hT, NormalFrameStabilization.operator_sum]
  apply ContinuousLinearMap.ext
  intro v
  simp only [OperatorSum.operator_apply, ContinuousLinearMap.comp_apply, map_add]

end NoExoticSixSphere.StereographicEquator

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization StereographicEquator Stiefel NormalFrameSourceCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - 6)))
  (hg : ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) ∞ g)
  (hreg : ∀ y, g y = sphereZero (e.ambientDimension - 6) →
    Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) g y))
  (hN : e.ambientDimension = (e.ambientDimension - 6) + 6)
  (hfiber : ∀ y, g y = sphereZero (e.ambientDimension - 6) ↔ ∃ x, e.compactifiedEmbedding x = y)

local notation "eC" => RegularSphereFiber.embedding g hg (sphereZero (e.ambientDimension - 6))
  hreg 6 hN
local notation "D" => e.diffeomorphToCompactifiedFiber g hg hreg hN hfiber

variable (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)

include hf in
theorem compactifiedSphere_framedDerivative (s : Sphere 3) :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
      (by simpa using hN);
    SphereThreeTangentFrame.framedDerivative ((eC).toFun ∘ (D ∘ f)) s =
      (augmentedCoordinates e.ambientDimension (e.toFun (f s))).toContinuousLinearMap.comp
        ((appendZeroMap e.ambientDimension 1).comp
          (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s)) := by
  let := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  change SphereThreeTangentFrame.framedDerivative
    (finiteAmbient e.ambientDimension ∘ (e.toFun ∘ f)) s = _
  rw [SphereThreeTangentFrame.framedDerivative_postcomp_contDiff
    (finiteAmbient e.ambientDimension) (contDiff_finiteAmbient e.ambientDimension)
    (e.toFun ∘ f) (e.smooth.comp hf)]
  apply ContinuousLinearMap.ext
  intro v
  exact (augmentedCoordinates_appendZero e.ambientDimension (e.toFun (f s))
    (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s v)).symm

namespace FramedCollapseData

variable {e}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)
  (hgerm : ∀ x, (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - 6))
    =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap)
  (b : Sphere e.ambientDimension)

local notation "aC" => RegularSphereFiber.frameWithTargetChart g hg
  (sphereZero (e.ambientDimension - 6)) hreg 6 hN b
  (sphereProjectionDiffeomorph (e.ambientDimension - 6)) (sphereZero_mem_projection_source _)

include hgerm in
theorem compactifiedFrame_ambient_comp (x : M) :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
      (by simpa using hN);
    ((aC).ambient (D x)).comp (d.compactifiedNormalCoordinates hN).toContinuousLinearMap =
      (augmentedCoordinates e.ambientDimension (e.toFun x)).toContinuousLinearMap.comp
        (BlockSum.operator 1 (a.ambient x)) := by
  let := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  exact ContinuousLinearMap.ext (d.compactifiedFrame_ambient hN g hg hreg hfiber hgerm b x)

include hf hgerm in
theorem compactified_rawSphereFrameOperator (s : Sphere 3) :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
      (by simpa using hN);
    ((eC).rawSphereFrameOperator aC (D ∘ f) s).comp
      (block (d.compactifiedNormalCoordinates hN) 3).toContinuousLinearMap =
      (augmentedCoordinates e.ambientDimension (e.toFun (f s))).toContinuousLinearMap.comp
        (NormalFrameStabilization.operator 1 (e.rawSphereFrameOperator a f s)) := by
  let := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  exact rawFrame_block (e.toFun (f s)) (a.ambient (f s))
    (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s)
    ((aC).ambient (D (f s)))
    (SphereThreeTangentFrame.framedDerivative ((eC).toFun ∘ (D ∘ f)) s)
    (d.compactifiedNormalCoordinates hN)
    (d.compactifiedFrame_ambient_comp g hg hreg hN hfiber hgerm b (f s))
    (e.compactifiedSphere_framedDerivative g hg hreg hN hfiber f hf s)

end FramedCollapseData
end NoExoticSixSphere.EuclideanEmbedding
