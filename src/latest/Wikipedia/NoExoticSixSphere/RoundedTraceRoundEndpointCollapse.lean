import Wikipedia.NoExoticSixSphere.RoundedTraceEndpointCollapseNormalization
import Wikipedia.NoExoticSixSphere.CompactLinearFamilyBound
import Wikipedia.NoExoticSixSphere.RadialTubeShapeHomotopy

/-!
# Comparing the actual normalized endpoint collapse with a round framed tube

Compactness supplies a uniform positive shrinking factor for the final
linear fiber coordinates. The explicit radial deformation then gives a
based collapse homotopy to an actual round tube in the signed unit frame.
No new smooth atlas or independently assumed tube is introduced.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)
  {N : Type*} [TopologicalSpace N] (b : C(N, Boundary A))

def endpointFinalCoordinates (p : N) :
    TimeGraphFrameSpace (e := e) ≃L[ℝ] TimeGraphFrameSpace (e := e) :=
  boundaryFiberCoordinates A (1, b p)

theorem continuous_endpointFinalCoordinates :
    Continuous (fun p : N × TimeGraphFrameSpace (e := e) ↦
      endpointFinalCoordinates A b p.1 p.2) := by
  let F : C((I × N) × TimeGraphFrameSpace (e := e), TimeGraphFrameSpace (e := e)) :=
    ⟨fun q ↦ endpointFiberCoordinates A b q.1 q.2, continuous_endpointFiberCoordinates A b⟩
  let j : C(N × TimeGraphFrameSpace (e := e), (I × N) × TimeGraphFrameSpace (e := e)) :=
    ((ContinuousMap.const _ (1 : I)).prodMk ContinuousMap.fst).prodMk ContinuousMap.snd
  exact (F.comp j).continuous

theorem continuous_endpointFinalCoordinates_symm :
    Continuous (fun p : N × TimeGraphFrameSpace (e := e) ↦
      (endpointFinalCoordinates A b p.1).symm p.2) := by
  let F : C((I × N) × TimeGraphFrameSpace (e := e), TimeGraphFrameSpace (e := e)) :=
    ⟨fun q ↦ (endpointFiberCoordinates A b q.1).symm q.2,
      continuous_endpointFiberCoordinates_symm A b⟩
  let j : C(N × TimeGraphFrameSpace (e := e), (I × N) × TimeGraphFrameSpace (e := e)) :=
    ((ContinuousMap.const _ (1 : I)).prodMk ContinuousMap.fst).prodMk ContinuousMap.snd
  exact (F.comp j).continuous

variable [CompactSpace N]

def endpointRoundScale : ℝ := Classical.choose
  (exists_uniform_linear_family_shrink
    (fun p ↦ (endpointFinalCoordinates A b p).toContinuousLinearMap)
      (continuous_endpointFinalCoordinates A b))

theorem endpointRoundScale_pos : 0 < endpointRoundScale A b :=
  (Classical.choose_spec (exists_uniform_linear_family_shrink
    (fun p ↦ (endpointFinalCoordinates A b p).toContinuousLinearMap)
      (continuous_endpointFinalCoordinates A b))).1

theorem endpointRoundScale_bound (p : N) (v : TimeGraphFrameSpace (e := e)) :
    endpointRoundScale A b * ‖endpointFinalCoordinates A b p v‖ ≤ ‖v‖ :=
  (Classical.choose_spec (exists_uniform_linear_family_shrink
    (fun p ↦ (endpointFinalCoordinates A b p).toContinuousLinearMap)
      (continuous_endpointFinalCoordinates A b))).2 p v

variable (τ : N × TimeGraphFrameSpace (e := e) → Vector (e.ambientDimension + 6))

def roundEndpointTube := RadialTubeShapeHomotopy.tube (endpointFinalCoordinates A b)
  (endpointRoundScale A b) (endpointRoundScale_pos A b) τ 1

theorem isOpenEmbedding_roundEndpointTube (hτ : IsOpenEmbedding τ) :
    IsOpenEmbedding (roundEndpointTube A b τ) :=
  RadialTubeShapeHomotopy.isOpenEmbedding_tube (endpointFinalCoordinates A b)
    (endpointRoundScale A b) (endpointRoundScale_pos A b)
    (continuous_endpointFinalCoordinates A b) (continuous_endpointFinalCoordinates_symm A b)
    (endpointRoundScale_bound A b) τ hτ 1

def roundEndpointCollapse (hτ : IsOpenEmbedding τ) :
    C(OnePoint (Vector (e.ambientDimension + 6)), OnePoint (TimeGraphFrameSpace (e := e))) :=
  RadialTubeShapeHomotopy.collapseAt (endpointFinalCoordinates A b)
    (endpointRoundScale A b) (endpointRoundScale_pos A b)
    (continuous_endpointFinalCoordinates A b) (continuous_endpointFinalCoordinates_symm A b)
    (endpointRoundScale_bound A b) τ hτ 1

theorem roundEndpointCollapse_apply (hτ : IsOpenEmbedding τ)
    (z : OnePoint (Vector (e.ambientDimension + 6))) :
    roundEndpointCollapse A b τ hτ z =
      OpenFiberCollapse.collapseOnePoint (roundEndpointTube A b τ) z :=
  RadialTubeShapeHomotopy.collapseFamily_apply (endpointFinalCoordinates A b)
    (endpointRoundScale A b) (endpointRoundScale_pos A b)
    (continuous_endpointFinalCoordinates A b) (continuous_endpointFinalCoordinates_symm A b)
    (endpointRoundScale_bound A b) τ hτ 1 z

def endpointRoundingHomotopy (hτ : IsOpenEmbedding τ) :
    (normalizedEndpointCollapse A b τ hτ 1).Homotopy (roundEndpointCollapse A b τ hτ) where
  toContinuousMap := RadialTubeShapeHomotopy.collapseFamily (endpointFinalCoordinates A b)
    (endpointRoundScale A b) (endpointRoundScale_pos A b)
    (continuous_endpointFinalCoordinates A b) (continuous_endpointFinalCoordinates_symm A b)
    (endpointRoundScale_bound A b) τ hτ
  map_zero_left z := by
    have ht : RadialTubeShapeHomotopy.tube (endpointFinalCoordinates A b)
        (endpointRoundScale A b) (endpointRoundScale_pos A b) τ 0 =
          normalizedEndpointTube A b τ 1 := funext (fun p ↦
      RadialTubeShapeHomotopy.tube_zero (endpointFinalCoordinates A b)
        (endpointRoundScale A b) (endpointRoundScale_pos A b) τ p)
    refine (RadialTubeShapeHomotopy.collapseFamily_apply (endpointFinalCoordinates A b)
      (endpointRoundScale A b) (endpointRoundScale_pos A b)
      (continuous_endpointFinalCoordinates A b) (continuous_endpointFinalCoordinates_symm A b)
      (endpointRoundScale_bound A b) τ hτ 0 z).trans ?_
    rw [ht]
    exact (endpointCollapseFamily_apply A b τ hτ 1 z).symm
  map_one_left _ := rfl

theorem endpointRoundingHomotopy_infty (hτ : IsOpenEmbedding τ) (t : I) :
    endpointRoundingHomotopy A b τ hτ (t, OnePoint.infty) = OnePoint.infty :=
  RadialTubeShapeHomotopy.collapseFamily_infty (endpointFinalCoordinates A b)
    (endpointRoundScale A b) (endpointRoundScale_pos A b)
    (continuous_endpointFinalCoordinates A b) (continuous_endpointFinalCoordinates_symm A b)
    (endpointRoundScale_bound A b) τ hτ t

theorem roundEndpointTube_formula (j : N → Vector (e.ambientDimension + 6))
    (r : ℝ) (hr : 0 < r) (hτ : ∀ q, τ q = j q.1 + boundaryVerticalFrame A (b q.1)
      (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) r q.2))
    (q : N × TimeGraphFrameSpace (e := e)) :
    roundEndpointTube A b τ q = j q.1 + boundaryUnitFrame A (b q.1)
      (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
        (r * endpointRoundScale A b) q.2) := by
  let w := OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
    (r * endpointRoundScale A b) q.2
  have hC := RadialShapeChange.univBall_finalCoordinates
    (endpointFinalCoordinates A b q.1).toContinuousLinearMap (endpointRoundScale A b)
      (endpointRoundScale_pos A b) (endpointRoundScale_bound A b q.1) r hr q.2
  have hB := boundaryVerticalFrame_fiberCoordinates A (1 : I) (b q.1) w
  change boundaryVerticalFrame A (b q.1) (boundaryFiberCoordinates A (1, b q.1) w) =
    boundaryFrameFamily A 1 (b q.1) w at hB
  rw [boundaryFrameFamily_one] at hB
  calc
    roundEndpointTube A b τ q = τ (q.1,
        RadialShapeChange.finalCoordinates (endpointFinalCoordinates A b q.1).toContinuousLinearMap
          (endpointRoundScale A b) q.2) :=
      RadialTubeShapeHomotopy.tube_one (endpointFinalCoordinates A b)
        (endpointRoundScale A b) (endpointRoundScale_pos A b) τ q
    _ = j q.1 + boundaryVerticalFrame A (b q.1)
        (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) r
          (RadialShapeChange.finalCoordinates
            (endpointFinalCoordinates A b q.1).toContinuousLinearMap
              (endpointRoundScale A b) q.2)) := hτ _
    _ = j q.1 + boundaryVerticalFrame A (b q.1) (endpointFinalCoordinates A b q.1 w) :=
      congrArg (fun v : TimeGraphFrameSpace (e := e) ↦
        j q.1 + boundaryVerticalFrame A (b q.1) v) hC
    _ = j q.1 + boundaryUnitFrame A (b q.1) w := congrArg (fun v ↦ j q.1 + v) hB

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
