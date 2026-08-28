import Wikipedia.HopfProblem.DegreeCollapseLowAttachingDimension
import Wikipedia.HopfProblem.DegreeCollapseLowUnchangedHandleCoordinates
import Wikipedia.NoExoticSixSphere.OpenSuperlevelAtlas

/-!

# The boundary atlas on the actual unchanged handle piece

The open source-disk coordinate and regular transverse-ball superlevel give
the same half-space model as the other pieces. Its actual ambient map is
smooth, and boundary points are exactly the remaining transverse-sphere points.
-/

noncomputable section

open Function Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def handleLevelAtlas : SuperlevelAtlas (K := Vector 7) 𝓘(ℝ, Vector (d + 1) × Vector (7 - d))
    (LowHandleSuperlevel.level (n := d + 1) (q := 7 - d) (UnroundedTrace.handleRadius A)) :=
  LowHandleSuperlevel.superlevelAtlas (n := d + 1) (q := 7 - d)
    (UnroundedTrace.handleRadius_pos A) A.handle_dimension

@[instance_reducible]
def unchangedHandleChartedSpace :
    ChartedSpace (ProductHalfSpace.Space (Vector 7)) (handleOnlyPart A) :=
  OpenSuperlevelAtlas.chartedSpace (handleLevelAtlas A) (unchangedHandleWindow A)
    (unchangedHandleHomeomorph A)

theorem unchangedHandle_isManifold : letI := unchangedHandleChartedSpace A;
    IsManifold (ProductHalfSpace.model (Vector 7)) ∞ (handleOnlyPart A) :=
  OpenSuperlevelAtlas.isManifold (handleLevelAtlas A) (unchangedHandleWindow A)
    (unchangedHandleHomeomorph A)

theorem contMDiff_unchangedHandle_parameters : letI := unchangedHandleChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7)) 𝓘(ℝ, Vector (d + 1) × Vector (7 - d)) ∞
      (fun p : handleOnlyPart A ↦ (unchangedHandleHomeomorph A p).val.val) :=
  OpenSuperlevelAtlas.contMDiff_coordinates (handleLevelAtlas A) (unchangedHandleWindow A)
    (unchangedHandleHomeomorph A)

theorem unchangedHandle_isBoundaryPoint_iff (p : handleOnlyPart A) :
    letI := unchangedHandleChartedSpace A;
    (ProductHalfSpace.model (Vector 7)).IsBoundaryPoint p ↔
      (unchangedHandleHomeomorph A p).val.val.2 ∈
        sphere (0 : Vector (7 - d)) (UnroundedTrace.handleRadius A) := by
  let := unchangedHandleChartedSpace A
  exact (OpenSuperlevelAtlas.isBoundaryPoint_iff (handleLevelAtlas A)
    (unchangedHandleWindow A) (unchangedHandleHomeomorph A) p).trans
      (LowHandleSuperlevel.zero_iff (UnroundedTrace.handleRadius_pos A) _)

theorem bijective_mfderiv_unchangedHandle_parameters (p : handleOnlyPart A) :
    letI := unchangedHandleChartedSpace A;
    Bijective (mfderiv (ProductHalfSpace.model (Vector 7)) 𝓘(ℝ, Vector (d + 1) × Vector (7 - d))
      (fun q : handleOnlyPart A ↦ (unchangedHandleHomeomorph A q).val.val) p) :=
  OpenSuperlevelAtlas.bijective_mfderiv_coordinates (handleLevelAtlas A)
    (unchangedHandleWindow A) (unchangedHandleHomeomorph A) p

theorem contMDiff_unchangedHandle_ambient : letI := unchangedHandleChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7)) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      (fun p : handleOnlyPart A ↦ p.val.val) := by
  let := unchangedHandleChartedSpace A
  intro p
  let q := unchangedHandleHomeomorph A p
  have h := (A.smooth q.val.val.1 (ball_subset_closedBall q.property.1) q.val.val.2
    (handleSuperlevel_vector_mem A q.val)).contMDiffAt.comp p
      ((contMDiff_unchangedHandle_parameters A) p)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun z ↦ (unchangedHandleHomeomorph_ambient A z).symm))

variable {B H P : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {J : ModelWithCorners ℝ B H}
  [TopologicalSpace P] [ChartedSpace H P]

theorem contMDiffAt_unchangedHandle_iff_parameters (g : P → handleOnlyPart A) (x : P) :
    letI := unchangedHandleChartedSpace A;
    ContMDiffAt J (ProductHalfSpace.model (Vector 7)) ∞ g x ↔
      ContMDiffAt J 𝓘(ℝ, Vector (d + 1) × Vector (7 - d)) ∞
        (fun y ↦ (unchangedHandleHomeomorph A (g y)).val.val) x :=
  OpenSuperlevelAtlas.contMDiffAt_iff_coordinates (handleLevelAtlas A)
    (unchangedHandleWindow A) (unchangedHandleHomeomorph A) g x

theorem contMDiff_unchangedHandle_iff_parameters (g : P → handleOnlyPart A) :
    letI := unchangedHandleChartedSpace A;
    ContMDiff J (ProductHalfSpace.model (Vector 7)) ∞ g ↔
      ContMDiff J 𝓘(ℝ, Vector (d + 1) × Vector (7 - d)) ∞
        (fun y ↦ (unchangedHandleHomeomorph A (g y)).val.val) :=
  OpenSuperlevelAtlas.contMDiff_iff_coordinates (handleLevelAtlas A)
    (unchangedHandleWindow A) (unchangedHandleHomeomorph A) g

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
