import Wikipedia.NoExoticSixSphere.UnchangedCylinderCoordinates
import Wikipedia.NoExoticSixSphere.OpenSuperlevelAtlas

/-!
# The original-atlas boundary structure on the unchanged cylinder piece

Apply the interval superlevel construction and the actual cylinder
homeomorphism. The resulting half-space model is the same as on the rounded
collar. Native boundary points are precisely the remaining endpoint points.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def cylinderLevelAtlas : SuperlevelAtlas (K := Vector n) ((𝓡 n).prod 𝓘(ℝ, ℝ))
    (IntervalSuperlevel.level (M := M) (UnroundedTrace.height A)) :=
  IntervalSuperlevel.superlevelAtlas (I := 𝓡 n) (UnroundedTrace.height_pos A) n
    finrank_euclideanSpace_fin

@[instance_reducible]
def unchangedCylinderChartedSpace :
    ChartedSpace (ProductHalfSpace.Space (Vector n)) (cylinderOnlyPart A) :=
  OpenSuperlevelAtlas.chartedSpace (cylinderLevelAtlas A) (unchangedCylinderWindow A)
    (unchangedCylinderHomeomorph A)

theorem unchangedCylinder_isManifold : letI := unchangedCylinderChartedSpace A;
    IsManifold (ProductHalfSpace.model (Vector n)) ∞ (cylinderOnlyPart A) :=
  OpenSuperlevelAtlas.isManifold (cylinderLevelAtlas A) (unchangedCylinderWindow A)
    (unchangedCylinderHomeomorph A)

theorem contMDiff_unchangedCylinder_parameters : letI := unchangedCylinderChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector n)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : cylinderOnlyPart A ↦ (unchangedCylinderHomeomorph A p).val.val) :=
  OpenSuperlevelAtlas.contMDiff_coordinates (cylinderLevelAtlas A) (unchangedCylinderWindow A)
    (unchangedCylinderHomeomorph A)

theorem unchangedCylinder_isBoundaryPoint_iff (p : cylinderOnlyPart A) :
    letI := unchangedCylinderChartedSpace A;
    (ProductHalfSpace.model (Vector n)).IsBoundaryPoint p ↔
      (unchangedCylinderHomeomorph A p).val.val.2 = 0 ∨
        (unchangedCylinderHomeomorph A p).val.val.2 = UnroundedTrace.height A := by
  let := unchangedCylinderChartedSpace A
  exact (OpenSuperlevelAtlas.isBoundaryPoint_iff (cylinderLevelAtlas A)
    (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) p).trans
      (IntervalSuperlevel.zero_iff _ _)

theorem bijective_mfderiv_unchangedCylinder_parameters (p : cylinderOnlyPart A) :
    letI := unchangedCylinderChartedSpace A;
    Bijective (mfderiv (ProductHalfSpace.model (Vector n)) ((𝓡 n).prod 𝓘(ℝ, ℝ))
      (fun q : cylinderOnlyPart A ↦ (unchangedCylinderHomeomorph A q).val.val) p) :=
  OpenSuperlevelAtlas.bijective_mfderiv_coordinates (cylinderLevelAtlas A)
    (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) p

theorem contMDiff_unchangedCylinder_ambient : letI := unchangedCylinderChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector n)) (𝓡 (e.ambientDimension + 6)) ∞
      (fun p : cylinderOnlyPart A ↦ p.val.val) := by
  let := unchangedCylinderChartedSpace A
  have h := e.contMDiff_heightCylinder.comp (contMDiff_unchangedCylinder_parameters A)
  intro p
  exact (h p).congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun q ↦ (unchangedCylinderHomeomorph_ambient A q).symm))

variable {B H P : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {J : ModelWithCorners ℝ B H}
  [TopologicalSpace P] [ChartedSpace H P]

theorem contMDiffAt_unchangedCylinder_iff_parameters (g : P → cylinderOnlyPart A) (x : P) :
    letI := unchangedCylinderChartedSpace A;
    ContMDiffAt J (ProductHalfSpace.model (Vector n)) ∞ g x ↔
      ContMDiffAt J ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun y ↦ (unchangedCylinderHomeomorph A (g y)).val.val) x :=
  OpenSuperlevelAtlas.contMDiffAt_iff_coordinates (cylinderLevelAtlas A)
    (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) g x

theorem contMDiff_unchangedCylinder_iff_parameters (g : P → cylinderOnlyPart A) :
    letI := unchangedCylinderChartedSpace A;
    ContMDiff J (ProductHalfSpace.model (Vector n)) ∞ g ↔
      ContMDiff J ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun y ↦ (unchangedCylinderHomeomorph A (g y)).val.val) :=
  OpenSuperlevelAtlas.contMDiff_iff_coordinates (cylinderLevelAtlas A)
    (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) g

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
