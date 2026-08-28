import Wikipedia.HopfProblem.DegreeCollapseSevenUnchangedCylinderCoordinates
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

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def cylinderLevelAtlas : SuperlevelAtlas (K := Vector 7) ((𝓡 7).prod 𝓘(ℝ, ℝ))
    (IntervalSuperlevel.level (M := M) (UnroundedTrace.height A)) :=
  IntervalSuperlevel.superlevelAtlas (I := 𝓡 7) (UnroundedTrace.height_pos A) 7
    finrank_euclideanSpace_fin

@[instance_reducible]
def unchangedCylinderChartedSpace :
    ChartedSpace (ProductHalfSpace.Space (Vector 7)) (cylinderOnlyPart A) :=
  OpenSuperlevelAtlas.chartedSpace (cylinderLevelAtlas A) (unchangedCylinderWindow A)
    (unchangedCylinderHomeomorph A)

theorem unchangedCylinder_isManifold : letI := unchangedCylinderChartedSpace A;
    IsManifold (ProductHalfSpace.model (Vector 7)) ∞ (cylinderOnlyPart A) :=
  OpenSuperlevelAtlas.isManifold (cylinderLevelAtlas A) (unchangedCylinderWindow A)
    (unchangedCylinderHomeomorph A)

theorem contMDiff_unchangedCylinder_parameters : letI := unchangedCylinderChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7)) ((𝓡 7).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : cylinderOnlyPart A ↦ (unchangedCylinderHomeomorph A p).val.val) :=
  OpenSuperlevelAtlas.contMDiff_coordinates (cylinderLevelAtlas A) (unchangedCylinderWindow A)
    (unchangedCylinderHomeomorph A)

theorem unchangedCylinder_isBoundaryPoint_iff (p : cylinderOnlyPart A) :
    letI := unchangedCylinderChartedSpace A;
    (ProductHalfSpace.model (Vector 7)).IsBoundaryPoint p ↔
      (unchangedCylinderHomeomorph A p).val.val.2 = 0 ∨
        (unchangedCylinderHomeomorph A p).val.val.2 = UnroundedTrace.height A := by
  let := unchangedCylinderChartedSpace A
  exact (OpenSuperlevelAtlas.isBoundaryPoint_iff (cylinderLevelAtlas A)
    (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) p).trans
      (IntervalSuperlevel.zero_iff _ _)

theorem bijective_mfderiv_unchangedCylinder_parameters (p : cylinderOnlyPart A) :
    letI := unchangedCylinderChartedSpace A;
    Bijective (mfderiv (ProductHalfSpace.model (Vector 7)) ((𝓡 7).prod 𝓘(ℝ, ℝ))
      (fun q : cylinderOnlyPart A ↦ (unchangedCylinderHomeomorph A q).val.val) p) :=
  OpenSuperlevelAtlas.bijective_mfderiv_coordinates (cylinderLevelAtlas A)
    (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) p

theorem contMDiff_unchangedCylinder_ambient : letI := unchangedCylinderChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7)) (𝓡 (e.ambientDimension + 6)) ∞
      (fun p : cylinderOnlyPart A ↦ p.val.val) := by
  let := unchangedCylinderChartedSpace A
  have h := (HeightCylinder.contMDiff_heightCylinder e).comp (contMDiff_unchangedCylinder_parameters A)
  intro p
  exact (h p).congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun q ↦ (unchangedCylinderHomeomorph_ambient A q).symm))

variable {B H P : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {J : ModelWithCorners ℝ B H}
  [TopologicalSpace P] [ChartedSpace H P]

theorem contMDiffAt_unchangedCylinder_iff_parameters (g : P → cylinderOnlyPart A) (x : P) :
    letI := unchangedCylinderChartedSpace A;
    ContMDiffAt J (ProductHalfSpace.model (Vector 7)) ∞ g x ↔
      ContMDiffAt J ((𝓡 7).prod 𝓘(ℝ, ℝ)) ∞
        (fun y ↦ (unchangedCylinderHomeomorph A (g y)).val.val) x :=
  OpenSuperlevelAtlas.contMDiffAt_iff_coordinates (cylinderLevelAtlas A)
    (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) g x

theorem contMDiff_unchangedCylinder_iff_parameters (g : P → cylinderOnlyPart A) :
    letI := unchangedCylinderChartedSpace A;
    ContMDiff J (ProductHalfSpace.model (Vector 7)) ∞ g ↔
      ContMDiff J ((𝓡 7).prod 𝓘(ℝ, ℝ)) ∞
        (fun y ↦ (unchangedCylinderHomeomorph A (g y)).val.val) :=
  OpenSuperlevelAtlas.contMDiff_iff_coordinates (cylinderLevelAtlas A)
    (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) g

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
