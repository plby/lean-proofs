import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceTopBoundary
import Wikipedia.NoExoticSixSphere.OpenSuperlevelBoundary

/-!
# Regular zero-fiber atlases for the three native boundary pieces

All three scalar defining functions are regular at zero. Their actual
zero-fiber atlases therefore supply seven-dimensional smooth structures on
the native boundaries of the already constructed eight-dimensional pieces.
Their inclusions into those pieces are smooth.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def cylinderZeroAtlas : RegularLevelAtlas (K := Vector 7) ((𝓡 7).prod 𝓘(ℝ, ℝ))
    (IntervalSuperlevel.level (M := M) (UnroundedTrace.height A)) :=
  Classical.choice (nonempty_regularLevelAtlas isOpen_univ
    (IntervalSuperlevel.contMDiff_level (I := 𝓡 7) (M := M) (UnroundedTrace.height A)).contMDiffOn
    (subset_univ _) (fun _ hp ↦ IntervalSuperlevel.regular_zero
      (I := 𝓡 7) (UnroundedTrace.height_pos A) hp) 7 (by
        simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]))

def handleZeroAtlas : RegularLevelAtlas (K := Vector 7) 𝓘(ℝ, Vector 4 × Vector 4)
    (Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel.level (UnroundedTrace.handleRadius A)) :=
  Classical.choice (nonempty_regularLevelAtlas isOpen_univ
    (Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel.contDiff_level
      (UnroundedTrace.handleRadius A)).contMDiff.contMDiffOn
    (subset_univ _) (fun _ hp ↦ by
      rw [mfderiv_eq_fderiv]
      exact Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel.regular_zero
        (UnroundedTrace.handleRadius_pos A) hp) 7 (by
          simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]))

def collarZeroAtlas : RegularLevelAtlas (K := Vector 7) collarModel
    (collarLevel (bump A) (UnroundedTrace.handleRadius A)) :=
  Classical.choice (nonempty_regularLevelAtlas isOpen_univ
    (contMDiff_collarLevel (bump A) (UnroundedTrace.handleRadius A)).contMDiffOn
    (subset_univ _) (fun _ hp ↦ regular_collarLevel_zero (bump A)
      (UnroundedTrace.handleRadius_pos A) hp) 7 (by
        simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]))

abbrev LocalBoundary (i : Piece) := letI := pieceAtlas A i;
  {p : pieceDomain A i // (ProductHalfSpace.model (Vector 7)).IsBoundaryPoint p}

@[instance_reducible]
def localBoundaryAtlas (i : Piece) : ChartedSpace (Vector 7) (LocalBoundary A i) := by
  cases i with
  | cylinder =>
      exact OpenSuperlevelBoundary.chartedSpace (cylinderLevelAtlas A)
        (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) (cylinderZeroAtlas A)
  | handle =>
      exact OpenSuperlevelBoundary.chartedSpace (handleLevelAtlas A)
        (unchangedHandleWindow A) (unchangedHandleHomeomorph A) (handleZeroAtlas A)
  | collar =>
      exact OpenSuperlevelBoundary.chartedSpace (collarLevelAtlas A)
        (collarWindow A) (collarWindowHomeomorph A) (collarZeroAtlas A)

theorem localBoundary_isManifold (i : Piece) : letI := localBoundaryAtlas A i;
    IsManifold (𝓡 7) ∞ (LocalBoundary A i) := by
  cases i with
  | cylinder =>
      exact OpenSuperlevelBoundary.isManifold (cylinderLevelAtlas A)
        (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) (cylinderZeroAtlas A)
  | handle =>
      exact OpenSuperlevelBoundary.isManifold (handleLevelAtlas A)
        (unchangedHandleWindow A) (unchangedHandleHomeomorph A) (handleZeroAtlas A)
  | collar =>
      exact OpenSuperlevelBoundary.isManifold (collarLevelAtlas A)
        (collarWindow A) (collarWindowHomeomorph A) (collarZeroAtlas A)

theorem localBoundary_contMDiff_inclusion (i : Piece) : letI := pieceAtlas A i;
    letI := localBoundaryAtlas A i;
    ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞
      (Subtype.val : LocalBoundary A i → pieceDomain A i) := by
  cases i with
  | cylinder =>
      exact OpenSuperlevelBoundary.contMDiff_inclusion (cylinderLevelAtlas A)
        (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) (cylinderZeroAtlas A)
  | handle =>
      exact OpenSuperlevelBoundary.contMDiff_inclusion (handleLevelAtlas A)
        (unchangedHandleWindow A) (unchangedHandleHomeomorph A) (handleZeroAtlas A)
  | collar =>
      exact OpenSuperlevelBoundary.contMDiff_inclusion (collarLevelAtlas A)
        (collarWindow A) (collarWindowHomeomorph A) (collarZeroAtlas A)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
