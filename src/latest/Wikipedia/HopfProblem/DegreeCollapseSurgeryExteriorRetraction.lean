import Wikipedia.HopfProblem.DegreeCollapsePuncturedClosedBallRetraction
import Wikipedia.SmoothSixDPoincare.SurgeryComplementPieces
import Wikipedia.SmoothSixDPoincare.ClosedPieceMaps

/-!
# The actual core complement retracts to the closed surgery exterior

The exterior and punctured product are the original closed embedded pieces.
Normalize only the punctured disk coordinate and use the original corner
map. Exact corner incidences glue this to the identity of the exterior.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorRetraction

open Wikipedia.SmoothSixDPoincare PuncturedHandle

variable {E F R X Y : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

theorem boundary_incidence (q : UnitSphere E × UnitSphere F) :
    d.oldExterior (d.boundary q) = d.oldPiece (oldBoundary q) :=
  (d.old_overlap _ _).mpr ⟨q, rfl, rfl⟩

theorem continuous_boundary : Continuous d.boundary := by
  apply d.oldExterior_closed.isEmbedding.isInducing.continuous_iff.mpr
  have he : (fun q ↦ d.oldExterior (d.boundary q)) =
      fun q ↦ d.oldPiece (oldBoundary q) := funext (boundary_incidence d)
  change Continuous (fun q ↦ d.oldExterior (d.boundary q))
  rw [he]
  apply d.oldPiece_closed.continuous.comp
  exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

def boundaryMap : C(UnitSphere E × UnitSphere F, R) := ⟨d.boundary, continuous_boundary d⟩

def exteriorInclusion : C(R, d.OldComplement) :=
  ⟨d.oldExteriorMap, d.isClosedEmbedding_oldExteriorMap.continuous⟩

def puncturedInclusion : C(UnitSphere E × PuncturedBall F, d.OldComplement) :=
  ⟨d.oldPuncturedMap, d.isClosedEmbedding_oldPuncturedMap.continuous⟩

def radialBoundaryMap : C(UnitSphere E × PuncturedBall F, R) :=
  (boundaryMap d).comp (ContinuousMap.fst.prodMk
    (PuncturedClosedBallRetraction.direction.comp ContinuousMap.snd))

theorem radialBoundary_agrees (r : R) (p : UnitSphere E × PuncturedBall F)
    (h : d.oldExteriorMap r = d.oldPuncturedMap p) : r = radialBoundaryMap d p := by
  obtain ⟨q, rfl, rfl⟩ := (d.oldPunctured_overlap r p).mp h
  change d.boundary q = d.boundary
    (q.1, PuncturedClosedBallRetraction.direction (boundaryPoint q.2))
  apply congrArg d.boundary
  apply Prod.ext
  · rfl
  · exact (PuncturedClosedBallRetraction.direction_inclusion q.2).symm

def retraction : C(d.OldComplement, R) :=
  ClosedCover.mapOfClosedPieces d.oldExteriorMap d.oldPuncturedMap
    d.isClosedEmbedding_oldExteriorMap d.isClosedEmbedding_oldPuncturedMap
    d.oldComplement_cover (ContinuousMap.id R) (radialBoundaryMap d) (radialBoundary_agrees d)

theorem retraction_exterior (r : R) : retraction d (d.oldExteriorMap r) = r :=
  ClosedCover.mapOfClosedPieces_left _ _ _ _ _ _ _ _ r

theorem retraction_punctured (p : UnitSphere E × PuncturedBall F) :
    retraction d (d.oldPuncturedMap p) =
      d.boundary (p.1, PuncturedClosedBallRetraction.direction p.2) :=
  ClosedCover.mapOfClosedPieces_right _ _ _ _ _ _ _ _ p

theorem exterior_boundary (q : UnitSphere E × UnitSphere F) :
    d.oldExteriorMap (d.boundary q) = d.oldPuncturedMap (q.1, boundaryPoint q.2) :=
  (d.oldPunctured_overlap _ _).mpr ⟨q, rfl, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorRetraction
