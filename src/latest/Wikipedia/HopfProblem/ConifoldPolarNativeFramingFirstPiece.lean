import Wikipedia.HopfProblem.ConifoldPolarNativeFramingBoundary
import Wikipedia.HopfProblem.ConifoldPolarNativeFramingRegions
import Wikipedia.HopfProblem.ThreefoldStandardNormalPieceBoundary

/-!
# Pointwise agreement on the original threefold frontier

The corrected canonical smoothing comparison and the already constructed
compact normal-piece homeomorphism agree on every point of the original
frontier.  The two maps are compared in the original standard sphere,
using the literal normalized conifold matrix of that frontier point.
This is a boundary comparison, not a map on the original exterior.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open CuspCircleNormalTrivialization

/-- The model and actual compact-piece maps coincide on the original frontier. -/
theorem correctedComplement_closedBoundaryNormalizedHomeomorph
    (x : frontier closedDiskNeighborhood) :
    (correctedComplementHomeomorph
      (⟨(closedBoundaryNormalizedHomeomorph x).val,
        (closedBoundaryNormalizedHomeomorph x).property.1⟩ : SpecialLinear)).val =
      (SpecialPeriods.Threefold.StandardNormalPiece.closedHomeomorph
        (SpecialPeriods.Threefold.StandardNormalPiece.boundaryIntoClosed x)).val := by
  obtain ⟨p, rfl⟩ := standardBoundaryHomeomorph.surjective x
  rw [SpecialPeriods.Threefold.StandardNormalPiece.closedHomeomorph_boundaryIntoClosed,
    SpecialPeriods.Threefold.StandardNormalPiece.boundaryHomeomorph_parametrization]
  exact congrArg (fun q : StandardSixSphereCircleModel.Complement => q.val)
    (correctedComplement_smoothingPoint p)

/-- The original normalized frontier matrix lies in the literal smoothing cap. -/
def frontierCapPoint (x : frontier closedDiskNeighborhood) : SmoothingCap :=
  ⟨⟨(closedBoundaryNormalizedHomeomorph x).val,
      (closedBoundaryNormalizedHomeomorph x).property.1⟩, by
    change ConifoldStandardBoundary.frobeniusSq
      (closedBoundaryNormalizedHomeomorph x).val ≤ (17 / 4 : ℝ)
    have h := (closedBoundaryNormalizedHomeomorph x).property.2
    norm_num at h
    exact h.le⟩

@[simp] theorem frontierCapPoint_val (x : frontier closedDiskNeighborhood) :
    (frontierCapPoint x).val.val = (closedBoundaryNormalizedHomeomorph x).val := rfl

/-- The compact cap comparison has the same original frontier marking as the first piece. -/
theorem correctedCapHomeomorph_frontierCapPoint (x : frontier closedDiskNeighborhood) :
    (correctedCapHomeomorph (frontierCapPoint x)).val =
      (SpecialPeriods.Threefold.StandardNormalPiece.closedHomeomorph
        (SpecialPeriods.Threefold.StandardNormalPiece.boundaryIntoClosed x)).val :=
  correctedComplement_closedBoundaryNormalizedHomeomorph x

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
