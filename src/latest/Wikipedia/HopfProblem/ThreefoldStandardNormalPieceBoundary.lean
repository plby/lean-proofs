import Wikipedia.HopfProblem.ThreefoldStandardNormalPieceSmooth
import Wikipedia.HopfProblem.StandardSixSphereCircleModelTube

/-!
# The unchanged actual boundary marking in the standard six-sphere

The frontier of the original normal disk maps homeomorphically to the literal
normal-radius-one-half level in the standard sphere. Its map is precisely the
restriction of the already constructed compact-piece map, and it preserves
the original circle action. This does not construct the missing exterior map.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.StandardNormalPiece

open CuspCircleNormalTrivialization StandardSixSphereCircleModel

attribute [local instance] SpecialPeriods.Threefold.space_t2Space

local notation "Circle" => AddCircle (1 : ℝ)

/-- The actual frontier is identified with the literal standard sphere radius level. -/
def boundaryHomeomorph : frontier closedDiskNeighborhood ≃ₜ ↥(Tube.radiusLevel (1 / 2)) :=
  standardBoundaryHomeomorph.symm.trans
    (Tube.boundaryHomeomorph (1 / 2) (by norm_num) (by norm_num))

@[simp] theorem boundaryHomeomorph_parametrization (p : StandardNormalBoundary) :
    (boundaryHomeomorph (standardBoundaryHomeomorph p)).val =
      (boundaryPoint (1 / 2) (by norm_num) (by norm_num) p).val := by
  change (Tube.boundaryHomeomorph (1 / 2) (by norm_num) (by norm_num)
    (standardBoundaryHomeomorph.symm (standardBoundaryHomeomorph p))).val = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The literal inclusion of the actual frontier into the actual compact normal piece. -/
def boundaryIntoClosed (x : frontier closedDiskNeighborhood) : closedDiskNeighborhood :=
  ⟨x.val, closedDiskNeighborhood_isCompact.isClosed.frontier_subset x.property⟩

@[simp] theorem boundaryIntoClosed_coe (x : frontier closedDiskNeighborhood) :
    (boundaryIntoClosed x : Space) = x.val := rfl

theorem boundaryIntoClosed_parametrization (p : StandardNormalBoundary) :
    boundaryIntoClosed (standardBoundaryHomeomorph p) =
      standardClosedDiskNeighborhoodHomeomorph (standardBoundaryIntoClosedDisk p) := rfl

/-- No additional gluing automorphism is inserted at the boundary of the compact piece. -/
theorem closedHomeomorph_boundaryIntoClosed (x : frontier closedDiskNeighborhood) :
    (closedHomeomorph (boundaryIntoClosed x)).val = (boundaryHomeomorph x).val := by
  obtain ⟨p, rfl⟩ := standardBoundaryHomeomorph.surjective x
  rw [boundaryIntoClosed_parametrization, closedHomeomorph_boundary,
    boundaryHomeomorph_parametrization]

/-- The boundary homeomorphism also intertwines the unchanged original circle actions. -/
theorem boundaryHomeomorph_circleAction (t : Circle)
    (x : frontier closedDiskNeighborhood) :
    (boundaryHomeomorph (closedBoundaryCircleAction t x)).val =
      Isometries.sphereMap (RealFour.circleRotation t) (boundaryHomeomorph x).val := by
  obtain ⟨p, rfl⟩ := standardBoundaryHomeomorph.surjective x
  rw [← standardBoundaryHomeomorph_circleAction, boundaryHomeomorph_parametrization,
    boundaryHomeomorph_parametrization]
  exact congrArg (fun q : Complement => q.val)
    (Isometries.complementMap_boundaryPoint (RealFour.circleRotation t)
      (1 / 2) (by norm_num) (by norm_num) p).symm

/-- Both sides are now literal topological frontiers of their original compact pieces. -/
def frontierHomeomorph :
    frontier closedDiskNeighborhood ≃ₜ frontier (Tube.closedTube (1 / 2)) :=
  boundaryHomeomorph.trans
    (Homeomorph.setCongr (Tube.frontier_closedTube (1 / 2) (by norm_num) (by norm_num)).symm)

@[simp] theorem frontierHomeomorph_coe (x : frontier closedDiskNeighborhood) :
    (frontierHomeomorph x).val = (boundaryHomeomorph x).val := rfl

/-- The full boundary inclusion square for the actual compact pieces commutes exactly. -/
theorem closedHomeomorph_frontier_square (x : frontier closedDiskNeighborhood) :
    closedHomeomorph (boundaryIntoClosed x) =
      Tube.frontierIntoClosed (1 / 2) (by norm_num) (by norm_num) (frontierHomeomorph x) :=
  Subtype.ext (closedHomeomorph_boundaryIntoClosed x)

theorem frontierHomeomorph_circleAction (t : Circle)
    (x : frontier closedDiskNeighborhood) :
    (frontierHomeomorph (closedBoundaryCircleAction t x)).val =
      Isometries.sphereMap (RealFour.circleRotation t) (frontierHomeomorph x).val :=
  boundaryHomeomorph_circleAction t x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.StandardNormalPiece
