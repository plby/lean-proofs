import Wikipedia.HopfProblem.DegreeCollapseSurgeryExteriorRetraction
import Wikipedia.HopfProblem.DegreeCollapseClosedPieceHomotopy
import Mathlib.Topology.Homotopy.Equiv

/-!
# A deformation of the actual core complement fixing its entire exterior

Glue the radial punctured-piece homotopy to the stationary exterior. The
closed-cover gluing retains both formulas at every time. Its endpoint is
the original exterior inclusion followed by the constructed retraction.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorRetraction

open Wikipedia.SmoothSixDPoincare PuncturedHandle

variable {E F R X Y : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

def exteriorDeformation :
    ((ContinuousMap.id d.OldComplement).comp (exteriorInclusion d)).Homotopy
      (((exteriorInclusion d).comp (retraction d)).comp (exteriorInclusion d)) where
  toFun p := d.oldExteriorMap p.2
  continuous_toFun := (exteriorInclusion d).continuous.comp continuous_snd
  map_zero_left _ := rfl
  map_one_left r := by
    change d.oldExteriorMap r = d.oldExteriorMap (retraction d (d.oldExteriorMap r))
    rw [retraction_exterior]

def puncturedDeformation :
    ((ContinuousMap.id d.OldComplement).comp (puncturedInclusion d)).Homotopy
      (((exteriorInclusion d).comp (retraction d)).comp (puncturedInclusion d)) where
  toFun p := d.oldPuncturedMap
    (p.2.1, PuncturedClosedBallRetraction.deformationMap (p.1, p.2.2))
  continuous_toFun := (puncturedInclusion d).continuous.comp
    ((continuous_fst.comp continuous_snd).prodMk
      (PuncturedClosedBallRetraction.deformationMap.continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  map_zero_left p := by
    change d.oldPuncturedMap (p.1, PuncturedClosedBallRetraction.deformationMap (0, p.2)) =
      d.oldPuncturedMap p
    rw [PuncturedClosedBallRetraction.deformationMap_zero]
  map_one_left p := by
    change d.oldPuncturedMap (p.1, PuncturedClosedBallRetraction.deformationMap (1, p.2)) =
      d.oldExteriorMap (retraction d (d.oldPuncturedMap p))
    rw [PuncturedClosedBallRetraction.deformationMap_one, retraction_punctured]
    exact (exterior_boundary d (p.1, PuncturedClosedBallRetraction.direction p.2)).symm

theorem deformation_agreement (t : unitInterval) (r : R) (p : UnitSphere E × PuncturedBall F)
    (h : d.oldExteriorMap r = d.oldPuncturedMap p) :
    exteriorDeformation d (t, r) = puncturedDeformation d (t, p) := by
  obtain ⟨q, rfl, rfl⟩ := (d.oldPunctured_overlap r p).mp h
  change d.oldExteriorMap (d.boundary q) = d.oldPuncturedMap
    (q.1, PuncturedClosedBallRetraction.deformationMap
      (t, PuncturedClosedBallRetraction.inclusion q.2))
  rw [PuncturedClosedBallRetraction.deformationMap_boundary]
  exact exterior_boundary d q

def deformation : (ContinuousMap.id d.OldComplement).Homotopy
    ((exteriorInclusion d).comp (retraction d)) :=
  ClosedPieceHomotopy.glue d.oldExteriorMap d.oldPuncturedMap
    d.isClosedEmbedding_oldExteriorMap d.isClosedEmbedding_oldPuncturedMap d.oldComplement_cover
    (ContinuousMap.id d.OldComplement) ((exteriorInclusion d).comp (retraction d))
    (exteriorDeformation d) (puncturedDeformation d) (deformation_agreement d)

theorem deformation_exterior (t : unitInterval) (r : R) :
    deformation d (t, d.oldExteriorMap r) = d.oldExteriorMap r :=
  ClosedPieceHomotopy.glue_left d.oldExteriorMap d.oldPuncturedMap
    d.isClosedEmbedding_oldExteriorMap d.isClosedEmbedding_oldPuncturedMap d.oldComplement_cover
    (ContinuousMap.id d.OldComplement) ((exteriorInclusion d).comp (retraction d))
    (exteriorDeformation d) (puncturedDeformation d) (deformation_agreement d) t r

theorem deformation_punctured (t : unitInterval) (p : UnitSphere E × PuncturedBall F) :
    deformation d (t, d.oldPuncturedMap p) = d.oldPuncturedMap
      (p.1, PuncturedClosedBallRetraction.deformationMap (t, p.2)) :=
  ClosedPieceHomotopy.glue_right d.oldExteriorMap d.oldPuncturedMap
    d.isClosedEmbedding_oldExteriorMap d.isClosedEmbedding_oldPuncturedMap d.oldComplement_cover
    (ContinuousMap.id d.OldComplement) ((exteriorInclusion d).comp (retraction d))
    (exteriorDeformation d) (puncturedDeformation d) (deformation_agreement d) t p

/-- The forward map is the actual original exterior inclusion into the whole core complement. -/
def homotopyEquiv : R ≃ₕ d.OldComplement where
  toFun := exteriorInclusion d
  invFun := retraction d
  left_inv := by
    have h : (retraction d).comp (exteriorInclusion d) = ContinuousMap.id R :=
      ContinuousMap.ext (retraction_exterior d)
    rw [h]
  right_inv := ⟨(deformation d).symm⟩

theorem homotopyEquiv_point (r : R) : (homotopyEquiv d r).val = d.oldExterior r := rfl

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorRetraction
