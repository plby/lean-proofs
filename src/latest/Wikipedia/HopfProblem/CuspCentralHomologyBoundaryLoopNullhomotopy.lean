import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverCompatibility
import Mathlib.Topology.Homotopy.Contractible

/-!
# The actual boundary-direction loop contracts in the central fibre

At unit compact phase, the boundary attaching map gives a literal loop
in the radius-one locus. Its image in the original central cusp fibre
contracts by scaling the planar frontier representative to zero. The
homotopy takes values in the whole central fibre, not in its boundary.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspHoneycomb

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual boundary-direction loop with constant unit compact phase. -/
def boundaryLoop : C(Circle, centralBoundary C ε hε) :=
  (circleBoundaryCellMap C ε hε).comp
    ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩

@[simp] theorem boundaryLoop_apply (z : Circle) :
    boundaryLoop C ε hε z = circleBoundaryCellMap C ε hε (1, z) := rfl

@[simp] theorem boundaryLoop_coe (z : Circle) :
    (boundaryLoop C ε hε z : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε
        (1, (Radial.frontierCellCircleHomeomorph.symm z : Plane)) := rfl

/-- The literal inclusion of the boundary locus into the original central fibre. -/
def centralBoundaryInclusion :
    C(centralBoundary C ε hε, QuotientCentralFibre C ε) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem centralBoundaryInclusion_apply (q : centralBoundary C ε hε) :
    centralBoundaryInclusion C ε hε q = (q : QuotientCentralFibre C ε) := rfl

/-- The boundary-direction loop regarded in the original central fibre. -/
def boundaryLoopInCentral : C(Circle, QuotientCentralFibre C ε) :=
  (centralBoundaryInclusion C ε hε).comp (boundaryLoop C ε hε)

@[simp] theorem boundaryLoopInCentral_apply (z : Circle) :
    boundaryLoopInCentral C ε hε z = honeycombCollapseMap C ε hε
      (1, (Radial.frontierCellCircleHomeomorph.symm z : Plane)) := rfl

/-- Shrinking the literal planar representative gives a homotopy to the
actual unit-phase centre in the original central cusp fibre. -/
def boundaryLoopContraction :
    (boundaryLoopInCentral C ε hε).Homotopy
      (ContinuousMap.const Circle (honeycombCollapseMap C ε hε (1, 0))) where
  toFun p := honeycombCollapseMap C ε hε
    (1, (1 - (p.1 : ℝ)) • (Radial.frontierCellCircleHomeomorph.symm p.2 : Plane))
  continuous_toFun :=
    (honeycombCollapseMap_continuous C ε hε).comp
      (continuous_const.prodMk
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp
            (Radial.frontierCellCircleHomeomorph.symm.continuous.comp continuous_snd))))
  map_zero_left z := by
    change honeycombCollapseMap C ε hε
      (1, (1 - (0 : ℝ)) •
        (Radial.frontierCellCircleHomeomorph.symm z : Plane)) =
      honeycombCollapseMap C ε hε
        (1, (Radial.frontierCellCircleHomeomorph.symm z : Plane))
    simp only [sub_zero, one_smul]
  map_one_left z := by
    change honeycombCollapseMap C ε hε
      (1, (1 - (1 : ℝ)) •
        (Radial.frontierCellCircleHomeomorph.symm z : Plane)) =
      honeycombCollapseMap C ε hε (1, 0)
    simp only [sub_self, zero_smul]

@[simp] theorem boundaryLoopContraction_apply (s : unitInterval) (z : Circle) :
    boundaryLoopContraction C ε hε (s, z) = honeycombCollapseMap C ε hε
      (1, (1 - (s : ℝ)) • (Radial.frontierCellCircleHomeomorph.symm z : Plane)) := rfl

@[simp] theorem boundaryLoopContraction_zero (z : Circle) :
    boundaryLoopContraction C ε hε (0, z) = boundaryLoopInCentral C ε hε z :=
  (boundaryLoopContraction C ε hε).map_zero_left z

@[simp] theorem boundaryLoopContraction_one (z : Circle) :
    boundaryLoopContraction C ε hε (1, z) = honeycombCollapseMap C ε hε (1, 0) :=
  (boundaryLoopContraction C ε hε).map_one_left z

/-- Only the composite with the inclusion into the whole central fibre
is asserted to be nullhomotopic. -/
theorem boundaryLoopInCentral_nullhomotopic :
    (boundaryLoopInCentral C ε hε).Nullhomotopic :=
  ⟨honeycombCollapseMap C ε hε (1, 0), ⟨boundaryLoopContraction C ε hε⟩⟩

theorem centralBoundaryInclusion_comp_boundaryLoop_nullhomotopic :
    ((centralBoundaryInclusion C ε hε).comp (boundaryLoop C ε hε)).Nullhomotopic :=
  boundaryLoopInCentral_nullhomotopic C ε hε

end Wikipedia.HopfProblem.CuspCentralHomology
