import Wikipedia.HopfProblem.CuspCentralHomologyPhaseAction
import Wikipedia.HopfProblem.CuspCentralHomologyBoundaryLoopNullhomotopy

/-!
# The actual boundary attaching map is the phase action on its base loop

The boundary map in the open-cover coordinates is exactly compact phase
multiplication applied to its phase-one loop. This identity is proved for
the original quotient maps, including all edge and vertex collapses.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

@[simp] theorem centralPhaseAction_honeycombCollapseMap (u : CompactFibreTorus)
    (p : PhasePlane) :
    centralPhaseAction C ε hε u (honeycombCollapseMap C ε hε p) =
      honeycombCollapseMap C ε hε (u * p.1, p.2) :=
  centralPhaseAction_collapse C ε hε u (p.1, honeycombHomeomorph (C 0) p.2)

@[simp] theorem centralPhaseAction_fundamentalCellMap (u : CompactFibreTorus)
    (p : FundamentalCell) :
    centralPhaseAction C ε hε u (fundamentalCellMap C ε hε p) =
      fundamentalCellMap C ε hε (u * p.1, p.2) :=
  centralPhaseAction_honeycombCollapseMap C ε hε u (p.1, p.2)

/-- Every radius level of the actual central quotient is phase invariant. -/
@[simp] theorem centralRadius_phaseAction (u : CompactFibreTorus)
    (x : QuotientCentralFibre C ε) :
    centralRadius C ε hε (centralPhaseAction C ε hε u x) = centralRadius C ε hε x := by
  obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε x
  rw [centralPhaseAction_fundamentalCellMap, centralRadius_fundamentalCellMap,
    centralRadius_fundamentalCellMap]

@[simp] theorem boundaryPhaseAction_boundaryCellMap (u : CompactFibreTorus)
    (p : BoundaryPhaseCell) :
    boundaryPhaseAction C ε hε u (boundaryCellMap C ε hε p) =
      boundaryCellMap C ε hε (u * p.1, p.2) := by
  apply Subtype.ext
  exact centralPhaseAction_honeycombCollapseMap C ε hε u (p.1, p.2)

@[simp] theorem boundaryPhaseAction_circleBoundaryCellMap (u : CompactFibreTorus)
    (p : CompactFibreTorus × Circle) :
    boundaryPhaseAction C ε hε u (circleBoundaryCellMap C ε hε p) =
      circleBoundaryCellMap C ε hε (u * p.1, p.2) := by
  rw [circleBoundaryCellMap_apply, boundaryPhaseAction_boundaryCellMap,
    circleBoundaryCellMap_apply]

/-- The actual attaching map is phase multiplication on its genuine base loop. -/
theorem circleBoundaryCellMap_phaseAction (u : CompactFibreTorus) (z : Circle) :
    circleBoundaryCellMap C ε hε (u, z) =
      boundaryPhaseAction C ε hε u (boundaryLoop C ε hε z) := by
  rw [boundaryLoop_apply, boundaryPhaseAction_circleBoundaryCellMap, mul_one]

variable (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))

/-- Bundled continuous-map form of the exact attaching-map factorization. -/
theorem circleBoundaryCellMap_eq_phaseAction :
    circleBoundaryCellMap C ε hε =
      (boundaryPhaseActionMap C ε hε hC).comp
        ((ContinuousMap.id CompactFibreTorus).prodMap (boundaryLoop C ε hε)) := by
  apply ContinuousMap.ext
  intro p
  exact circleBoundaryCellMap_phaseAction C ε hε p.1 p.2

end Wikipedia.HopfProblem.CuspCentralHomology
