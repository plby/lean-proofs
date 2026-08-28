import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusTheta

/-!
# The actual boundary cylinders in marked theta coordinates

The character map on each theta edge is exactly the original compact-phase
quotient map over the corresponding side of the honeycomb cell.  The middle
edge is reversed on both sides of the comparison.  In particular the
identification also holds at the two actual toric-origin orbits.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The original quotient projection of a character cylinder is the actual
honeycomb collapse over its straight dual side, including its endpoints. -/
theorem centralProject_edgeCylinder_character_dualSide
    (k : Fin 6) (t : unitInterval) (u : CompactFibreTorus) :
    centralProject C ε hε (edgeCylinder (C 0) k (t, hexagonCharacter k u)) =
      honeycombCollapseMap C ε hε (u, dualSidePoint k t) := by
  rw [edgeCylinder_character_all]
  change centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) =
    centralCollapseMap C ε hε (u, honeycombHomeomorph (C 0) (dualSidePoint k t))
  rw [← edgeArcBase_eq_dualSidePoint (C 0) k t, honeycombHomeomorph_edgeArcBase]

/-- The three character cylinders represent the same actual central points
as the marked, consistently oriented edges of the base theta graph. -/
theorem doubleSuspensionMap_character_orientedEdge
    (u : CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    doubleSuspensionMap C ε hε
        (Suspension.mk t (thetaCircleInclusion j
          (hexagonCharacter (thetaEdgeIndex j) u))) =
      honeycombCollapseMap C ε hε (u, orientedEdgeBasePoint t j) := by
  fin_cases j
  · exact centralProject_edgeCylinder_character_dualSide C ε hε 0 t u
  · exact centralProject_edgeCylinder_character_dualSide C ε hε 1 (unitInterval.symm t) u
  · exact centralProject_edgeCylinder_character_dualSide C ε hε 2 t u

end Wikipedia.HopfProblem.CuspCentralHomology
