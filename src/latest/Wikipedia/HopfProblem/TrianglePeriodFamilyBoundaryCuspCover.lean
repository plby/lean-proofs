import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspNormalizedMap
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspTailFrame
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRefinedWang

/-!
# The actual cusp map on the refined mapping-torus cover

The original cusp attachment is genuinely homotopic to the normalized
clockwise outer-circle map.  Its whole real projection is known from the
actual lifted square.  The explicit shorter cylinder intervals therefore
map to the two actual slit opens.  Both quarter-time maps below are literal
restrictions of this continuous map, with the original fibre unchanged.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle Homology
open ThreefoldOverlapMappingTorus.Cusp SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual normalized boundary projection is the entire clockwise outer curve. -/
theorem normalizedBoundaryMap_outer_projection (t : ℝ) (x : RealTorus₄) :
    boundaryRegularData.projection
        (normalizedBoundaryMap (MappingTorus.mk monodromy (t, x))) =
      outerClockwiseRegularCurve t := by
  rw [normalizedBoundaryMap_projection_mk, nativeLiftedSquare_final_projection]

/-- The first genuine refined cylinder maps into the upper regular-family slit. -/
theorem normalizedBoundaryMap_upper :
    MapsTo normalizedBoundaryMap (RefinedWang.U monodromy)
      (upperFamily boundaryRegularData) := by
  intro q hq
  obtain ⟨t, x, ht, ht', rfl⟩ := (RefinedWang.mem_U_iff monodromy).mp hq
  change boundaryRegularData.projection
    (normalizedBoundaryMap (MappingTorus.mk monodromy (t, x))) ∈ upperBase
  rw [normalizedBoundaryMap_outer_projection]
  exact outerClockwiseRegularCurve_mem_upperBase t ht ht'

/-- The second genuine refined cylinder maps into the lower regular-family slit. -/
theorem normalizedBoundaryMap_lower :
    MapsTo normalizedBoundaryMap (RefinedWang.V monodromy)
      (lowerFamily boundaryRegularData) := by
  intro q hq
  obtain ⟨t, x, ht, ht', rfl⟩ := (RefinedWang.mem_V_iff monodromy).mp hq
  change boundaryRegularData.projection
    (normalizedBoundaryMap (MappingTorus.mk monodromy (t, x))) ∈ lowerBase
  rw [normalizedBoundaryMap_outer_projection]
  exact outerClockwiseRegularCurve_mem_lowerBase t ht ht'

/-- The first actual intersection fibre, at one quarter of the native positive period. -/
def lowerColumn : C(RealTorus₄, familyIntersection boundaryRegularData) :=
  RefinedWang.lowerColumnMap boundaryRegularData monodromy normalizedBoundaryMap
    normalizedBoundaryMap_upper normalizedBoundaryMap_lower

/-- The second actual intersection fibre, at three quarters of that same period. -/
def upperColumn : C(RealTorus₄, familyIntersection boundaryRegularData) :=
  RefinedWang.upperColumnMap boundaryRegularData monodromy normalizedBoundaryMap
    normalizedBoundaryMap_upper normalizedBoundaryMap_lower

/-- No fibre translation or change of marking is introduced in the first map. -/
theorem lowerColumn_coe (x : RealTorus₄) :
    (lowerColumn x).val =
      boundaryRegularData.quotient (nativeLiftedSquare (1, 1 / 4), x) := by
  rw [lowerColumn, RefinedWang.lowerColumnMap_coe, normalizedBoundaryMap_mk]

/-- The second map likewise keeps the literal original fibre point. -/
theorem upperColumn_coe (x : RealTorus₄) :
    (upperColumn x).val =
      boundaryRegularData.quotient (nativeLiftedSquare (1, 3 / 4), x) := by
  rw [upperColumn, RefinedWang.upperColumnMap_coe, normalizedBoundaryMap_mk]

/-- The entire first column lies in the actual left intersection component. -/
theorem lowerColumn_mem (x : RealTorus₄) :
    lowerColumn x ∈ intersectionPiece boundaryRegularData 1 := by
  change boundaryRegularData.projection (lowerColumn x).val ∈
    overlapBase (intersectionIndex 1)
  rw [lowerColumn_coe, boundaryRegularData.projection_quotient]
  change triangleRegularProject (nativeLiftedSquare (1, 1 / 4)) ∈ overlapBase 0
  rw [nativeLiftedSquare_final_projection]
  exact outerClockwiseQuarterPoint.property

/-- The entire second column lies in the actual right intersection component. -/
theorem upperColumn_mem (x : RealTorus₄) :
    upperColumn x ∈ intersectionPiece boundaryRegularData 2 := by
  change boundaryRegularData.projection (upperColumn x).val ∈
    overlapBase (intersectionIndex 2)
  rw [upperColumn_coe, boundaryRegularData.projection_quotient]
  change triangleRegularProject (nativeLiftedSquare (1, 3 / 4)) ∈ overlapBase 2
  rw [nativeLiftedSquare_final_projection]
  exact outerClockwiseThreeQuarterPoint.property

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
