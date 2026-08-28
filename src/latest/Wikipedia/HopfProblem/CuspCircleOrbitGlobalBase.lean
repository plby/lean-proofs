import Wikipedia.HopfProblem.CuspCircleOrbitGlobalBasic

/-!
# The original base coordinate and toric overlaps survive circle descent

The invariant-coordinate map to the actual global orbit space retains
the original Riemann-sphere projection, its original cusp chart, and every
original toric chart overlap. The full global orbit equality is stated
with its actual coordinate-cover equality; deck identifications are not
discarded or replaced by injectivity of a whole chart.
-/

noncomputable section

open Set Topology
open scoped Matrix OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
namespace Global

open ToricCharts ToricFan
open _root_.Wikipedia.HopfProblem.ToricFan.Triangle
open Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

local notation "E₃" => CoordinateSpace 3

/-- The unchanged cusp covering retains the literal original monomial time. -/
theorem cuspParameter_quotientMap (a : Triangle) (z : Domain) :
    CuspGeometry.parameter (quotientMap a z) = ToricFan.Triangle.time (z : E₃) := by
  change ToricSpace.time (ToricSpace.inclusion a (z : E₃)) = _
  exact ToricSpace.time_inclusion a z

theorem baseProjection_invariantMap_mem_source (a : Triangle) (p : orbitDomain) :
    CircleOrbitSpace.baseProjection (invariantMap a p) ∈ CuspGeometry.sphereChart.source := by
  obtain ⟨z, rfl⟩ := localOrbitProjection_surjective p
  rw [invariantMap_projection, CircleOrbitSpace.baseProjection_quotientMap]
  exact CuspGeometry.projectionSphere_inclusion_mem_sphereChart_source (quotientMap a z)

/-- In the actual base cusp chart, the descended base function is exactly `aβ/2`. -/
theorem sphereChart_baseProjection_invariantMap (a : Triangle) (p : orbitDomain) :
    CuspGeometry.sphereChart (CircleOrbitSpace.baseProjection (invariantMap a p)) =
      orbitTime (p : ℂ × ℂ × ℝ) := by
  obtain ⟨z, rfl⟩ := localOrbitProjection_surjective p
  rw [invariantMap_projection, CircleOrbitSpace.baseProjection_quotientMap]
  change CuspGeometry.sphereChart
      (projectionSphere (CuspGeometry.inclusion (quotientMap a z))) =
    orbitTime (localOrbitMap z)
  rw [CuspGeometry.sphereChart_projectionSphere_inclusion,
    cuspParameter_quotientMap, orbitTime_localOrbitMap]

/-- The original sphere-valued projection itself, not merely a reparametrized time function. -/
theorem baseProjection_invariantMap (a : Triangle) (p : orbitDomain) :
    CircleOrbitSpace.baseProjection (invariantMap a p) =
      CuspGeometry.sphereChart.symm (orbitTime (p : ℂ × ℂ × ℝ)) := by
  rw [← sphereChart_baseProjection_invariantMap a p]
  exact (CuspGeometry.sphereChart.left_inv
    (baseProjection_invariantMap_mem_source a p)).symm

/-- The original central fibre is still detected by the original vanishing time. -/
theorem baseProjection_invariantMap_eq_infty_iff (a : Triangle) (p : orbitDomain) :
    CircleOrbitSpace.baseProjection (invariantMap a p) = (∞ : RiemannSphere) ↔
      orbitTime (p : ℂ × ℂ × ℝ) = 0 := by
  obtain ⟨z, rfl⟩ := localOrbitProjection_surjective p
  rw [invariantMap_projection, CircleOrbitSpace.baseProjection_quotientMap]
  change projectionSphere (CuspGeometry.inclusion (quotientMap a z)) =
      (∞ : RiemannSphere) ↔ orbitTime (localOrbitMap z) = 0
  rw [CuspGeometry.projectionSphere_inclusion_eq_infty_iff,
    cuspParameter_quotientMap, orbitTime_localOrbitMap]

/-- The full global orbit relation still retains the original coordinate-cover equality. -/
theorem invariantMap_projection_eq_iff (a b : Triangle) (z w : Domain) :
    invariantMap a (localOrbitProjection z) = invariantMap b (localOrbitProjection w) ↔
      ∃ t : AddCircle (1 : ℝ),
        globalMap b (coordinateAction (DeltaSweep.circleParameter t) w) = globalMap a z := by
  rw [invariantMap_projection, invariantMap_projection, CircleOrbitSpace.quotientMap_eq_iff]
  simp only [globalMap_circle_coordinateAction]

/-- Any original toric overlap gives exactly the original global covering equality. -/
theorem globalMap_chartChange (a b : Triangle) {z w : Domain}
    (hz : (z : E₃) ∈ (chartChange a b).source)
    (hw : chartChange a b (z : E₃) = (w : E₃)) :
    globalMap a z = globalMap b w := by
  have hi : ToricSpace.inclusion a (z : E₃) = ToricSpace.inclusion b (w : E₃) :=
    (ToricSpace.inclusion_eq_iff a b _ _).mpr ⟨hz, hw⟩
  have ht : tubeMap a z = tubeMap b w := Subtype.ext hi
  simp only [globalMap, Function.comp_apply, quotientMap, ht]

/-- The original toric overlap remains an equality in the actual global circle quotient. -/
theorem invariantMap_chartChange (a b : Triangle) {z w : Domain}
    (hz : (z : E₃) ∈ (chartChange a b).source)
    (hw : chartChange a b (z : E₃) = (w : E₃)) :
    invariantMap a (localOrbitProjection z) = invariantMap b (localOrbitProjection w) := by
  rw [invariantMap_projection, invariantMap_projection]
  exact congrArg CircleOrbitSpace.quotientMap (globalMap_chartChange a b hz hw)

/-- In particular the original two-chart normal transition is retained after descent. -/
theorem invariantMap_normalTransition {z w : Domain} (hz : (z : E₃) 1 ≠ 0)
    (hw : (w : E₃) = ![(z : E₃) 0 * (z : E₃) 1, ((z : E₃) 1)⁻¹,
      (z : E₃) 1 * (z : E₃) 2]) :
    invariantMap ToricSpace.referenceTriangle (localOrbitProjection z) =
      invariantMap (upperNeighbour 1) (localOrbitProjection w) := by
  rw [invariantMap_projection, invariantMap_projection]
  exact congrArg CircleOrbitSpace.quotientMap (globalMap_normalTransition hz hw)

end Global
end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
