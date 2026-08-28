import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspBasic

/-!
# Exact double-curve tests in the native normal charts

The original cusp-quotient branch criterion pulls back to the literal
coordinate axes. The inverse normal coordinates then give the precise
axis parametrizations, without an injectivity assumption on the quotient.
-/

noncomputable section

open Set
open scoped OnePoint

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open ToricCharts ToricFan ToricFan.Triangle
open SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction
open CuspCircleNormalTrivialization

local notation "CD" => CuspGeometry.data

/-- The original global chart meets a double curve on exactly its native axis. -/
theorem globalMap_mem_doubleCurve_iff (s : Triangle) (z : FixedCoordinates.Domain)
    (i : Fin 3) :
    FixedCoordinates.globalMap s z ∈ CuspGeometry.doubleCurve i ↔
      ∀ j : Fin 3, j ≠ s.axisIndex i → (z : CoordinateSpace 3) j = 0 := by
  change CuspGeometry.inclusion
      (CuspQuotient.quotientMap (CD).correction (CD).radius
        (FixedCoordinates.tubeMap s z)) ∈
    CuspGeometry.inclusion ''
      CuspQuotient.doubleCurve (CD).correction (CD).radius (CD).radius_pos i ↔ _
  refine (CuspGeometry.inclusion_injective.mem_set_image).trans ?_
  refine (CuspQuotient.mem_doubleCurve_quotientMap (CD).correction (CD).radius
    (CD).radius_pos (FixedCoordinates.tubeMap s z) i).trans ?_
  change (∃ v ∈ ToricSpace.branchVertices (ToricSpace.inclusion s z),
    v + edgeDirection i ∈ ToricSpace.branchVertices (ToricSpace.inclusion s z)) ↔ _
  rw [ToricSpace.branchVertices_inclusion]
  exact chartBranches_edge_axis s z i

/-- The exact branch criterion after the actual inverse normal coordinate map. -/
theorem globalProductMap_chart_mem_doubleCurve_iff (b : Bool) (q : Model)
    (hq : radiusSq q.2 < 4 * (CD).radius) (i : Fin 3) :
    globalProductMap ⟨baseProductChart b q, hq⟩ ∈ CuspGeometry.doubleCurve i ↔
      ∀ j : Fin 3, j ≠ (chartTriangle b).axisIndex i →
        (chartCoordinates b).symm q j = 0 := by
  rw [globalProductMap_baseProductChart]
  exact globalMap_mem_doubleCurve_iff (chartTriangle b) (coordinatePoint b q hq) i

/-- A native coordinate-axis test is the range of its literal normal-coordinate parametrization. -/
theorem chartCoordinates_axis_iff (b : Bool) (q : Model) (i : Fin 3) :
    (∀ j : Fin 3, j ≠ (chartTriangle b).axisIndex i →
      (chartCoordinates b).symm q j = 0) ↔
    ∃ z : ℂ, q = chartCoordinates b (axisPoint (chartTriangle b) i z) := by
  rw [← eq_axisPoint_iff]
  constructor
  · intro h
    refine ⟨(chartCoordinates b).symm q ((chartTriangle b).axisIndex i), ?_⟩
    have he := congrArg (chartCoordinates b) h
    simpa only [(chartCoordinates b).apply_symm_apply] using he
  · rintro ⟨z, rfl⟩
    rw [(chartCoordinates b).symm_apply_apply, axisPoint_apply_axisIndex]

/-- The full original quotient pullback is exactly the actual chart-axis range. -/
theorem globalProductMap_chart_mem_doubleCurve_iff_axis (b : Bool) (q : Model)
    (hq : radiusSq q.2 < 4 * (CD).radius) (i : Fin 3) :
    globalProductMap ⟨baseProductChart b q, hq⟩ ∈ CuspGeometry.doubleCurve i ↔
      ∃ z : ℂ, q = chartCoordinates b (axisPoint (chartTriangle b) i z) := by
  rw [globalProductMap_chart_mem_doubleCurve_iff, chartCoordinates_axis_iff]

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
