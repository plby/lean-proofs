import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusAxesCharts
import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusTransitions

/-!
# The complete two-pole pullback of the remaining double curves

The original normal-product map meets each nonfixed double curve in
exactly the two displayed normal axes over zero and infinity. This is
proved on the full native small product domain before restriction to
the injective round chart and the actual compact disk neighborhood.
-/

noncomputable section

open Set
open scoped OnePoint

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open ToricCharts ToricFan ToricFan.Triangle
open SpecialPeriods SpecialPeriods.Threefold
open CuspCircleNormalTrivialization

local notation "CD" => CuspGeometry.data

/-- At a finite base point the nonfixed curve forces the base to zero
and the normal vector to its literal lower axis. -/
theorem globalProductMap_coe_mem_doubleCurve_iff (b : Bool) (a : ℂ) (v : Fibre)
    (hv : radiusSq v < 4 * (CD).radius) :
    globalProductMap ⟨((a : RiemannSphere), v), hv⟩ ∈
        CuspGeometry.doubleCurve (curveIndex b) ↔
      a = 0 ∧ ∃ z : ℂ, v = lowerNormal b z := by
  have haxis := globalProductMap_chart_mem_doubleCurve_iff_axis
    false (a, v) hv (curveIndex b)
  change globalProductMap ⟨((a : RiemannSphere), v), hv⟩ ∈
      CuspGeometry.doubleCurve (curveIndex b) ↔
    ∃ z : ℂ, (a, v) = chartCoordinates false
      (axisPoint ToricSpace.referenceTriangle (curveIndex b) z) at haxis
  simp only [chartCoordinates_lower_axis] at haxis
  constructor
  · intro hp
    obtain ⟨z, hz⟩ := haxis.mp hp
    exact ⟨congrArg Prod.fst hz, z, congrArg Prod.snd hz⟩
  · rintro ⟨ha, z, hz⟩
    exact haxis.mpr ⟨z, Prod.ext ha hz⟩

/-- Over infinity, the complete original quotient pullback is the upper normal axis. -/
theorem globalProductMap_infty_mem_doubleCurve_iff (b : Bool) (v : Fibre)
    (hv : radiusSq v < 4 * (CD).radius) :
    globalProductMap ⟨((∞ : RiemannSphere), v), hv⟩ ∈
        CuspGeometry.doubleCurve (curveIndex b) ↔
      ∃ z : ℂ, v = upperNormal b z := by
  have haxis := globalProductMap_chart_mem_doubleCurve_iff_axis
    true (0, v) hv (curveIndex b)
  change globalProductMap ⟨(RiemannSphere.infinityParametrization 0, v), hv⟩ ∈
      CuspGeometry.doubleCurve (curveIndex b) ↔
    ∃ z : ℂ, (0, v) = chartCoordinates true
      (axisPoint (upperNeighbour 1) (curveIndex b) z) at haxis
  simp only [RiemannSphere.infinityParametrization_zero,
    chartCoordinates_upper_axis] at haxis
  constructor
  · intro hp
    obtain ⟨z, hz⟩ := haxis.mp hp
    exact ⟨z, congrArg Prod.snd hz⟩
  · rintro ⟨z, hz⟩
    exact haxis.mpr ⟨z, Prod.ext rfl hz⟩

/-- The exhaustive native pullback has exactly the two pole axes, including their origins. -/
theorem globalProductMap_mem_doubleCurve_iff (b : Bool) (p : smallNormalProduct) :
    globalProductMap p ∈ CuspGeometry.doubleCurve (curveIndex b) ↔
      (p.val.1 = ((0 : ℂ) : RiemannSphere) ∧ ∃ z : ℂ, p.val.2 = lowerNormal b z) ∨
      (p.val.1 = (∞ : RiemannSphere) ∧ ∃ z : ℂ, p.val.2 = upperNormal b z) := by
  rcases p with ⟨⟨a, v⟩, hp⟩
  induction a using OnePoint.rec with
  | infty =>
      simpa only [OnePoint.infty_ne_coe, false_and, eq_self, true_and, false_or] using
        globalProductMap_infty_mem_doubleCurve_iff b v hp
  | coe a =>
      simpa only [OnePoint.coe_eq_coe, OnePoint.coe_ne_infty, false_and, or_false] using
        globalProductMap_coe_mem_doubleCurve_iff b a v hp

/-- The same complete pullback holds in the actual injective round normal chart. -/
theorem roundProductMap_mem_doubleCurve_iff (b : Bool) (p : roundNormalProduct) :
    roundProductMap p ∈ CuspGeometry.doubleCurve (curveIndex b) ↔
      (p.val.1 = ((0 : ℂ) : RiemannSphere) ∧ ∃ z : ℂ, p.val.2 = lowerNormal b z) ∨
      (p.val.1 = (∞ : RiemannSphere) ∧ ∃ z : ℂ, p.val.2 = upperNormal b z) :=
  globalProductMap_mem_doubleCurve_iff b (roundToSmall p)

/-- The original compact disk neighborhood meets each nonfixed double curve
only in its two actual pole disks. -/
theorem closedProductMap_mem_doubleCurve_iff (b : Bool) (p : ClosedNormalProduct) :
    closedProductMap p ∈ CuspGeometry.doubleCurve (curveIndex b) ↔
      (p.1 = ((0 : ℂ) : RiemannSphere) ∧ ∃ z : ℂ, p.2.val = lowerNormal b z) ∨
      (p.1 = (∞ : RiemannSphere) ∧ ∃ z : ℂ, p.2.val = upperNormal b z) :=
  roundProductMap_mem_doubleCurve_iff b (closedProductIntoRound p)

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
