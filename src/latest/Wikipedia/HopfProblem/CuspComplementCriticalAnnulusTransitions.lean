import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusKappa
import Wikipedia.HopfProblem.CuspComplementNormalLifts

/-!
# The literal normal frames at both ends of the two nonfixed double curves

The two remaining curve indices are zero and two. Their original affine
parameters give explicit real normal vectors over zero and infinity in
the already fixed normal product. The upper parameters retain the full
correction-dependent deck multipliers. Every displayed closed-disk map
is the unchanged map into the original threefold.
-/

noncomputable section

open Set
open scoped ComplexConjugate Matrix OnePoint

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open ToricCharts ToricFan ToricFan.Triangle ToricSpace
open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

local notation "CD" => CuspGeometry.data

/-- The two native double curves other than the fixed middle curve. -/
def curveIndex : Bool → Fin 3
  | false => 0
  | true => 2

theorem curveIndex_ne_one (b : Bool) : curveIndex b ≠ 1 := by
  cases b <;> decide

/-- The original upper-chart deck factor for the chosen curve. -/
def kappa : Bool → ℂ
  | false => kappaZero
  | true => kappaTwo

theorem kappa_ne_zero (b : Bool) : kappa b ≠ 0 := by
  cases b
  · exact kappaZero_ne_zero
  · exact kappaTwo_ne_zero

/-- The original lower normal frame over the lower triple point. -/
def lowerNormal : Bool → ℂ → Fibre
  | false, z => (z, 0)
  | true, z => (0, conj z)

/-- The original upper normal frame over the upper triple point. -/
def upperNormal : Bool → ℂ → Fibre
  | false, w => (-conj w, 0)
  | true, w => (0, w)

@[simp] theorem lowerNormal_zero (b : Bool) : lowerNormal b 0 = 0 := by
  cases b <;> simp [lowerNormal]

@[simp] theorem upperNormal_zero (b : Bool) : upperNormal b 0 = 0 := by
  cases b <;> simp [upperNormal]

theorem radiusSq_lowerNormal (b : Bool) (z : ℂ) :
    radiusSq (lowerNormal b z) = ‖z‖ ^ 2 := by
  cases b <;> simp [lowerNormal, radiusSq, Complex.normSq_eq_norm_sq]

theorem radiusSq_upperNormal (b : Bool) (z : ℂ) :
    radiusSq (upperNormal b z) = ‖z‖ ^ 2 := by
  cases b <;> simp [upperNormal, radiusSq, Complex.normSq_eq_norm_sq]

theorem radiusSq_lowerNormal_le_iff (b : Bool) (z : ℂ) :
    radiusSq (lowerNormal b z) ≤ closedRadius ^ 2 ↔ ‖z‖ ≤ closedRadius := by
  rw [radiusSq_lowerNormal]
  exact sq_le_sq₀ (norm_nonneg z) closedRadius_pos.le

theorem radiusSq_upperNormal_le_iff (b : Bool) (z : ℂ) :
    radiusSq (upperNormal b z) ≤ closedRadius ^ 2 ↔ ‖z‖ ≤ closedRadius := by
  rw [radiusSq_upperNormal]
  exact sq_le_sq₀ (norm_nonneg z) closedRadius_pos.le

theorem radiusSq_lowerNormal_lt_iff (b : Bool) (z : ℂ) :
    radiusSq (lowerNormal b z) < closedRadius ^ 2 ↔ ‖z‖ < closedRadius := by
  rw [radiusSq_lowerNormal]
  exact sq_lt_sq₀ (norm_nonneg z) closedRadius_pos.le

theorem radiusSq_upperNormal_lt_iff (b : Bool) (z : ℂ) :
    radiusSq (upperNormal b z) < closedRadius ^ 2 ↔ ‖z‖ < closedRadius := by
  rw [radiusSq_upperNormal]
  exact sq_lt_sq₀ (norm_nonneg z) closedRadius_pos.le

/-- The lower axis formula uses the actual reversed lower axis indexing. -/
theorem chartCoordinates_lower_axis (b : Bool) (z : ℂ) :
    chartCoordinates false (axisPoint referenceTriangle (curveIndex b) z) =
      (0, lowerNormal b z) := by
  cases b <;>
    simp [curveIndex, lowerNormal, chartCoordinates_apply, axisPoint, axisIndex,
      referenceTriangle, fibreEquiv, lowerMap]

/-- The upper axis formula uses the original upper triangle of the fixed normal chart. -/
theorem chartCoordinates_upper_axis (b : Bool) (z : ℂ) :
    chartCoordinates true (axisPoint (upperNeighbour 1) (curveIndex b) z) =
      (0, upperNormal b z) := by
  cases b <;>
    simp [curveIndex, upperNormal, chartCoordinates_apply, axisPoint, axisIndex,
      upperNeighbour, fibreEquiv, upperMap]

theorem chartCoordinates_symm_lowerNormal (b : Bool) (z : ℂ) :
    (chartCoordinates false).symm (0, lowerNormal b z) =
      axisPoint referenceTriangle (curveIndex b) z := by
  rw [← chartCoordinates_lower_axis, (chartCoordinates false).symm_apply_apply]

theorem chartCoordinates_symm_upperNormal (b : Bool) (z : ℂ) :
    (chartCoordinates true).symm (0, upperNormal b z) =
      axisPoint (upperNeighbour 1) (curveIndex b) z := by
  rw [← chartCoordinates_upper_axis, (chartCoordinates true).symm_apply_apply]

/-- The lower normal frame maps to the original lower toric axis. -/
theorem fromProduct_lowerNormal (b : Bool) (z : ℂ) :
    fromProduct (((0 : ℂ) : RiemannSphere), lowerNormal b z) =
      inclusion referenceTriangle (axisPoint referenceTriangle (curveIndex b) z) := by
  rw [fromProduct_coe, toricChartMap_apply, chartCoordinates_symm_lowerNormal]
  rfl

/-- The upper normal frame maps to the original upper toric axis. -/
theorem fromProduct_upperNormal (b : Bool) (z : ℂ) :
    fromProduct ((∞ : RiemannSphere), upperNormal b z) =
      inclusion (upperNeighbour 1) (axisPoint (upperNeighbour 1) (curveIndex b) z) := by
  rw [fromProduct_infty, toricChartMap_apply, chartCoordinates_symm_upperNormal]
  rfl

/-- The lower closed normal representative is exactly the original curve parameter. -/
theorem closedProductMap_lowerNormal (b : Bool) (z : ℂ)
    (hnorm : radiusSq (lowerNormal b z) ≤ closedRadius ^ 2) :
    closedProductMap (((0 : ℂ) : RiemannSphere), ⟨lowerNormal b z, hnorm⟩) =
      CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) := by
  rw [doubleCurve_lower]
  apply congrArg CuspGeometry.inclusion
  apply congrArg (CuspQuotient.quotientMap (CD).correction (CD).radius)
  exact Subtype.ext (fromProduct_lowerNormal b z)

/-- The upper closed normal representative is exactly the original upper axis map. -/
theorem closedProductMap_upperNormal (b : Bool) (z : ℂ)
    (hnorm : radiusSq (upperNormal b z) ≤ closedRadius ^ 2) :
    closedProductMap ((∞ : RiemannSphere), ⟨upperNormal b z, hnorm⟩) =
      CuspGeometry.inclusion
        (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
          (upperNeighbour 1) (curveIndex b) z) := by
  apply congrArg CuspGeometry.inclusion
  apply congrArg (CuspQuotient.quotientMap (CD).correction (CD).radius)
  exact Subtype.ext (fromProduct_upperNormal b z)

/-- The original finite curve parameter has the unchanged upper deck factor. -/
theorem doubleCurve_upper (b : Bool) (z : ℂ) (hz : z ≠ 0) :
    CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) =
      CuspGeometry.inclusion
        (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
          (upperNeighbour 1) (curveIndex b) (kappa b * z⁻¹)) := by
  cases b
  · exact doubleCurve_zero_upper z hz
  · exact doubleCurve_two_upper z hz

/-- The upper finite-parameter normal frame retains the original scale and phase. -/
theorem closedProductMap_upperNormal_finite (b : Bool) (z : ℂ) (hz : z ≠ 0)
    (hnorm : radiusSq (upperNormal b (kappa b * z⁻¹)) ≤ closedRadius ^ 2) :
    closedProductMap ((∞ : RiemannSphere), ⟨upperNormal b (kappa b * z⁻¹), hnorm⟩) =
      CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) := by
  rw [closedProductMap_upperNormal]
  exact (doubleCurve_upper b z hz).symm

/-- The upper origin is the original infinity endpoint of either curve. -/
theorem upper_axis_zero (b : Bool) :
    CuspGeometry.inclusion
        (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
          (upperNeighbour 1) (curveIndex b) 0) =
      CuspGeometry.doubleCurveParametrization (curveIndex b) (∞ : RiemannSphere) := by
  rw [CuspGeometry.doubleCurveParametrization_infty]
  apply congrArg CuspGeometry.inclusion
  rw [CuspQuotient.axisMap_zero, CuspQuotient.centralChartMap_origin_reference,
    upperNeighbour_upper]
  rfl

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
