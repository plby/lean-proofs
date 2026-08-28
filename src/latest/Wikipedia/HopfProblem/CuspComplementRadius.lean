import Wikipedia.HopfProblem.CuspCircleNormalTrivializationClosedDisk

/-!
# A fixed outer cusp level separated from the deleted normal disk

The original compact normal disk lies strictly below half the actual
cusp filling radius.  The estimate uses the literal cubic toric time
and the already chosen injective normal radius; no further shrinking
or change of the frozen normal neighborhood is made.
-/

noncomputable section

open Set Topology
open scoped ContDiff OnePoint

namespace Wikipedia.HopfProblem.CuspComplement

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

local notation "CD" => CuspGeometry.data

/-- The outer level is fixed in the original cusp coordinate. -/
def capRadius : ℝ := (CD).radius / 2

theorem capRadius_pos : 0 < capRadius := half_pos (CD).radius_pos

theorem capRadius_lt_cuspRadius : capRadius < (CD).radius :=
  half_lt_self (CD).radius_pos

/-- Testing the diagonal normal vector gives a uniform strict margin
between the unchanged compact disk and the chosen outer cusp level. -/
theorem closedRadius_sq_lt_two_cuspRadius :
    closedRadius ^ 2 < 2 * (CD).radius := by
  let v : Fibre := ((closedRadius : ℂ), (closedRadius : ℂ))
  have hv : ‖v‖ < injectiveRadius := by
    simpa only [v, Prod.norm_def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos closedRadius_pos, max_self] using closedRadius_lt_injectiveRadius
  have hp : (((0 : ℂ) : RiemannSphere), v) ∈ smallNormalProduct :=
    injectiveRadius_product_subset
    ⟨show ((0 : ℂ) : RiemannSphere) ∈ (univ : Set RiemannSphere) from mem_univ _,
      show v ∈ Metric.ball (0 : Fibre) injectiveRadius from
        by simpa only [Metric.mem_ball, dist_zero_right] using hv⟩
  change radiusSq v < 4 * (CD).radius at hp
  simp only [radiusSq, v, Complex.normSq_ofReal] at hp
  nlinarith only [hp]

/-- The two original toric charts give the same global time bound. -/
theorem fromProduct_time_bound (p : RiemannSphere × Fibre) :
    4 * ‖ToricSpace.time (fromProduct p)‖ ≤ radiusSq p.2 := by
  obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
  rw [fromProduct_baseProductChart]
  exact chartParameters_time_bound b q

/-- The global cusp coordinate is still the original toric monomial. -/
@[simp] theorem cuspCoordinate_globalProductMap (p : smallNormalProduct) :
    CuspGeometry.cuspCoordinate (globalProductMap p) =
      ToricSpace.time (fromProduct (p : RiemannSphere × Fibre)) := by
  exact CuspGeometry.cuspCoordinate_inclusion _

/-- The unchanged compact normal-disk map has a uniform original-time bound. -/
theorem closedProductMap_time_bound (p : ClosedNormalProduct) :
    4 * ‖CuspGeometry.cuspCoordinate (closedProductMap p)‖ ≤ closedRadius ^ 2 := by
  change 4 * ‖CuspGeometry.cuspCoordinate
    (globalProductMap (roundToSmall (closedProductIntoRound p)))‖ ≤ _
  rw [cuspCoordinate_globalProductMap]
  exact (fromProduct_time_bound (p.1, p.2.val)).trans p.2.property

theorem closedProductMap_time_lt_capRadius (p : ClosedNormalProduct) :
    ‖CuspGeometry.cuspCoordinate (closedProductMap p)‖ < capRadius := by
  have h := closedProductMap_time_bound p
  have hr := closedRadius_sq_lt_two_cuspRadius
  change ‖CuspGeometry.cuspCoordinate (closedProductMap p)‖ < (CD).radius / 2
  linarith only [h, hr]

/-- Every point of the already fixed compact normal neighborhood is
strictly inside the specified actual cusp level. -/
theorem closedDiskNeighborhood_time_lt_capRadius {x : Threefold.Space}
    (hx : x ∈ closedDiskNeighborhood) :
    ‖CuspGeometry.cuspCoordinate x‖ < capRadius := by
  obtain ⟨p, rfl⟩ := hx
  exact closedProductMap_time_lt_capRadius p

end Wikipedia.HopfProblem.CuspComplement
