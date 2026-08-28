import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansBased
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansElliptic
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansCusp

/-!
# Actual elliptic and cusp meridians of the regular triangle quotient

The loops below are the projections of the explicit Cayley arcs and
horizontal cusp segments.  Their local coordinates are literal circles
with phase `2πt`, or `-2πt` after reversal.  The chart-source statements
ensure that these are formulas in actual quotient charts throughout the
loop.  Their lifted endpoints follow from the actual quotient covering.

The source uses clockwise meridians.  We keep those names separate from
the counterclockwise loops, and do not identify forward transport with
the source's inverse-transport convention.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle

/-- A small positive elliptic meridian in the actual regular quotient. -/
def ellipticCCWMeridian (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Path (triangleRegularProject (ellipticBasePoint j r hr hr1))
      (triangleRegularProject (ellipticBasePoint j r hr hr1)) :=
  projectLift (ellipticBasePoint j r hr hr1) (ellipticGenerator j)
    (ellipticCCWLift j r hr hr1)

/-- The source's clockwise elliptic meridian, with literal reversed orientation. -/
def ellipticCWMeridian (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Path (triangleRegularProject (ellipticBasePoint j r hr hr1))
      (triangleRegularProject (ellipticBasePoint j r hr hr1)) :=
  (ellipticCCWMeridian j r hr hr1).symm

@[simp] theorem ellipticCCWMeridian_apply (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    ellipticCCWMeridian j r hr hr1 t =
      triangleRegularProject (ellipticCCWLift j r hr hr1 t) := rfl

theorem ellipticCCWMeridian_chart_source (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    triangleRegularToOrbit (ellipticCCWMeridian j r hr hr1 t) ∈
      (ellipticFullChart j).source :=
  ellipticCCWLift_projection_mem_source j r hr hr1 t

theorem ellipticCCWMeridian_chart (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    ellipticFullChart j (triangleRegularToOrbit (ellipticCCWMeridian j r hr hr1 t)) =
      (r : ℂ) ^ j.order * turn (t : ℝ) :=
  ellipticCCWLift_fullChart j r hr hr1 t

/-- Negative phase certifies the clockwise orientation in the actual
holomorphic elliptic quotient coordinate. -/
theorem ellipticCWMeridian_chart (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    ellipticFullChart j (triangleRegularToOrbit (ellipticCWMeridian j r hr hr1 t)) =
      (r : ℂ) ^ j.order * turn (-(t : ℝ)) := by
  change ellipticFullChart j
    (triangleRegularToOrbit (ellipticCCWMeridian j r hr hr1 (unitInterval.symm t))) = _
  rw [ellipticCCWMeridian_chart, unitInterval.coe_symm_eq, turn_one_sub]

theorem ellipticCCWMeridian_chart_norm (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    ‖ellipticFullChart j (triangleRegularToOrbit (ellipticCCWMeridian j r hr hr1 t))‖ =
      r ^ j.order := by
  rw [ellipticCCWMeridian_chart, norm_mul, norm_pow, norm_turn, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

theorem ellipticCCWMeridian_chart_ne_zero (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    ellipticFullChart j (triangleRegularToOrbit (ellipticCCWMeridian j r hr hr1 t)) ≠ 0 := by
  rw [ellipticCCWMeridian_chart]
  exact mul_ne_zero (pow_ne_zero j.order (Complex.ofReal_ne_zero.mpr hr.ne')) (turn_ne_zero _)

/-- The specified fractional Cayley arc is the actual full covering lift. -/
theorem ellipticCCWMeridian_liftPath (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    triangleRegularProject_covering.isCoveringMap.liftPath (ellipticCCWMeridian j r hr hr1)
      (ellipticBasePoint j r hr hr1) (ellipticCCWMeridian j r hr hr1).source =
        (ellipticCCWLift j r hr hr1).toContinuousMap :=
  projectLift_liftPath _ _ _

theorem ellipticCCWMeridian_monodromy (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (ellipticCCWMeridian j r hr hr1))
      ⟨ellipticBasePoint j r hr hr1, rfl⟩ : TriangleRegularPoint) =
        (ellipticGenerator j)⁻¹ • ellipticBasePoint j r hr hr1 :=
  congrArg Subtype.val (projectLift_monodromy _ _ _)

theorem ellipticCWMeridian_monodromy (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (ellipticCWMeridian j r hr hr1))
      ⟨ellipticBasePoint j r hr hr1, rfl⟩ : TriangleRegularPoint) =
        ellipticGenerator j • ellipticBasePoint j r hr hr1 :=
  projectLift_symm_monodromy _ _ _

/-- A positive cusp meridian in the actual regular quotient. -/
def cuspCCWMeridian (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    Path (triangleRegularProject (cuspBasePoint Y hY z))
      (triangleRegularProject (cuspBasePoint Y hY z)) :=
  projectLift (cuspBasePoint Y hY z) triangleCuspGenerator (cuspCCWLift Y hY z)

/-- The source's clockwise cusp meridian. -/
def cuspCWMeridian (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    Path (triangleRegularProject (cuspBasePoint Y hY z))
      (triangleRegularProject (cuspBasePoint Y hY z)) :=
  (cuspCCWMeridian Y hY z).symm

@[simp] theorem cuspCCWMeridian_apply (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) (t : unitInterval) :
    cuspCCWMeridian Y hY z t = triangleRegularProject (cuspCCWLift Y hY z t) := rfl

theorem cuspCCWMeridian_chart_source (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) (t : unitInterval) :
    triangleOpenInclusion (triangleRegularToOrbit (cuspCCWMeridian Y hY z t)) ∈
      (cuspFullChart Y hY).source :=
  cuspCCWLift_chart_source Y hY z t

theorem cuspCCWMeridian_chart (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) (t : unitInterval) :
    cuspFullChart Y hY
      (triangleOpenInclusion (triangleRegularToOrbit (cuspCCWMeridian Y hY z t))) =
      cuspQ (z : ℍ) * turn (t : ℝ) :=
  cuspCCWLift_chart Y hY z t

/-- The negative exponential phase is the actual clockwise cusp coordinate. -/
theorem cuspCWMeridian_chart (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) (t : unitInterval) :
    cuspFullChart Y hY
      (triangleOpenInclusion (triangleRegularToOrbit (cuspCWMeridian Y hY z t))) =
      cuspQ (z : ℍ) * turn (-(t : ℝ)) := by
  change cuspFullChart Y hY
    (triangleOpenInclusion
      (triangleRegularToOrbit (cuspCCWMeridian Y hY z (unitInterval.symm t)))) = _
  rw [cuspCCWMeridian_chart, unitInterval.coe_symm_eq, turn_one_sub]

theorem cuspCCWMeridian_chart_norm (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) (t : unitInterval) :
    ‖cuspFullChart Y hY
      (triangleOpenInclusion (triangleRegularToOrbit (cuspCCWMeridian Y hY z t)))‖ =
      ‖cuspQ (z : ℍ)‖ :=
  cuspCCWLift_chart_norm Y hY z t

theorem cuspCCWMeridian_chart_ne_zero (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) (t : unitInterval) :
    cuspFullChart Y hY
      (triangleOpenInclusion (triangleRegularToOrbit (cuspCCWMeridian Y hY z t))) ≠ 0 :=
  cuspCCWLift_chart_ne_zero Y hY z t

/-- The horizontal segment is the actual full covering lift of this loop. -/
theorem cuspCCWMeridian_liftPath (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    triangleRegularProject_covering.isCoveringMap.liftPath (cuspCCWMeridian Y hY z)
      (cuspBasePoint Y hY z) (cuspCCWMeridian Y hY z).source =
        (cuspCCWLift Y hY z).toContinuousMap :=
  projectLift_liftPath _ _ _

theorem cuspCCWMeridian_monodromy (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (cuspCCWMeridian Y hY z))
      ⟨cuspBasePoint Y hY z, rfl⟩ : TriangleRegularPoint) =
        triangleCuspGenerator⁻¹ • cuspBasePoint Y hY z :=
  congrArg Subtype.val (projectLift_monodromy _ _ _)

theorem cuspCWMeridian_monodromy (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (cuspCWMeridian Y hY z))
      ⟨cuspBasePoint Y hY z, rfl⟩ : TriangleRegularPoint) =
        triangleCuspGenerator • cuspBasePoint Y hY z :=
  projectLift_symm_monodromy _ _ _

/-- The specified positive elliptic meridian with a chosen tail to a
common base point.  Its local circle is unchanged. -/
def basedEllipticCCWMeridian (b : TriangleRegularPoint) (j : Elliptic.Kind)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Path (triangleRegularProject b) (triangleRegularProject b) :=
  basedLoop b (ellipticBasePoint j r hr hr1) (ellipticGenerator j)
    (ellipticCCWLift j r hr hr1)

/-- The specified positive cusp meridian with a chosen tail to the same
arbitrary regular base point. -/
def basedCuspCCWMeridian (b : TriangleRegularPoint) (Y : ℝ)
    (hY : width ≤ Y) (z : horodisc Y) :
    Path (triangleRegularProject b) (triangleRegularProject b) :=
  basedLoop b (cuspBasePoint Y hY z) triangleCuspGenerator (cuspCCWLift Y hY z)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
