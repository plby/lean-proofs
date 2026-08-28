import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelQuotient
import Wikipedia.HopfProblem.CuspPositiveRetractionPhases

/-!
# Compensated phase rotation of the actual central cusp presentation

An ordinary rotation of the base phase does not descend through the cusp
deck transformations.  The two displayed planar phase factors compensate
for the integral shear in their compact-torus normalizer.  At a full turn
the base phase is again one, and the remaining map is the integral
unipotent shear on the free phase-plane source.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspCollapse CuspHoneycomb CuspHoneycombTiling CuspPositive

local notation "Plane" => CuspHoneycombTiling.Plane

theorem circle_exp_two_pi : Circle.exp (2 * Real.pi) = 1 := by
  apply Circle.ext
  simpa only [Circle.coe_exp, Circle.coe_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using Complex.exp_two_pi_mul_I

/-- The two integral characters of the actual honeycomb plane. -/
def planarPhase (y : Plane) : CompactFibreTorus :=
  fun i => Circle.exp (2 * Real.pi * y i)

theorem planarPhase_continuous : Continuous planarPhase := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (continuous_const.mul (continuous_apply i))

theorem circle_exp_add_integer (a y : ℝ) (n : ℤ) :
    Circle.exp (a * (y + n)) = Circle.exp (a * y) * Circle.exp a ^ n := by
  rw [mul_add, Circle.exp_add]
  congr 1
  rw [mul_comm, Circle.exp_intCast_mul]

@[simp] theorem planarPhase_latticePoint (v : Fin 2 → ℤ) :
    planarPhase (latticePoint v) = 1 := by
  funext i
  change Circle.exp (2 * Real.pi * (v i : ℝ)) = 1
  rw [mul_comm, Circle.exp_intCast_mul, circle_exp_two_pi, one_zpow]

theorem planarPhase_add_latticePoint (y : Plane) (v : Fin 2 → ℤ) :
    planarPhase (y + latticePoint v) = planarPhase y := by
  funext i
  change Circle.exp (2 * Real.pi * (y i + (v i : ℝ))) = _
  rw [circle_exp_add_integer, circle_exp_two_pi, one_zpow, mul_one]
  rfl

/-- The compensating compact-three-torus element, with a rotating base phase. -/
def compensatingPhase (r : ℝ) (p : PhasePlane) : CompactTorus :=
  ![p.1 0 * Circle.exp (2 * Real.pi * r * p.2 0),
    p.1 1 * Circle.exp (2 * Real.pi * r * p.2 1),
    Circle.exp (2 * Real.pi * r)]

theorem compensatingPhase_continuous :
    Continuous (fun p : ℝ × PhasePlane => compensatingPhase p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [compensatingPhase] <;> fun_prop

@[simp] theorem compensatingPhase_zero (p : PhasePlane) :
    compensatingPhase 0 p = compactFibrePhase p.1 := by
  funext i
  fin_cases i <;> simp [compensatingPhase, compactFibrePhase]

@[simp] theorem compensatingPhase_one (p : PhasePlane) :
    compensatingPhase 1 p = compactFibrePhase (p.1 * planarPhase p.2) := by
  funext i
  fin_cases i <;> simp [compensatingPhase, compactFibrePhase, planarPhase, circle_exp_two_pi]

/-- Exact covariance with the original compact normalizer, not just with
the diagonal fibre phases.  It is this identity that makes the intermediate
base rotations descend on the central cusp quotient. -/
theorem compensatingPhase_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (r : ℝ) (p : PhasePlane) :
    compensatingPhase r (honeycombDeckMap C₀ v p) =
      phaseTransform C₀ v (compensatingPhase r p) := by
  funext i
  fin_cases i
  · change (deckFibrePhase C₀ v 0 * p.1 0) *
        Circle.exp (2 * Real.pi * r * (p.2 0 + (cuspVector v 0 : ℝ))) =
      frozenPhaseCoordinate C₀ v 0 *
        ((p.1 0 * Circle.exp (2 * Real.pi * r * p.2 0)) *
          Circle.exp (2 * Real.pi * r) ^ cuspVector v 0)
    rw [circle_exp_add_integer]
    simp only [deckFibrePhase, mul_assoc]
  · change (deckFibrePhase C₀ v 1 * p.1 1) *
        Circle.exp (2 * Real.pi * r * (p.2 1 + (cuspVector v 1 : ℝ))) =
      frozenPhaseCoordinate C₀ v 1 *
        ((p.1 1 * Circle.exp (2 * Real.pi * r * p.2 1)) *
          Circle.exp (2 * Real.pi * r) ^ cuspVector v 1)
    rw [circle_exp_add_integer]
    simp only [deckFibrePhase, mul_assoc]
  · simp [compensatingPhase, phaseTransform, frozenPhase, phaseShear]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
