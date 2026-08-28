import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCusp
import Wikipedia.HopfProblem.CuspPuncturedBasic

/-!
# Literal exponential-coordinate formulas for the cusp vertical flow

On the open torus the extended flow multiplies exactly the second fibre
coordinate by `exp (2π i s)`.  On the original logarithmic cover it is
translation by `s (0,1)` in the fibre coordinates.  These identities are
equalities of the actual toric and cusp-quotient maps, so they can be used
directly in the analytic gluing overlaps.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp

open ToricCharts ToricFan ToricSpace CuspUniformization

/-- Multiplication on torus representatives is the actual extended toric action. -/
theorem torusAction_torusPoint (u : ActingTorus) (w : CoordinateSpace 3) :
    torusAction u (torusPoint w) = torusPoint (fun j => (u j : ℂ) * w j) := by
  change torusAction u (inclusion referenceTriangle (monomial referenceTriangle.dual w)) =
    inclusion referenceTriangle
      (monomial referenceTriangle.dual ((fun j => (u j : ℂ)) * w))
  rw [torusAction_inclusion, monomial_mul]
  rfl

/-- The literal open-orbit formula: only the second fibre torus coordinate changes. -/
theorem toricFlow_torusPoint (s : ℂ) (w : CoordinateSpace 3) :
    toricFlow s (torusPoint w) =
      torusPoint ![w 0, exponential s * w 1, w 2] := by
  rw [toricFlow, torusAction_torusPoint]
  apply congrArg torusPoint
  ext i
  fin_cases i <;> simp [multiplier, fibreMultiplier, exponential]

/-- The genuine extended toric flow lifts to the constant vertical translation. -/
theorem toricFlow_exponentialPoint (s t : ℂ) (z : ComplexPlane₂) :
    toricFlow s (exponentialPoint t z) =
      exponentialPoint t (z + s • (![0, 1] : ComplexPlane₂)) := by
  change toricFlow s (torusPoint (exponentialCoordinates t z)) =
    torusPoint (exponentialCoordinates t (z + s • (![0, 1] : ComplexPlane₂)))
  rw [toricFlow_torusPoint]
  apply congrArg torusPoint
  ext i
  fin_cases i <;> simp [exponentialCoordinates, exponential_add, mul_comm]

/-- The literal vertical translation on the original full logarithmic cusp cover. -/
def logFlow (ε : ℝ) (s : ℂ) (p : LogCover ε) : LogCover ε :=
  ⟨(p.val.1, p.val.2 + s • (![0, 1] : ComplexPlane₂)), p.property⟩

@[simp] theorem logFlow_coe (ε : ℝ) (s : ℂ) (p : LogCover ε) :
    (logFlow ε s p : ℂ × ComplexPlane₂) =
      (p.val.1, p.val.2 + s • (![0, 1] : ComplexPlane₂)) := rfl

theorem toricFlow_totalExponentialPoint (s : ℂ) (p : ℂ × ComplexPlane₂) :
    toricFlow s (totalExponentialPoint p) =
      totalExponentialPoint (p.1, p.2 + s • (![0, 1] : ComplexPlane₂)) :=
  toricFlow_exponentialPoint s (exponential p.1) p.2

theorem tubeFlow_totalExponentialLift (ε : ℝ) (s : ℂ) (p : LogCover ε) :
    tubeFlow (CuspQuotient.disc ε) s (totalExponentialLift ε p) =
      totalExponentialLift ε (logFlow ε s p) :=
  Subtype.ext (toricFlow_totalExponentialPoint s p)

/-- On actual quotient representatives the cusp action is exactly the
constant vertical translation used on the regular family. -/
theorem flow_totalCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (p : LogCover ε) :
    flow C ε s (totalCuspCover C ε p) = totalCuspCover C ε (logFlow ε s p) := by
  change CuspQuotient.quotientMap C ε
    (tubeFlow (CuspQuotient.disc ε) s (totalExponentialLift ε p)) = _
  rw [tubeFlow_totalExponentialLift]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp
