import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspChart
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspExponential
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspLogCover

/-!
# The three logarithmic curves meeting the reference cusp divisors

The points and vectors below belong to the actual logarithmic cover.
Their images in the reference toric chart are the three coordinate axes
with the other coordinates equal to one. The tangent calculation keeps
the exact normalized exponential factor.
-/

noncomputable section

open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open ToricCharts CuspUniformization CuspFamily

local notation "E₃" => CoordinateSpace 3
local notation "EL" => ℂ × ComplexPlane₂
local notation "K" => (2 * Real.pi * Complex.I : ℂ)

/-- The literal vector point of the logarithmic cover over a logarithmic base point. -/
def logPoint (s : LogBase CuspGeometry.data.radius) (ζ : ComplexPlane₂) : LogDomain :=
  ⟨((s : ℂ), ζ), s.property⟩

@[simp] theorem logPoint_val (s : LogBase CuspGeometry.data.radius) (ζ : ComplexPlane₂) :
    (logPoint s ζ : EL) = ((s : ℂ), ζ) := rfl

/-- The fibre coordinates of the three curves are `0`, `(s,0)`, and `(0,s)`. -/
def logAxisFibre (k : Fin 3) (s : ℂ) : ComplexPlane₂ := ![0, ![s, 0], ![0, s]] k

/-- Their actual constant tangent vectors in the logarithmic coordinates. -/
def logAxisDirection (k : Fin 3) : EL := (1, logAxisFibre k 1)

def logAxisPoint (k : Fin 3) (s : LogBase CuspGeometry.data.radius) : LogDomain :=
  logPoint s (logAxisFibre k s)

@[simp] theorem logAxisPoint_zero (s : LogBase CuspGeometry.data.radius) :
    logAxisPoint 0 s = logPoint s 0 := rfl

/-- Each of the three actual logarithmic curves parametrizes the corresponding toric axis. -/
theorem refExp_logAxisPoint (k : Fin 3) (s : LogBase CuspGeometry.data.radius) :
    refExp (logAxisPoint k s) = axis k (exponential s) := by
  fin_cases k
  · change refExp ((s : ℂ), 0) = _
    rw [refExp_zero_fibre]
    ext j
    fin_cases j <;> simp [axis]
  · change refExp ((s : ℂ), ![(s : ℂ), 0]) = _
    rw [refExp_logCurve_one]
    ext j
    fin_cases j <;> simp [axis]
  · change refExp ((s : ℂ), ![0, (s : ℂ)]) = _
    rw [refExp_logCurve_two]
    ext j
    fin_cases j <;> simp [axis]

/-- The exact tangent pushforward along each curve is `2πi q` times its coordinate vector. -/
theorem refExpDerivative_logAxisPoint (k : Fin 3) (s : LogBase CuspGeometry.data.radius) :
    refExpDerivative (logAxisPoint k s) (logAxisDirection k) =
      (K * exponential s) • (Pi.single k 1 : E₃) := by
  fin_cases k
  · change refExpDerivative ((s : ℂ), 0) (1, 0) = _
    rw [refExpDerivative_base]
    ext j
    fin_cases j <;> simp
  · change refExpDerivative ((s : ℂ), ![(s : ℂ), 0]) (1, ![1, 0]) = _
    rw [refExpDerivative_logCurve_one]
    ext j
    fin_cases j <;> simp
  · change refExpDerivative ((s : ℂ), ![0, (s : ℂ)]) (1, ![0, 1]) = _
    rw [refExpDerivative_logCurve_two]
    ext j
    fin_cases j <;> simp

theorem refExpDerivative_logPoint_base (s : LogBase CuspGeometry.data.radius) :
    refExpDerivative (logPoint s 0) (1, 0) =
      (K * exponential s) • (Pi.single (0 : Fin 3) 1 : E₃) :=
  refExpDerivative_logAxisPoint 0 s

/-- The two fibre columns keep the negative base-coordinate shear and its exact scale. -/
theorem refExpDerivative_logPoint_fibre (s : LogBase CuspGeometry.data.radius) (i : Fin 2) :
    refExpDerivative (logPoint s 0) (0, Pi.single i 1) =
      -(K * exponential s) • (Pi.single (0 : Fin 3) 1 : E₃) +
        K • (Pi.single i.succ 1 : E₃) := by
  rw [refExpDerivative_apply]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [logPoint, refExp, smul_eq_mul]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
