import Wikipedia.HopfProblem.CuspRetractionTorus
import Wikipedia.HopfProblem.CuspRetractionDisplacement
import Wikipedia.HopfProblem.CuspQuotient

/-!
# The actual change of cusp twist

This is the explicit map of Lemma 7.5, with the target twist temporarily
allowed to vary.  No quotient or complex structure is transported to
define it: it acts by a fibre-torus multiplier on the glued toric space.
The source's straightening is the specialization to the constant twist
`C(0)`.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricFan ToricSpace

variable (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

def frozen (_t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := C 0

@[simp] theorem frozen_apply (t : ℂ) : frozen C t = C 0 := rfl

/-- The logarithmic correction in the exponential multiplier. -/
def correction (x : Space) : Fin 2 → ℂ :=
  (D (time x) - C (time x)) *ᵥ
    realToComplex (inverseDisplacement C (time x) (position x))

/-- The map changes a `C`-twist into a `D`-twist.  Lemma 7.5 uses
`D = frozen C`; this specializes the sign to `-(C(t)-C(0))`. -/
def changeTwist (x : Space) : Space := expFibreAction (correction C D x) x

@[simp] theorem time_changeTwist (x : Space) : time (changeTwist C D x) = time x :=
  time_expFibreAction _ _

@[simp] theorem correction_of_time_zero {x : Space} (hx : time x = 0) :
    correction C D x = 0 := by
  rw [correction, position_of_time_zero hx, map_zero, map_zero, Matrix.mulVec_zero]

@[simp] theorem changeTwist_of_time_zero {x : Space} (hx : time x = 0) :
    changeTwist C D x = x := by
  rw [changeTwist, correction_of_time_zero C D hx, expFibreAction_zero]

@[simp] theorem correction_self (x : Space) : correction C C x = 0 := by
  simp only [correction, sub_self, Matrix.zero_mulVec]

@[simp] theorem changeTwist_self (x : Space) : changeTwist C C x = x := by
  rw [changeTwist, correction_self, expFibreAction_zero]

def tubeChangeTwist (ε : ℝ) (x : Tube (CuspQuotient.disc ε)) :
    Tube (CuspQuotient.disc ε) :=
  ⟨changeTwist C D x, by
    change time (changeTwist C D x) ∈ CuspQuotient.disc ε
    rw [time_changeTwist]
    exact x.2⟩

@[simp] theorem tubeChangeTwist_coe (ε : ℝ) (x : Tube (CuspQuotient.disc ε)) :
    (tubeChangeTwist C D ε x : Space) = changeTwist C D x := rfl

/-- The closed sub-tube occurring in Proposition 7.2. -/
abbrev ClosedTube (η : ℝ) := {x : Space // ‖time x‖ ≤ η}

def closedTubeChangeTwist (η : ℝ) (x : ClosedTube η) : ClosedTube η :=
  ⟨changeTwist C D x, by
    rw [time_changeTwist]
    exact x.2⟩

@[simp] theorem closedTubeChangeTwist_coe (η : ℝ) (x : ClosedTube η) :
    (closedTubeChangeTwist C D η x : Space) = changeTwist C D x := rfl

end Wikipedia.HopfProblem.CuspRetraction
