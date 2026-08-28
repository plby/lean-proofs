import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexPhase
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Pointwise choice of an angle for a nonzero complex level

The principal argument is used only to choose a real lift for one fixed
time.  No continuous argument on the punctured disc is asserted or used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

/-- A pointwise real lift of the base phase, measured in turns. -/
def argumentTurns (t : ℂ) : ℝ := t.arg / (2 * Real.pi)

/-- Norm and the chosen argument recover the exact original complex time. -/
theorem rotatedLevel_norm_argumentTurns (t : ℂ) :
    rotatedLevel ‖t‖ (argumentTurns t) = t := by
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have he : 2 * Real.pi * (t.arg / (2 * Real.pi)) = t.arg :=
    mul_div_cancel₀ t.arg hπ
  rw [rotatedLevel, argumentTurns, he, Circle.coe_exp, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I t

/-- Every nonzero level has positive radius and a real angle in the model. -/
theorem exists_rotatedLevel (t : ℂ) (ht : t ≠ 0) :
    ∃ (ρ : ℝ) (_ : 0 < ρ) (r : ℝ), rotatedLevel ρ r = t :=
  ⟨‖t‖, norm_pos_iff.mpr ht, argumentTurns t, rotatedLevel_norm_argumentTurns t⟩

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
