import ErdosProblems.Erdos1148.SpecialLinearCharacters
import ErdosProblems.Erdos1148.ModularTopology
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Left Haar measure on SL(2,R) is also right invariant -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups

instance realSpecialLinearMeasurableSpace : MeasurableSpace SL(2, ℝ) := borel SL(2, ℝ)

instance realSpecialLinearBorelSpace : BorelSpace SL(2, ℝ) := ⟨rfl⟩

theorem specialLinear_modularCharacter_eq_one (g : SL(2, ℝ)) :
    Measure.modularCharacterFun g = 1 :=
  specialLinear_commMonoidHom_eq_one Measure.modularCharacter g

theorem specialLinear_haar_map_right (μ : Measure SL(2, ℝ)) [IsHaarMeasure μ]
    [μ.InnerRegular] (g : SL(2, ℝ)) : Measure.map (fun h => h * g) μ = μ := by
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    specialLinear_modularCharacter_eq_one, one_smul]

end Erdos1148.DukeArithmetic
