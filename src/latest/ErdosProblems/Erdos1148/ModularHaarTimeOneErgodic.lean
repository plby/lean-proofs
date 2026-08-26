import ErdosProblems.Erdos1148.ModularL2Action
import ErdosProblems.Erdos1148.ModularHaarErgodicAction
import ErdosProblems.Erdos1148.ModularTimeOne
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Ergodicity of diagonal time one for the modular Haar probability -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure Filter
open scoped MatrixGroups ENNReal

lemma modularL2_smul_indicator (g : SL(2, ℝ)) {U : Set ModularOrbitSpace}
    (hU : MeasurableSet U) :
    g • indicatorConstLp 2 hU (measure_ne_top normalizedModularHaarMeasure U) (1 : ℝ) =
      indicatorConstLp 2 (hU.preimage (continuous_modularRightTranslate g).measurable)
        (measure_ne_top normalizedModularHaarMeasure _) (1 : ℝ) := rfl

lemma modularL2_indicator_fixed_iff (g : SL(2, ℝ)) {U : Set ModularOrbitSpace}
    (hU : MeasurableSet U) :
    g • indicatorConstLp 2 hU (measure_ne_top normalizedModularHaarMeasure U) (1 : ℝ) =
      indicatorConstLp 2 hU (measure_ne_top normalizedModularHaarMeasure U) (1 : ℝ) ↔
      (modularRightTranslate g) ⁻¹' U =ᵐ[normalizedModularHaarMeasure] U := by
  rw [modularL2_smul_indicator]
  exact indicatorConstLp_inj _ _ _ _ one_ne_zero

theorem normalizedModularHaarMeasure_time_one_ergodic :
    Ergodic modularTimeOne normalizedModularHaarMeasure := by
  refine ⟨measurePreserving_modularRightTranslate (diagonalFlow 1), ⟨?_⟩⟩
  intro U hU hinv
  have hf : diagonalFlow 1 • indicatorConstLp 2 hU
      (measure_ne_top normalizedModularHaarMeasure U) (1 : ℝ) =
      indicatorConstLp 2 hU (measure_ne_top normalizedModularHaarMeasure U) (1 : ℝ) :=
    (modularL2_indicator_fixed_iff (diagonalFlow 1) hU).mpr (.of_eq hinv)
  apply normalizedModularHaarMeasure_aeconst_of_right_invariant hU
  intro g
  exact (modularL2_indicator_fixed_iff g hU).mp (modularL2_fixed_of_time_one_fixed hf g)

end Erdos1148.DukeArithmetic
