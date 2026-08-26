import ErdosProblems.Erdos1002.Sawtooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary finite facts for Erdős Problem 1002

This file establishes the measurability and basic measure bounds needed
before any limiting argument.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1002

noncomputable section

theorem measurable_rotationSum (N : ℕ) : Measurable (rotationSum N) := by
  classical
  unfold rotationSum
  exact Finset.measurable_fun_sum (Finset.Icc 1 N) fun k _ =>
    sawtooth_measurable.comp (measurable_const.mul measurable_id)

theorem measurable_normalizedRotationSum (N : ℕ) :
    Measurable (normalizedRotationSum N) := by
  exact (measurable_rotationSum N).div_const _

theorem measurableSet_distributionEvent (N : ℕ) (c : ℝ) :
    MeasurableSet
      {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α ≤ c} := by
  exact measurableSet_Ioo.inter
    (measurableSet_le (measurable_normalizedRotationSum N) measurable_const)

theorem volume_distributionEvent_le_one (N : ℕ) (c : ℝ) :
    volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α ≤ c} ≤ 1 := by
  calc
    volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α ≤ c}
        ≤ volume (Ioo (0 : ℝ) 1) := measure_mono fun _ hα => hα.1
    _ = 1 := by simp

theorem distributionValue_nonneg (N : ℕ) (c : ℝ) :
    0 ≤ distributionValue N c := by
  exact ENNReal.toReal_nonneg

theorem distributionValue_le_one (N : ℕ) (c : ℝ) :
    distributionValue N c ≤ 1 := by
  rw [distributionValue, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono (by simp) (volume_distributionEvent_le_one N c)

theorem distributionValue_mono {N : ℕ} : Monotone (distributionValue N) := by
  intro c d hcd
  unfold distributionValue
  apply ENNReal.toReal_mono
  · exact ne_of_lt
      (lt_of_le_of_lt (volume_distributionEvent_le_one N d) ENNReal.one_lt_top)
  · apply measure_mono
    intro α hα
    exact ⟨hα.1, hα.2.trans hcd⟩

end

end Erdos1002
