import ErdosProblems.Erdos1002.MarkedResonances
import ErdosProblems.Erdos1002.ShotLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The marked-point shot functional

The finite-shot limit is obtained by applying the function `V(u) / x` to
the marked resonance points.  This file proves the corresponding identity
for the finite sums exactly.  In particular, the primitive-resonance
indicator, the cutoff, and the convention at `x = 0` are all retained.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

local instance markedShotFunctionalPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The jump contributed by a marked point `(t,x,u)`.  Lean's total division
sets the value to zero when `x = 0`, matching the manuscript's convention. -/
def markedShotKernel (z : ℝ × ℝ × ℝ) : ℝ :=
  bernoulliMark z.2.2 / z.2.1

theorem measurable_markedShotKernel : Measurable markedShotKernel := by
  exact (bernoulliMark_measurable.comp (measurable_snd.comp measurable_snd)).div
    (measurable_fst.comp measurable_snd)

/-- The only possible discontinuity of the marked shot kernel is its stated
singular hyperplane `x = 0`. -/
theorem continuousAt_markedShotKernel
    {z : ℝ × ℝ × ℝ} (hz : z.2.1 ≠ 0) :
    ContinuousAt markedShotKernel z := by
  unfold markedShotKernel
  exact (continuous_bernoulliMark.comp
      (continuous_snd.comp continuous_snd)).continuousAt.div
    ((continuous_fst.comp continuous_snd).continuousAt) hz

theorem continuousOn_markedShotKernel_away_zero :
    ContinuousOn markedShotKernel {z : ℝ × ℝ × ℝ | z.2.1 ≠ 0} := by
  intro z hz
  exact (continuousAt_markedShotKernel hz).continuousWithinAt

@[simp]
theorem markedShotKernel_of_second_eq_zero
    (t u : ℝ) : markedShotKernel (t, 0, u) = 0 := by
  simp [markedShotKernel]

/-- Evaluation of the marked kernel at one resonance point, before imposing
primitivity. -/
theorem markedShotKernel_markedResonancePoint
    (N p : ℕ) (α : ℝ) :
    markedShotKernel (markedResonancePoint N p α) =
      bernoulliMark ((N : ℝ) * resonanceDelta p α) /
        (Real.log (N : ℝ) * (p : ℝ) * resonanceDelta p α) := by
  rw [markedShotKernel, markedResonancePoint]
  change bernoulliMark (resonanceTorusCoordinate N p α) /
      scaledResonanceCoordinate N p α = _
  rw [bernoulliMark_resonanceTorusCoordinate]
  rfl

/-- The normalized primitive shot is exactly the marked-point kernel when
the nearest rational cell is primitive, and is zero otherwise. -/
theorem primitiveShot_div_log_eq_markedShotKernel
    (N p : ℕ) (α : ℝ) :
    primitiveShot N p α / Real.log (N : ℝ) =
      if IsPrimitiveResonance p α then
        markedShotKernel (markedResonancePoint N p α)
      else 0 := by
  by_cases hprim : IsPrimitiveResonance p α
  · rw [if_pos hprim, primitiveShot_of_primitive N p α hprim,
      markedShotKernel_markedResonancePoint]
    simp only [div_eq_mul_inv]
    ring
  · rw [if_neg hprim, primitiveShot_of_not_primitive N p α hprim]
    simp

/-- The literal marked-point representation of the retained finite shot
sum.  Keeping this as a finite sum avoids any hidden convention about point
measures or multiplicities. -/
def markedFiniteShotFunctional (N : ℕ) (A : ℝ) (α : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 N,
    if IsPrimitiveResonance p α ∧
        |scaledResonanceCoordinate N p α| ≤ A then
      markedShotKernel (markedResonancePoint N p α)
    else 0

theorem measurable_markedFiniteShotFunctional (N : ℕ) (A : ℝ) :
    Measurable (markedFiniteShotFunctional N A) := by
  classical
  unfold markedFiniteShotFunctional
  apply Finset.measurable_fun_sum
  intro p _hp
  apply Measurable.ite
  · exact (measurableSet_isPrimitiveResonance p).inter
      (measurableSet_le (measurable_scaledResonanceCoordinate N p).abs
        measurable_const)
  · exact measurable_markedShotKernel.comp (measurable_markedResonancePoint N p)
  · exact measurable_const

/-- Exact finite-sum bridge between the manuscript's normalized resonance
shots and its marked point process. -/
theorem normalizedFiniteResonanceShotSum_eq_markedFiniteShotFunctional
    (N : ℕ) (A : ℝ) (α : ℝ) :
    normalizedFiniteResonanceShotSum N A α =
      markedFiniteShotFunctional N A α := by
  classical
  rw [normalizedFiniteResonanceShotSum, finiteResonanceShotSum,
    Finset.sum_div]
  unfold markedFiniteShotFunctional
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hcut : |scaledResonanceCoordinate N p α| ≤ A
  · rw [if_pos hcut]
    by_cases hprim : IsPrimitiveResonance p α
    · rw [if_pos ⟨hprim, hcut⟩,
        primitiveShot_div_log_eq_markedShotKernel, if_pos hprim]
    · rw [if_neg (fun h ↦ hprim h.1),
        primitiveShot_div_log_eq_markedShotKernel, if_neg hprim]
  · rw [if_neg hcut, zero_div, if_neg (fun h ↦ hcut h.2)]

/-- Away from the singular coordinate, the elementary sharp bound
`|V(u)/x| ≤ (1/8)/|x|` holds. -/
theorem abs_markedShotKernel_le (z : ℝ × ℝ × ℝ) :
    |markedShotKernel z| ≤ (1 / 8 : ℝ) / |z.2.1| := by
  rw [markedShotKernel, abs_div]
  exact div_le_div_of_nonneg_right
    (abs_bernoulliMark_le_one_eighth z.2.2) (abs_nonneg z.2.1)

/-- Uniform boundedness on a truncated state-space strip. -/
theorem abs_markedShotKernel_le_of_le_abs
    {ε : ℝ} (hε : 0 < ε) (z : ℝ × ℝ × ℝ)
    (hz : ε ≤ |z.2.1|) :
    |markedShotKernel z| ≤ (1 / 8 : ℝ) / ε := by
  calc
    |markedShotKernel z| ≤ (1 / 8 : ℝ) / |z.2.1| :=
      abs_markedShotKernel_le z
    _ ≤ (1 / 8 : ℝ) / ε := by
      exact div_le_div_of_nonneg_left (by norm_num) hε hz

end

end Erdos1002
