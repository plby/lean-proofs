import ErdosProblems.Erdos1002.Sawtooth
import ErdosProblems.Erdos1002.Resonances

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Primitive resonance shots

This file gives literal Lean definitions of the manuscript's primitive shot
sum.  Lean's division operation is total and returns zero at a zero
denominator; because `V(0)=0`, this agrees exactly with the paper's stated
zero-at-resonance convention.
-/

open Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- The `p`-th primitive shot. -/
def primitiveShot (N p : ℕ) (α : ℝ) : ℝ :=
  if IsPrimitiveResonance p α then
    bernoulliMark ((N : ℝ) * resonanceDelta p α) /
      ((p : ℝ) * resonanceDelta p α)
  else 0

/-- Primitive shots with denominators from `1` through `P`. -/
def primitiveShotSum (N P : ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 P, primitiveShot N p α

/-- The central shot sum `Y_N` from the manuscript. -/
def reconstructedShotSum (N : ℕ) : ℝ → ℝ :=
  primitiveShotSum N N

/-- The signed coordinate `(ℓog N) p δ_p` of a resonance. -/
def scaledResonanceCoordinate (N p : ℕ) (α : ℝ) : ℝ :=
  Real.log (N : ℝ) * (p : ℝ) * resonanceDelta p α

/-- The fixed-`A` finite shot process retained for the Poisson limit. -/
def finiteResonanceShotSum (N : ℕ) (A : ℝ) (α : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 N,
    if |scaledResonanceCoordinate N p α| ≤ A then primitiveShot N p α else 0

/-- The complementary small-jump tail removed in the manuscript. -/
def minorResonanceShotSum (N : ℕ) (A : ℝ) (α : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 N,
    if A < |scaledResonanceCoordinate N p α| then primitiveShot N p α else 0

theorem primitiveShot_of_not_primitive (N p : ℕ) (α : ℝ)
    (h : ¬ IsPrimitiveResonance p α) :
    primitiveShot N p α = 0 := by
  simp [primitiveShot, h]

theorem primitiveShot_of_primitive (N p : ℕ) (α : ℝ)
    (h : IsPrimitiveResonance p α) :
    primitiveShot N p α =
      bernoulliMark ((N : ℝ) * resonanceDelta p α) /
        ((p : ℝ) * resonanceDelta p α) := by
  simp [primitiveShot, h]

/-- The convention at an exact rational resonance is zero. -/
theorem primitiveShot_of_delta_eq_zero (N p : ℕ) (α : ℝ)
    (hδ : resonanceDelta p α = 0) :
    primitiveShot N p α = 0 := by
  by_cases h : IsPrimitiveResonance p α
  · rw [primitiveShot_of_primitive N p α h, hδ]
    simp [bernoulliMark]
  · exact primitiveShot_of_not_primitive N p α h

theorem measurable_primitiveShot (N p : ℕ) :
    Measurable (primitiveShot N p) := by
  apply Measurable.ite (measurableSet_isPrimitiveResonance p)
  · exact (bernoulliMark_measurable.comp
      (measurable_const.mul (measurable_resonanceDelta p))).div
        (measurable_const.mul (measurable_resonanceDelta p))
  · exact measurable_const

theorem measurable_primitiveShotSum (N P : ℕ) :
    Measurable (primitiveShotSum N P) := by
  classical
  unfold primitiveShotSum
  exact Finset.measurable_fun_sum (Finset.Icc 1 P) fun p _ ↦
    measurable_primitiveShot N p

theorem measurable_reconstructedShotSum (N : ℕ) :
    Measurable (reconstructedShotSum N) :=
  measurable_primitiveShotSum N N

theorem measurable_scaledResonanceCoordinate (N p : ℕ) :
    Measurable (scaledResonanceCoordinate N p) := by
  unfold scaledResonanceCoordinate
  exact (measurable_const.mul measurable_const).mul
    (measurable_resonanceDelta p)

theorem measurable_finiteResonanceShotSum (N : ℕ) (A : ℝ) :
    Measurable (finiteResonanceShotSum N A) := by
  classical
  unfold finiteResonanceShotSum
  apply Finset.measurable_fun_sum
  intro p _
  apply Measurable.ite
  · exact measurableSet_le (measurable_scaledResonanceCoordinate N p).abs measurable_const
  · exact measurable_primitiveShot N p
  · exact measurable_const

theorem measurable_minorResonanceShotSum (N : ℕ) (A : ℝ) :
    Measurable (minorResonanceShotSum N A) := by
  classical
  unfold minorResonanceShotSum
  apply Finset.measurable_fun_sum
  intro p _
  apply Measurable.ite
  · exact measurableSet_lt measurable_const
      (measurable_scaledResonanceCoordinate N p).abs
  · exact measurable_primitiveShot N p
  · exact measurable_const

/-- Exact decomposition into the retained finite process and its complement. -/
theorem reconstructedShotSum_eq_finite_add_minor (N : ℕ) (A : ℝ) (α : ℝ) :
    reconstructedShotSum N α =
      finiteResonanceShotSum N A α + minorResonanceShotSum N A α := by
  classical
  unfold reconstructedShotSum primitiveShotSum finiteResonanceShotSum
    minorResonanceShotSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : |scaledResonanceCoordinate N p α| ≤ A
  · simp [h, not_lt.mpr h]
  · have h' : A < |scaledResonanceCoordinate N p α| := lt_of_not_ge h
    simp [h, h']

end

end Erdos1002
