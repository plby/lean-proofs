import ErdosProblems.Erdos1148.LongCuspVisitPatterns
import Mathlib.MeasureTheory.Measure.Map

/-! # The modular flow acts by measurable homeomorphisms -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma modularRightTranslate_diagonal_zero (x : ModularOrbitSpace) :
    modularRightTranslate (diagonalFlow 0) x = x := by
  induction x using Quotient.inductionOn' with | h g =>
    change modularMk (g * diagonalFlow 0) = modularMk g
    rw [diagonalFlow_zero, mul_one]

noncomputable def modularDiagonalFlowHomeomorph (t : ℝ) : ModularOrbitSpace ≃ₜ ModularOrbitSpace where
  toFun := modularRightTranslate (diagonalFlow t)
  invFun := modularRightTranslate (diagonalFlow (-t))
  left_inv := by
    intro x
    rw [modularRightTranslate_diagonal_add, add_neg_cancel, modularRightTranslate_diagonal_zero]
  right_inv := by
    intro x
    rw [modularRightTranslate_diagonal_add, neg_add_cancel, modularRightTranslate_diagonal_zero]
  continuous_toFun := continuous_modularRightTranslate _
  continuous_invFun := continuous_modularRightTranslate _

theorem modular_flow_measureReal_preimage (μ : Measure ModularOrbitSpace)
    (hinv : ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t)) μ = μ)
    (t : ℝ) (E : Set ModularOrbitSpace) :
    μ.real ((modularRightTranslate (diagonalFlow t)) ⁻¹' E) = μ.real E := by
  have h := (modularDiagonalFlowHomeomorph t).measurableEmbedding.map_apply μ E
  change (Measure.map (modularRightTranslate (diagonalFlow t)) μ) E =
    μ ((modularRightTranslate (diagonalFlow t)) ⁻¹' E) at h
  rw [hinv] at h
  exact congrArg ENNReal.toReal h.symm

end Erdos1148.DukeArithmetic
