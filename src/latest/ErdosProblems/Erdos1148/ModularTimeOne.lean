import ErdosProblems.Erdos1148.ModularFlowHomeomorph
import ErdosProblems.Erdos1148.FiniteOrbitPartition

/-! # Integer iterates of the time-one modular flow -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def modularTimeOne : ModularOrbitSpace → ModularOrbitSpace :=
  modularRightTranslate (diagonalFlow 1)

lemma continuous_modularTimeOne : Continuous modularTimeOne := continuous_modularRightTranslate _

lemma modularTimeOne_iterate (n : ℕ) (x : ModularOrbitSpace) :
    modularTimeOne^[n] x = modularRightTranslate (diagonalFlow (n : ℝ)) x := by
  induction n with
  | zero =>
    simpa only [Function.iterate_zero_apply, Nat.cast_zero] using
      (modularRightTranslate_diagonal_zero x).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change modularRightTranslate (diagonalFlow 1)
      (modularRightTranslate (diagonalFlow (n : ℝ)) x) = _
    rw [modularRightTranslate_diagonal_add, Nat.cast_add, Nat.cast_one]

lemma modularTimeOne_iterate_mk (n : ℕ) (g : SL(2, ℝ)) :
    modularTimeOne^[n] (modularMk g) = modularMk (g * diagonalFlow (n : ℝ)) := by
  rw [modularTimeOne_iterate, modularRightTranslate_mk]

end Erdos1148.DukeArithmetic
