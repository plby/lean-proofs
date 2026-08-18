/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.GuardedTraceControl

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible

noncomputable section

variable {beta eta : ℝ} {C : HigherDimensionalContext beta eta}
  {selector : BoundedCFPSelector C} {delta gamma : ℝ}

/-- Uniform first-crossing control when the initial selected rank is bounded
by a fixed `D0`. -/
def guardedTraceControl_first_crossing_uniform
    {m : ℕ} {tau sigma : ℝ} {J D0 : ℕ}
    {initial : CoordinateReplacementState selector} {n : ℕ}
    (Tg : RelationTrace
      (GuardedCoordinateReplacement selector delta gamma
        (Real.rpow (m : ℝ) tau)) initial (n + 1))
    (hdelta : 0 ≤ delta) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hm : 0 < m)
    (hsigma : 0 ≤ sigma) (ha : 0 ≤ tau * sigma)
    (hstrong : selector.UsesScaleExponent sigma)
    (hinitial : initial.selected.dimension ≤ D0)
    (hpre : coordinateUpwardJump Tg.forgetPopulationGuard n ≤ J) :
    let Q := D0 + J
    let R := max Q (rankBoundSum C Q)
    CoordinateTraceControl
      (quantitativeMoveParameters C delta gamma m (tau * sigma) R Q
        hdelta hgamma0 hgamma1 hm ha)
      Tg.forgetPopulationGuard := by
  let T := Tg.forgetPopulationGuard
  let Q := D0 + J
  let R := max Q (rankBoundSum C Q)
  have hzero : (T.state 0).selected.dimension = initial.selected.dimension := by
    exact congrArg (fun S : CoordinateReplacementState selector ↦
      S.selected.dimension) T.state_zero
  have hprefixRank : ∀ i, i ≤ n → (T.state i).selected.dimension ≤ Q := by
    intro i hi
    calc
      (T.state i).selected.dimension ≤
          (T.state 0).selected.dimension + J :=
        T.selected_dimension_le_of_upwardJump_le hi hpre
      _ = initial.selected.dimension + J := by rw [hzero]
      _ ≤ D0 + J := Nat.add_le_add_right hinitial J
  apply coordinateTraceControl_of_bounds T hdelta hgamma0 hgamma1 hm ha
  · intro i hi
    by_cases hilast : i = n + 1
    · subst i
      have hamb : (T.state (n + 1)).ambientDimension ≤ Q := by
        rw [T.ambientDimension_succ (show n < n + 1 by omega)]
        exact hprefixRank n le_rfl
      exact ((T.state (n + 1)).selected_dimension_le.trans
        (rankBound_le_rankBoundSum C hamb)).trans (le_max_right _ _)
    · exact (hprefixRank i (by omega)).trans (le_max_left _ _)
  · intro i hi
    rw [T.ambientDimension_succ hi]
    exact hprefixRank i (by omega)
  · intro i hi
    exact guarded_next_scale_lower (Tg.valid i hi) hm hsigma hstrong

/-- Uniform bounded-jump control using a fixed upper bound `D0` for the
initial selected rank. -/
def guardedTraceControl_of_jump_le_uniform
    {m : ℕ} {tau sigma : ℝ} {J D0 : ℕ}
    {initial : CoordinateReplacementState selector} {length : ℕ}
    (Tg : RelationTrace
      (GuardedCoordinateReplacement selector delta gamma
        (Real.rpow (m : ℝ) tau)) initial length)
    (hdelta : 0 ≤ delta) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hm : 0 < m)
    (hsigma : 0 ≤ sigma) (ha : 0 ≤ tau * sigma)
    (hstrong : selector.UsesScaleExponent sigma)
    (hinitial : initial.selected.dimension ≤ D0)
    (hjump : coordinateUpwardJump Tg.forgetPopulationGuard length ≤ J) :
    CoordinateTraceControl
      (quantitativeMoveParameters C delta gamma m (tau * sigma)
        (D0 + J) (D0 + J) hdelta hgamma0 hgamma1 hm ha)
      Tg.forgetPopulationGuard := by
  let T := Tg.forgetPopulationGuard
  have hzero : (T.state 0).selected.dimension = initial.selected.dimension := by
    exact congrArg (fun S : CoordinateReplacementState selector ↦
      S.selected.dimension) T.state_zero
  have hrank : ∀ i, i ≤ length →
      (T.state i).selected.dimension ≤ D0 + J := by
    intro i hi
    calc
      (T.state i).selected.dimension ≤
          (T.state 0).selected.dimension + J :=
        T.selected_dimension_le_of_upwardJump_le hi hjump
      _ = initial.selected.dimension + J := by rw [hzero]
      _ ≤ D0 + J := Nat.add_le_add_right hinitial J
  apply coordinateTraceControl_of_bounds T hdelta hgamma0 hgamma1 hm ha
  · exact hrank
  · intro i hi
    rw [T.ambientDimension_succ hi]
    exact hrank i (by omega)
  · intro i hi
    exact guarded_next_scale_lower (Tg.valid i hi) hm hsigma hstrong

end

end Erdos186.PZ.Reduction
