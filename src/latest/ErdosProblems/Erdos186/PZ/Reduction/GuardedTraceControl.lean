/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.GuardedTermination
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeOneStep

/-!
# Numerical control of population-guarded traces
-/

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible

noncomputable section

variable {beta eta : ℝ} {C : HigherDimensionalContext beta eta}
  {selector : BoundedCFPSelector C} {delta gamma cutoff : ℝ}

/-- The source scale saving follows from the population guard and a strong
current-population scale exponent. -/
theorem guarded_next_scale_lower
    {S T : CoordinateReplacementState selector}
    {m : ℕ} {tau sigma : ℝ}
    (hST : GuardedCoordinateReplacement selector delta gamma
      (Real.rpow (m : ℝ) tau) S T)
    (hm : 0 < m) (hsigma : 0 ≤ sigma)
    (hstrong : selector.UsesScaleExponent sigma) :
    Real.rpow (m : ℝ) (tau * sigma) ≤
      ((selector.input T.points T.eligible).scale : ℝ) := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hcutoff0 : 0 ≤ Real.rpow (m : ℝ) tau :=
    Real.rpow_nonneg hmreal.le _
  have hcard : Real.rpow (m : ℝ) tau ≤ (T.points.card : ℝ) :=
    hST.aboveCutoff.le
  calc
    Real.rpow (m : ℝ) (tau * sigma) =
        Real.rpow (Real.rpow (m : ℝ) tau) sigma :=
      Real.rpow_mul hmreal.le tau sigma
    _ ≤ Real.rpow (T.points.card : ℝ) sigma :=
      Real.rpow_le_rpow hcutoff0 hcard hsigma
    _ ≤ ((selector.input T.points T.eligible).scale : ℝ) :=
      hstrong T.points T.eligible

/-- If the whole guarded trace stays within an upward-jump budget, its exact
coordinate estimates form one uniformly controlled numerical trace. -/
def guardedTraceControl_of_jump_le
    {m : ℕ} {tau sigma : ℝ} {J : ℕ}
    {initial : CoordinateReplacementState selector} {length : ℕ}
    (Tg : RelationTrace
      (GuardedCoordinateReplacement selector delta gamma
        (Real.rpow (m : ℝ) tau)) initial length)
    (hdelta : 0 ≤ delta) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hm : 0 < m)
    (hsigma : 0 ≤ sigma) (ha : 0 ≤ tau * sigma)
    (hstrong : selector.UsesScaleExponent sigma)
    (hjump : coordinateUpwardJump Tg.forgetPopulationGuard length ≤ J) :
    CoordinateTraceControl
      (quantitativeMoveParameters C delta gamma m (tau * sigma)
        (initial.selected.dimension + J) (initial.selected.dimension + J)
        hdelta hgamma0 hgamma1 hm ha)
      Tg.forgetPopulationGuard := by
  let T := Tg.forgetPopulationGuard
  apply coordinateTraceControl_of_bounds T hdelta hgamma0 hgamma1 hm ha
  · intro i hi
    have hzero : (T.state 0).selected.dimension = initial.selected.dimension := by
      exact congrArg (fun S : CoordinateReplacementState selector ↦
        S.selected.dimension) T.state_zero
    simpa [hzero] using T.selected_dimension_le_of_upwardJump_le hi hjump
  · intro i hi
    rw [T.ambientDimension_succ hi]
    have hzero : (T.state 0).selected.dimension = initial.selected.dimension := by
      exact congrArg (fun S : CoordinateReplacementState selector ↦
        S.selected.dimension) T.state_zero
    simpa [hzero] using
      T.selected_dimension_le_of_upwardJump_le (show i ≤ length by omega) hjump
  · intro i hi
    exact guarded_next_scale_lower (Tg.valid i hi) hm hsigma hstrong

/-- Numerical control of the prefix ending at the first crossing of an
upward-jump budget.  Only the last selected rank needs the larger finite
`rankBoundSum` cap. -/
def guardedTraceControl_first_crossing
    {m : ℕ} {tau sigma : ℝ} {J : ℕ}
    {initial : CoordinateReplacementState selector} {n : ℕ}
    (Tg : RelationTrace
      (GuardedCoordinateReplacement selector delta gamma
        (Real.rpow (m : ℝ) tau)) initial (n + 1))
    (hdelta : 0 ≤ delta) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hm : 0 < m)
    (hsigma : 0 ≤ sigma) (ha : 0 ≤ tau * sigma)
    (hstrong : selector.UsesScaleExponent sigma)
    (hpre : coordinateUpwardJump Tg.forgetPopulationGuard n ≤ J) :
    let Q := initial.selected.dimension + J
    let R := max Q (rankBoundSum C Q)
    CoordinateTraceControl
      (quantitativeMoveParameters C delta gamma m (tau * sigma) R Q
        hdelta hgamma0 hgamma1 hm ha)
      Tg.forgetPopulationGuard := by
  let T := Tg.forgetPopulationGuard
  let Q := initial.selected.dimension + J
  let R := max Q (rankBoundSum C Q)
  have hzero : (T.state 0).selected.dimension = initial.selected.dimension := by
    exact congrArg (fun S : CoordinateReplacementState selector ↦
      S.selected.dimension) T.state_zero
  apply coordinateTraceControl_of_bounds T hdelta hgamma0 hgamma1 hm ha
  · intro i hi
    by_cases hilast : i = n + 1
    · subst i
      have hlast := T.next_selected_dimension_le_rankBoundSum
        (show n < n + 1 by omega) hpre
      rw [hzero] at hlast
      exact hlast.trans (le_max_right _ _)
    · have hin : i ≤ n := by omega
      have hdim : (T.state i).selected.dimension ≤ Q := by
        simpa [Q, hzero] using
          T.selected_dimension_le_of_upwardJump_le hin hpre
      exact hdim.trans (le_max_left _ _)
  · intro i hi
    rw [T.ambientDimension_succ hi]
    have hin : i ≤ n := by omega
    simpa [Q, hzero] using T.selected_dimension_le_of_upwardJump_le hin hpre
  · intro i hi
    exact guarded_next_scale_lower (Tg.valid i hi) hm hsigma hstrong

end

end Erdos186.PZ.Reduction
