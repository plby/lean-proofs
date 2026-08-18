/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.TraceAdapter

/-!
# Rank bookkeeping for coordinate replacement traces

This file supplies the rank-only part of the quantitative argument in
Pham--Zakharov Lemma 10.  It is independent of all GAP-volume estimates.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

variable {beta eta : ℝ} {C : HigherDimensionalContext beta eta}
  {selector : BoundedCFPSelector C} {delta gamma : ℝ}

/-- A convenient finite upper bound for all CFP ranks in ambient dimensions
at most `R`. -/
def rankBoundSum (C : HigherDimensionalContext beta eta) (R : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (R + 1), C.rankBound d

/-- A convenient positive finite upper bound for all CFP scale denominators
in ambient dimensions at most `R`. -/
def scaleDenSum (C : HigherDimensionalContext beta eta) (R : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (R + 1), C.scaleDen d

theorem rankBound_le_rankBoundSum (C : HigherDimensionalContext beta eta)
    {d R : ℕ} (hd : d ≤ R) : C.rankBound d ≤ rankBoundSum C R := by
  apply Finset.single_le_sum (fun i _hi ↦ Nat.zero_le (C.rankBound i))
  simp
  omega

theorem scaleDen_le_scaleDenSum (C : HigherDimensionalContext beta eta)
    {d R : ℕ} (hd : d ≤ R) : C.scaleDen d ≤ scaleDenSum C R := by
  apply Finset.single_le_sum (fun i _hi ↦ Nat.zero_le (C.scaleDen i))
  simp
  omega

theorem scaleDenSum_pos (C : HigherDimensionalContext beta eta) (R : ℕ) :
    0 < scaleDenSum C R := by
  exact (C.scaleDen_pos 0).trans_le
    (scaleDen_le_scaleDenSum C (show 0 ≤ R by omega))

/-- Total upward selected-rank jump in the first `m` coordinate moves. -/
def coordinateUpwardJump
    {initial : CoordinateReplacementState selector} {length : ℕ}
    (T : RelationTrace (CoordinateReplacement selector delta gamma)
      initial length) : ℕ → ℕ
  | 0 => 0
  | m + 1 => coordinateUpwardJump T m +
      ((T.state (m + 1)).selected.dimension -
        (T.state m).selected.dimension)

/-- Total downward selected-rank jump in the first `m` coordinate moves. -/
def coordinateDownwardJump
    {initial : CoordinateReplacementState selector} {length : ℕ}
    (T : RelationTrace (CoordinateReplacement selector delta gamma)
      initial length) : ℕ → ℕ
  | 0 => 0
  | m + 1 => coordinateDownwardJump T m +
      ((T.state m).selected.dimension -
        (T.state (m + 1)).selected.dimension)

namespace RelationTrace

variable {initial : CoordinateReplacementState selector} {length : ℕ}
  (T : RelationTrace (CoordinateReplacement selector delta gamma)
    initial length)

/-- Restrict a coordinate trace to one of its prefixes. -/
def take (m : ℕ) (hm : m ≤ length) :
    RelationTrace (CoordinateReplacement selector delta gamma) initial m where
  state := T.state
  state_zero := T.state_zero
  valid i hi := T.valid i (hi.trans_le hm)

@[simp] theorem coordinateUpwardJump_zero : coordinateUpwardJump T 0 = 0 := rfl

@[simp] theorem coordinateUpwardJump_succ (m : ℕ) :
    coordinateUpwardJump T (m + 1) = coordinateUpwardJump T m +
      ((T.state (m + 1)).selected.dimension -
        (T.state m).selected.dimension) := rfl

theorem coordinateUpwardJump_mono : Monotone (coordinateUpwardJump T) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
      exact ih.trans (Nat.le_add_right _ _)

/-- A first crossing of an upward-jump budget has a predecessor still within
the budget. -/
theorem exists_first_coordinateUpwardJump_gt {J : ℕ}
    (hcross : J < coordinateUpwardJump T length) :
    ∃ i : ℕ, i < length ∧ coordinateUpwardJump T i ≤ J ∧
      J < coordinateUpwardJump T (i + 1) := by
  let P : ℕ → Prop := fun n ↦ J < coordinateUpwardJump T n
  have hex : ∃ n, P n := ⟨length, hcross⟩
  have hnP : P (Nat.find hex) := Nat.find_spec hex
  have hnle : Nat.find hex ≤ length := Nat.find_min' hex hcross
  have hn0 : Nat.find hex ≠ 0 := by
    intro hn
    have : J < 0 := by simpa [P, hn] using hnP
    omega
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨i, by omega, ?_, ?_⟩
  · exact Nat.le_of_not_lt (Nat.find_min hex (by omega))
  · simpa [P, hi, coordinateUpwardJump] using hnP

/-- Selected dimensions telescope against total upward and downward jump. -/
theorem coordinate_dimension_balance (m : ℕ) :
    (T.state 0).selected.dimension + coordinateUpwardJump T m =
      (T.state m).selected.dimension + coordinateDownwardJump T m := by
  induction m with
  | zero => simp [coordinateDownwardJump]
  | succ m ih =>
      simp only [coordinateUpwardJump_succ, coordinateDownwardJump]
      omega

theorem selected_dimension_le_initial_add_upwardJump (m : ℕ) :
    (T.state m).selected.dimension ≤
      (T.state 0).selected.dimension + coordinateUpwardJump T m := by
  have h := T.coordinate_dimension_balance m
  omega

/-- After the initial state, the ambient dimension is the selected dimension
at the preceding state. -/
theorem ambientDimension_succ {i : ℕ} (hi : i < length) :
    (T.state (i + 1)).ambientDimension =
      (T.state i).selected.dimension :=
  (T.valid i hi).next_ambientDimension

/-- Before a prescribed upward-jump budget is crossed, every selected rank
is bounded by the initial selected rank plus that budget. -/
theorem selected_dimension_le_of_upwardJump_le
    {m J i : ℕ} (hi : i ≤ m)
    (hjump : coordinateUpwardJump T m ≤ J) :
    (T.state i).selected.dimension ≤
      (T.state 0).selected.dimension + J := by
  exact (T.selected_dimension_le_initial_add_upwardJump i).trans <| by
    gcongr
    exact (T.coordinateUpwardJump_mono hi).trans hjump

/-- The first state after a prefix whose upward jump is at most `J` has rank
bounded by a finite maximum depending only on that prefix cap. -/
theorem next_selected_dimension_le_rankBoundSum
    {i J : ℕ} (hi : i < length)
    (hjump : coordinateUpwardJump T i ≤ J) :
    (T.state (i + 1)).selected.dimension ≤
      rankBoundSum C ((T.state 0).selected.dimension + J) := by
  have hamb : (T.state (i + 1)).ambientDimension ≤
      (T.state 0).selected.dimension + J := by
    rw [T.ambientDimension_succ hi]
    exact T.selected_dimension_le_of_upwardJump_le (le_refl i) hjump
  exact (T.state (i + 1)).selected_dimension_le.trans
    (rankBound_le_rankBoundSum C hamb)

/-- The rank-only upward jump agrees with the numerical trace adapter's
`upwardJump`. -/
theorem coordinateUpwardJump_eq_upwardJump
    {p : Erdos186.Irreducible.MoveParameters}
    (H : CoordinateTraceControl p T) (m : ℕ) :
    coordinateUpwardJump T m =
      Erdos186.Irreducible.upwardJump H.toMoveTrace m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [coordinateUpwardJump_succ,
        Erdos186.Irreducible.upwardJump]
      rw [ih]
      by_cases hup : (T.state m).selected.dimension <
          (T.state (m + 1)).selected.dimension
      · have hkind : coordinateMoveKind (T.state m) (T.state (m + 1)) =
            .up := by simp [coordinateMoveKind, hup]
        simp only [CoordinateTraceControl.toMoveTrace, hkind, if_true]
        rfl
      · have hdiff : (T.state (m + 1)).selected.dimension -
            (T.state m).selected.dimension = 0 := Nat.sub_eq_zero_of_le
          (Nat.le_of_not_lt hup)
        have hkind : coordinateMoveKind (T.state m) (T.state (m + 1)) ≠
            .up := by
          simp only [coordinateMoveKind, hup, if_false]
          split <;> simp
        simp [CoordinateTraceControl.toMoveTrace, hkind, hdiff]

end RelationTrace

end

end Erdos186.PZ.Reduction
