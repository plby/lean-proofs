/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.NoDimensionIncrease
import ErdosProblems.Erdos186.Irreducible

/-!
# From coordinate replacements to numerical move traces

This file is the exact interface between the source-faithful,
varying-dimensional coordinate replacement relation and the numerical
bookkeeping in `Erdos186.Irreducible`.  Population, selected dimension, GAP
volume, and move kind are canonical.  A `CoordinateTraceControl` contains
only the two genuinely quantitative uniformizations: the chosen up-saving
factor and its one-step GAP bounds.
-/

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible

noncomputable section

variable {β η : ℝ} {C : HigherDimensionalContext β η}
  {selector : BoundedCFPSelector C} {δ γ : ℝ}

/-- Numerical state canonically attached to an eligible coordinate state. -/
def CoordinateReplacementState.toIterationState
    (S : CoordinateReplacementState selector) : IterationState where
  population := (S.points.card : ℝ)
  dimension := S.selected.dimension
  gapSize := (S.selected.progression.volume : ℝ)
  population_pos := by
    exact_mod_cast S.points_nonempty.card_pos
  one_le_gapSize := by
    have hcarrier : S.selected.progression.carrier.Nonempty :=
      ⟨S.selected.progression.coordPoint S.selected.progression.zeroCoord,
        S.selected.progression.coordPoint_mem_carrier
          S.selected.progression.zeroCoord⟩
    have hone : 1 ≤ S.selected.progression.carrier.card :=
      Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hcarrier)
    exact_mod_cast hone.trans S.selected.progression.card_carrier_le_volume

/-- Classify a coordinate step by comparison of its two selected ranks. -/
def coordinateMoveKind (S T : CoordinateReplacementState selector) : MoveKind :=
  if S.selected.dimension < T.selected.dimension then .up
  else if T.selected.dimension < S.selected.dimension then .down
  else .shrink

theorem coordinateMoveKind_dimension_rule
    (S T : CoordinateReplacementState selector) :
    match coordinateMoveKind S T with
    | .up => S.selected.dimension < T.selected.dimension
    | .down => T.selected.dimension < S.selected.dimension
    | .shrink => T.selected.dimension = S.selected.dimension := by
  simp only [coordinateMoveKind]
  split_ifs with hup hdown
  · exact hup
  · exact hdown
  · omega

/-- The remaining uniform numerical input needed to turn one whole
coordinate trace into a `MoveTrace`.  In the application, Lemma 6 supplies
the up branch, the residue-fibre Lemma 8 supplies the down branch, and
failure of Definition 9 supplies the shrink branch. -/
structure CoordinateTraceControl
    (p : MoveParameters)
    {initial : CoordinateReplacementState selector} {length : ℕ}
    (T : RelationTrace (CoordinateReplacement selector δ γ) initial length) where
  retention_eq : p.retention = δ
  upSaving : ℕ → ℝ
  upSaving_nonneg : ∀ i, i < length → 0 ≤ upSaving i
  gap_control : ∀ i, i < length →
    (((T.state (i + 1)).selected.progression.volume : ℕ) : ℝ) ≤
      stepMultiplier p (coordinateMoveKind (T.state i) (T.state (i + 1)))
        (upSaving i) *
      (((T.state i).selected.progression.volume : ℕ) : ℝ)
  upSaving_control : ∀ i, i < length →
    coordinateMoveKind (T.state i) (T.state (i + 1)) = .up →
      upSaving i ≤ p.upBase ^
        ((T.state (i + 1)).selected.dimension -
          (T.state i).selected.dimension)

namespace CoordinateTraceControl

variable {p : MoveParameters}
  {initial : CoordinateReplacementState selector} {length : ℕ}
  {T : RelationTrace (CoordinateReplacement selector δ γ) initial length}

/-- The canonical numerical move trace. -/
def toMoveTrace (H : CoordinateTraceControl p T) : MoveTrace p length where
  state i := (T.state i).toIterationState
  kind i := coordinateMoveKind (T.state i) (T.state (i + 1))
  upSaving := H.upSaving
  upSaving_nonneg := H.upSaving_nonneg
  population_retained i hi := by
    rw [H.retention_eq]
    exact (T.valid i hi).dense
  dimension_rule i _hi :=
    coordinateMoveKind_dimension_rule (T.state i) (T.state (i + 1))
  gap_control := H.gap_control
  upSaving_control := H.upSaving_control

@[simp] theorem toMoveTrace_population (H : CoordinateTraceControl p T)
    (i : ℕ) :
    (H.toMoveTrace.state i).population = ((T.state i).points.card : ℝ) := rfl

@[simp] theorem toMoveTrace_dimension (H : CoordinateTraceControl p T)
    (i : ℕ) :
    (H.toMoveTrace.state i).dimension = (T.state i).selected.dimension := rfl

@[simp] theorem toMoveTrace_gapSize (H : CoordinateTraceControl p T)
    (i : ℕ) :
    (H.toMoveTrace.state i).gapSize =
      ((T.state i).selected.progression.volume : ℝ) := rfl

/-- Exact collected population and GAP-volume estimates for a controlled
coordinate trace. -/
theorem population_and_volume_bounds
    (H : CoordinateTraceControl p T) {m : ℕ} (hm : m ≤ length) :
    p.retention ^ m * ((T.state 0).points.card : ℝ) ≤
        ((T.state m).points.card : ℝ) ∧
      ((T.state m).selected.progression.volume : ℝ) ≤
        p.cost ^ (kindCount H.toMoveTrace .up m +
            kindCount H.toMoveTrace .down m) *
          p.shrinkFactor ^ kindCount H.toMoveTrace .shrink m *
            p.upBase ^ upwardJump H.toMoveTrace m *
              ((T.state 0).selected.progression.volume : ℝ) := by
  exact ⟨retention_pow_mul_le_population H.toMoveTrace hm,
    gapSize_le_uniform_product H.toMoveTrace hm⟩

end CoordinateTraceControl

/-- Uniform numerical control of every eligible failure trace yields an
actual reachable, nonaveraging, irreducible coordinate state.  This is the
precise composition of the trace adapter with the finite termination theorem
from Lemma 10. -/
theorem exists_irreducible_of_uniform_trace_control
    (selector : BoundedCFPSelector C) (δ γ : ℝ)
    (initial : CoordinateReplacementState selector)
    (p : MoveParameters) (jumpBound shrinkBound : ℕ)
    (hNA : IsBoxNonaveraging initial.points)
    (control : ∀ {length : ℕ}
      (T : RelationTrace (CoordinateReplacement selector δ γ) initial length),
        CoordinateTraceControl p T)
    (hjump : ∀ {length : ℕ}
      (T : RelationTrace (CoordinateReplacement selector δ γ) initial length),
        upwardJump (control T).toMoveTrace length ≤ jumpBound)
    (hbudget :
      p.cost ^ (initial.selected.dimension + 2 * jumpBound) *
          p.shrinkFactor ^ (shrinkBound + 1) *
            (initial.selected.progression.volume : ℝ) < 1) :
    ∃ S, Relation.ReflTransGen (CoordinateReplacement selector δ γ) initial S ∧
      S.Irreducible δ γ ∧ IsBoxNonaveraging S.points := by
  apply exists_nonaveraging_irreducible_replacement_of_trace_bound
    selector δ γ initial
      (initial.selected.dimension + 2 * jumpBound + shrinkBound) hNA
  intro length T
  let H := control T
  have hj := hjump T
  have hdim : (T.state 0).selected.dimension = initial.selected.dimension :=
    congrArg (fun S : CoordinateReplacementState selector ↦
      S.selected.dimension) T.state_zero
  have hvolume : (T.state 0).selected.progression.volume =
      initial.selected.progression.volume :=
    congrArg (fun S : CoordinateReplacementState selector ↦
      S.selected.progression.volume) T.state_zero
  have hb :
      p.cost ^ ((H.toMoveTrace.state 0).dimension + 2 * jumpBound) *
          p.shrinkFactor ^ (shrinkBound + 1) *
            (H.toMoveTrace.state 0).gapSize < 1 := by
    change p.cost ^ ((T.state 0).selected.dimension + 2 * jumpBound) *
        p.shrinkFactor ^ (shrinkBound + 1) *
          ((T.state 0).selected.progression.volume : ℝ) < 1
    rw [hvolume]
    exact congrArg
      (fun n : ℕ ↦ p.cost ^ (n + 2 * jumpBound) *
        p.shrinkFactor ^ (shrinkBound + 1) *
          (initial.selected.progression.volume : ℝ)) hdim ▸ hbudget
  have hlength := length_le_of_upwardJump_and_budget H.toMoveTrace hj hb
  calc
    length ≤ (T.state 0).selected.dimension + 2 * jumpBound + shrinkBound :=
      hlength
    _ = initial.selected.dimension + 2 * jumpBound + shrinkBound :=
      congrArg (fun n : ℕ ↦ n + 2 * jumpBound + shrinkBound) hdim

end

end Erdos186.PZ.Reduction
