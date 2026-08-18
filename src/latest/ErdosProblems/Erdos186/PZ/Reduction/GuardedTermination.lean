/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.CoordinateReplacement

/-!
# The population-stopped coordinate replacement process

Lemma 10 of Pham--Zakharov does not iterate replacements after the population
has crossed its stopping threshold.  This file records that guard explicitly.
It also proves the exact closing argument: if every dense candidate at a
guarded terminal state is eligible and one further dense replacement would
still lie above the guard, then guarded terminality is genuine coordinate
irreducibility.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

variable {beta eta : ℝ} {C : HigherDimensionalContext beta eta}
  {selector : BoundedCFPSelector C} {delta gamma cutoff : ℝ}

/-- A coordinate replacement which remains strictly above the prescribed
population stopping threshold. -/
def GuardedCoordinateReplacement
    (selector : BoundedCFPSelector C) (delta gamma cutoff : ℝ)
    (S T : CoordinateReplacementState selector) : Prop :=
  CoordinateReplacement selector delta gamma S T ∧
    cutoff < (T.points.card : ℝ)

namespace GuardedCoordinateReplacement

variable {S T : CoordinateReplacementState selector}

theorem coordinate
    (hST : GuardedCoordinateReplacement selector delta gamma cutoff S T) :
    CoordinateReplacement selector delta gamma S T :=
  hST.1

theorem aboveCutoff
    (hST : GuardedCoordinateReplacement selector delta gamma cutoff S T) :
    cutoff < (T.points.card : ℝ) :=
  hST.2

theorem dense
    (hST : GuardedCoordinateReplacement selector delta gamma cutoff S T) :
    delta * (S.points.card : ℝ) ≤ (T.points.card : ℝ) :=
  hST.coordinate.dense

end GuardedCoordinateReplacement

/-- Forgetting the population guard preserves reachability in the ordinary
coordinate replacement relation. -/
theorem coordinateReachable_of_guardedReachable
    {S T : CoordinateReplacementState selector}
    (hST : Relation.ReflTransGen
      (GuardedCoordinateReplacement selector delta gamma cutoff) S T) :
    Relation.ReflTransGen (CoordinateReplacement selector delta gamma) S T := by
  exact Relation.ReflTransGen.trans_induction_on hST
    (fun _ ↦ Relation.ReflTransGen.refl)
    (fun h ↦ Relation.ReflTransGen.single h.coordinate)
    (fun _ _ h₁ h₂ ↦ h₁.trans h₂)

namespace RelationTrace

/-- Every reflexive-transitive derivation can be presented as a finite
relation trace ending at its target. -/
theorem exists_of_reflTransGen {State : Type*} {step : State → State → Prop}
    {a b : State} (h : Relation.ReflTransGen step a b) :
    ∃ length : ℕ, ∃ T : RelationTrace step a length, T.state length = b := by
  induction h with
  | refl =>
      let T : RelationTrace step a 0 := {
        state := fun _ ↦ a
        state_zero := rfl
        valid := by intro i hi; omega }
      exact ⟨0, T, rfl⟩
  | @tail b c hbc hcd ih =>
      obtain ⟨n, T, hT⟩ := ih
      let states : ℕ → State := fun i ↦ if i ≤ n then T.state i else c
      let U : RelationTrace step a (n + 1) := {
        state := states
        state_zero := by simpa [states] using T.state_zero
        valid := by
          intro i hi
          by_cases hin : i < n
          · simpa [states, Nat.le_of_lt hin, show i + 1 ≤ n by omega] using
              T.valid i hin
          · have hi : i = n := by omega
            subst i
            simpa [states, hT] using hcd }
      exact ⟨n + 1, U, by simp [U, states]⟩

/-- Forget the population guard on every step of a trace. -/
def forgetPopulationGuard
    {initial : CoordinateReplacementState selector} {length : ℕ}
    (T : RelationTrace
      (GuardedCoordinateReplacement selector delta gamma cutoff)
      initial length) :
    RelationTrace (CoordinateReplacement selector delta gamma) initial length where
  state := T.state
  state_zero := T.state_zero
  valid i hi := (T.valid i hi).coordinate

/-- Every positive-index state of a guarded trace lies above the cutoff. -/
theorem state_card_gt_cutoff
    {initial : CoordinateReplacementState selector} {length : ℕ}
    (T : RelationTrace
      (GuardedCoordinateReplacement selector delta gamma cutoff)
      initial length)
    {i : ℕ} (hi : 0 < i) (hil : i ≤ length) :
    cutoff < ((T.state i).points.card : ℝ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  exact (T.valid j (by omega)).aboveCutoff

end RelationTrace

/-- A common length bound for all population-guarded traces supplies a
reachable guarded terminal state. -/
theorem exists_guardedTerminal_of_trace_bound
    (selector : BoundedCFPSelector C) (delta gamma cutoff : ℝ)
    (initial : CoordinateReplacementState selector) (bound : ℕ)
    (trace_bound : ∀ {length : ℕ},
      RelationTrace
        (GuardedCoordinateReplacement selector delta gamma cutoff)
        initial length → length ≤ bound) :
    ∃ S,
      Relation.ReflTransGen
        (GuardedCoordinateReplacement selector delta gamma cutoff) initial S ∧
      ∀ T, ¬ GuardedCoordinateReplacement selector delta gamma cutoff S T := by
  apply exists_reachable_terminal_of_trace_bound
    (GuardedCoordinateReplacement selector delta gamma cutoff)
    (fun S ↦ ∀ T, ¬ GuardedCoordinateReplacement
      selector delta gamma cutoff S T)
    initial bound
  · intro S _hreachable hnot
    push Not at hnot
    exact hnot
  · exact trace_bound

/-- Local candidate closure and enough population for one more dense move
upgrade a guarded terminal state to genuine bounded coordinate
irreducibility. -/
theorem irreducible_of_guardedTerminal
    (S : CoordinateReplacementState selector)
    (hterminal : ∀ T,
      ¬ GuardedCoordinateReplacement selector delta gamma cutoff S T)
    (_hclosed : selector.CandidateClosedAt S.points S.eligible delta)
    (hnext : cutoff < delta * (S.points.card : ℝ)) :
    S.Irreducible delta gamma := by
  by_contra hirr
  obtain ⟨T, hST⟩ :=
    (not_stateIrreducible_iff_exists_replacement selector delta gamma S).mp hirr
  apply hterminal T
  exact ⟨hST, hnext.trans_le hST.dense⟩

end

end Erdos186.PZ.Reduction
