/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.MovingAdvance931
import ErdosProblems.Erdos599.HalfwayIndexedCertifiedScheduler

/-!
# Total indexed scheduling from the moving-slice successor

This adapter executes a concrete moving-slice 9.34 certificate for a real
terminal, records an already completed request, and otherwise leaves the
state unchanged. Strict index growth is retained in the terminal branch.
The geometric compiler remains an explicit input until its concrete
ladder/assignment construction is supplied.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

universe u w

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {persistent B : Set V}
variable {Stage : Type w} [LinearOrder Stage]
variable {slice closure : Stage → Set V}

namespace IndexedTerminalResolutionState

local notation "State" => IndexedTerminalResolutionState
  (Gamma := Gamma) (Y := Y) (kappa := kappa)
  (persistent := persistent) (B := B) slice closure

/-- A successful local terminal resolution with its actual new slice. -/
structure MovingTerminalAdvance (S : State) (u : V) where
  stageIndex : Stage
  blueprint : LinkageBlueprint Gamma Y kappa
  stage_strict : S.stageIndex < stageIndex
  conclusion : StableExtensionConclusion S.blueprint blueprint u
    (slice stageIndex) (closure stageIndex) persistent B
  refinement : S.blueprint.PredecessorRefines blueprint

/-- Concrete 9.30 and moving 9.31 data give a local indexed advance. -/
def MovingTerminalAdvance.of930931
    {S : State} {u z : V} {cut current U : LinkageBlueprint Gamma Y kappa}
    (j : Stage) (hij : S.stageIndex < j)
    (h30 : Continuation930 S.blueprint cut current u z (slice S.stageIndex) B)
    (h31 : MovingAdvance931 S.blueprint current U z
      (slice S.stageIndex) (slice j) (closure j) persistent B)
    (h30refines : S.blueprint.PredecessorRefines current)
    (h31refines : current.PredecessorRefines U) :
    MovingTerminalAdvance S u where
  stageIndex := j
  blueprint := U
  stage_strict := hij
  conclusion := movingAssertion934_of_930_931 h30 h31
  refinement := (movingAssertion934_of_refining_930_931
    h30 h31 h30refines h31refines).2

/-- The source-faithful all-real-terminal local compiler. -/
def AllRealTerminalMovingCompiler : Prop :=
  ∀ (S : State) (u : V), u ∈ S.blueprint.realPart.terminals →
    Nonempty (MovingTerminalAdvance S u)

namespace MovingSuccessor

variable (C : AllRealTerminalMovingCompiler
  (Gamma := Gamma) (Y := Y) (kappa := kappa)
  (persistent := persistent) (B := B) (slice := slice) (closure := closure))

def advanceData (S : State) (u : V) (hu : u ∈ S.blueprint.realPart.terminals) :
    MovingTerminalAdvance S u := (C S u hu).some

def advance (S : State) (u : V) (hu : u ∈ S.blueprint.realPart.terminals) :
    State where
  stageIndex := (advanceData C S u hu).stageIndex
  blueprint := (advanceData C S u hu).blueprint
  isBlueprint := (advanceData C S u hu).conclusion.isLinkageBlueprint
  stable := (advanceData C S u hu).conclusion.stable
  linked := insert u S.linked
  links := by
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact (advanceData C S u hu).conclusion.2.2.2.1
    · exact realLinksTo_mono (advanceData C S u hu).conclusion.realExtends.1
        (S.links x hx)

def recordLinked (S : State) (u : V) (hu : S.blueprint.RealLinksTo u B) :
    State where
  stageIndex := S.stageIndex
  blueprint := S.blueprint
  isBlueprint := S.isBlueprint
  stable := S.stable
  linked := insert u S.linked
  links := by
    intro x hx
    rcases hx with hx | hx
    · exact hx ▸ hu
    · exact S.links x hx

def step (S : State) (u : V) : State := by
  classical
  exact if hu : u ∈ S.blueprint.realPart.terminals then advance C S u hu
    else if hlinked : S.blueprint.RealLinksTo u B then recordLinked S u hlinked
    else S

theorem refiningExtends_step (S : State) (u : V) :
    S.RefiningExtends (step C S u) := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals
  · simp only [step, hu, dite_true]
    exact ⟨(advanceData C S u hu).conclusion.realExtends,
      (advanceData C S u hu).refinement,
      (advanceData C S u hu).stage_strict.le⟩
  · simp only [step, hu, dite_false]
    by_cases hlinked : S.blueprint.RealLinksTo u B
    · simp only [hlinked, dite_true]
      exact ⟨realExtends_refl S.blueprint B,
        PredecessorRefines.refl S.blueprint, le_rfl⟩
    · simp only [hlinked, dite_false]
      exact RefiningExtends.refl S

theorem stage_mono_step (S : State) (u : V) :
    S.stageIndex ≤ (step C S u).stageIndex := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals
  · simpa only [step, hu, dite_true, advance] using
      (advanceData C S u hu).stage_strict.le
  · by_cases hlinked : S.blueprint.RealLinksTo u B <;>
      simp [step, hu, hlinked, recordLinked]

theorem stage_strict_step (S : State) (u : V)
    (hu : u ∈ S.blueprint.realPart.terminals) :
    S.stageIndex < (step C S u).stageIndex := by
  simpa only [step, hu, dite_true, advance] using
    (advanceData C S u hu).stage_strict

theorem linked_subset_step (S : State) (u : V) :
    S.linked ⊆ (step C S u).linked := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals
  · simpa [step, hu, advance] using Set.subset_insert u S.linked
  · by_cases hlinked : S.blueprint.RealLinksTo u B <;>
      simp [step, hu, hlinked, recordLinked]

theorem terminal_or_completed_linked_step (S : State) (u : V)
    (hu : u ∈ S.blueprint.realPart.terminals ∨ S.blueprint.RealLinksTo u B) :
    u ∈ (step C S u).linked := by
  rcases hu with hu | hu
  · simp [step, hu, advance]
  · by_cases hterminal : u ∈ S.blueprint.realPart.terminals
    · simp [step, hterminal, advance]
    · simp [step, hterminal, hu, recordLinked]

end MovingSuccessor

/-- The indexed total successor used by the fair recursor. -/
def SchedulerSuccessor.ofMovingCompiler
    (C : AllRealTerminalMovingCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) (slice := slice) (closure := closure)) :
    SchedulerSuccessor (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure where
  step := MovingSuccessor.step C
  step_extends := MovingSuccessor.refiningExtends_step C
  stage_mono := MovingSuccessor.stage_mono_step C
  stage_strict_of_terminal := MovingSuccessor.stage_strict_step C
  linked_mono := MovingSuccessor.linked_subset_step C
  terminal_or_completed_linked := MovingSuccessor.terminal_or_completed_linked_step C

#print axioms MovingTerminalAdvance.of930931
#print axioms SchedulerSuccessor.ofMovingCompiler

end IndexedTerminalResolutionState
end Erdos599.Blueprint.LinkageBlueprint
