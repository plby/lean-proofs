/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCofinalGlobalTransition

/-!
# A closed simultaneous transaction as a fair global stage run

The source proof can present the end of the Section 9 recursion as one
simultaneously closed transaction.  Such a transaction has one common
inside/assignment relation and, for every alleged non-target sink, an
embedded finite route from that vertex to the ambient target.

An alleged sink cannot in fact exist: since its route ends in the target but
starts outside the target, the route has a first outgoing edge, and that edge
belongs to the common real relation.  This file packages that concrete
closure argument as a one-stage `CofinalClubStageRun`.  Relation and carrier
monotonicity and countable upper bounds are then definitional; scheduler
fairness follows from the embedded-route contradiction.  No rank,
monotonicity, fairness, or global orientation is assumed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- A target route embedded in the real part of a fixed simultaneous
transaction.  This is concrete path data, not a scheduler certificate. -/
structure EmbeddedTransactionTargetRoute
    {C : ClubStageGeometry Gamma Y kappa theta}
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} (D : ClubStageUnionData C W A u) (x : V) where
  path : FinitePath Gamma.graph
  start : path.start = x
  finish : path.finish ∈ Gamma.target
  support : path.support ⊆ D.carrier
  edges : path.edgeSet ⊆ relationRealEdges (Gamma := Gamma)
    (D.inside ∪ assignedFiniteEdges A)

/-- One fully closed simultaneous Section 9 transaction.

`data` is the actual inside-fragment/assignment datum, including an anchor
target route.  `resolve` is the output of the simultaneous closure: every
vertex which could still be a non-target sink has a target route embedded in
that same common relation. -/
structure SingleGlobalClubStageTransaction
    (C : ClubStageGeometry Gamma Y kappa theta) where
  blueprint : LinkageBlueprint Gamma Y kappa
  fractured : FracturedWarp Gamma
  assignment : SimultaneousAssignment fractured.paths Y
  anchor : V
  data : ClubStageUnionData C blueprint assignment anchor
  resolve : ∀ x,
    x ∈ data.carrier →
    (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma)
      (data.inside ∪ assignedFiniteEdges assignment)) →
    x ∉ Gamma.target →
    Nonempty (EmbeddedTransactionTargetRoute data x)

namespace SingleGlobalClubStageTransaction

variable {C : ClubStageGeometry Gamma Y kappa theta}

/-- The common surviving real-edge relation. -/
def realEdge (T : SingleGlobalClubStageTransaction C) : Set (V × V) :=
  relationRealEdges (Gamma := Gamma)
    (T.data.inside ∪ assignedFiniteEdges T.assignment)

/-- The simultaneous closure leaves no non-target sink in the common
carrier.  This is the key non-vacuous use of its embedded route family. -/
theorem no_nonTarget_sink (T : SingleGlobalClubStageTransaction C) (x : V)
    (hx : x ∈ T.data.carrier)
    (hno : ¬ ∃ y, (x, y) ∈ T.realEdge)
    (htarget : x ∉ Gamma.target) : False := by
  obtain ⟨R⟩ := T.resolve x hx hno htarget
  have hne : R.path.start ≠ R.path.finish := by
    intro h
    apply htarget
    rw [← R.start, h]
    exact R.finish
  obtain ⟨y, hy⟩ :=
    Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      R.path R.path.start_mem_support hne
  rw [R.start] at hy
  exact hno ⟨y, R.edges hy⟩

/-- The one and only stage of the closed transaction. -/
inductive StageIndex : Type
  | stage

namespace StageIndex

instance : Nonempty StageIndex := ⟨.stage⟩

instance : Preorder StageIndex where
  le _ _ := True
  le_refl _ := True.intro
  le_trans _ _ _ _ _ := True.intro

instance : IsDirectedOrder StageIndex where
  directed _ _ := ⟨.stage, True.intro, True.intro⟩

end StageIndex

/-- A closed simultaneous transaction induces a genuine cofinal run with
one constant stage. -/
def cofinalRun (T : SingleGlobalClubStageTransaction C) :
    CofinalClubStageRun C StageIndex where
  blueprint := fun _ => T.blueprint
  fractured := fun _ => T.fractured
  assignment := fun _ => T.assignment
  scheduled := fun _ => T.anchor
  data := fun _ => T.data
  realEdge_mono := fun _ _ _ => Set.Subset.rfl
  carrier_mono := fun _ _ _ => Set.Subset.rfl
  countably_bounded := by
    intro _
    exact ⟨.stage, fun _ => True.intro⟩
  fair := by
    intro x hx hno htarget
    exfalso
    apply T.no_nonTarget_sink x
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact hi
    · rintro ⟨y, hxy⟩
      apply hno
      exact ⟨y, Set.mem_iUnion.2 ⟨.stage, hxy⟩⟩
    · exact htarget

/-- Compile the closed simultaneous transaction to the exact ranked fair
global relation.  Its global rank is constructed by the cofinal-run theorem,
not supplied by the transaction. -/
def rankedFairGlobalRelation (T : SingleGlobalClubStageTransaction C) :
    CardinalInduction.HalfwayScheduler.RankedFairGlobalRelation
      Gamma Y kappa Gamma.target StageIndex :=
  T.cofinalRun.rankedFairGlobalRelation

@[simp] theorem cofinalRun_finalEdge
    (T : SingleGlobalClubStageTransaction C) :
    T.cofinalRun.finalEdge = T.realEdge := by
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
    exact hi
  · intro e he
    exact Set.mem_iUnion.2 ⟨.stage, he⟩

@[simp] theorem cofinalRun_finalCarrier
    (T : SingleGlobalClubStageTransaction C) :
    T.cofinalRun.finalCarrier = T.data.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact hi
  · intro x hx
    exact Set.mem_iUnion.2 ⟨.stage, hx⟩

@[simp] theorem ranked_edge
    (T : SingleGlobalClubStageTransaction C) :
    T.rankedFairGlobalRelation.edge = T.realEdge :=
  T.cofinalRun_finalEdge

@[simp] theorem ranked_carrier
    (T : SingleGlobalClubStageTransaction C) :
    T.rankedFairGlobalRelation.carrier = T.data.carrier :=
  T.cofinalRun_finalCarrier

end SingleGlobalClubStageTransaction

end LinkageBlueprint
end Blueprint
end Erdos599
