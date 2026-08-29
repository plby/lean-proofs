/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMacroStageAccounting
import ErdosProblems.Erdos599.HalfwaySingleGlobalTransaction

/-!
# A simultaneous marker-absorbed macro transaction

A fixed marker-absorbed request has one common relation and one common
carrier.  If the source construction supplies genuine continuation data for
every alleged non-target real sink of that relation, each continuation gives
an actual finite target route embedded in the same relation.  Thus the
request is a `SingleGlobalClubStageTransaction`.

This is the chronology-safe scheduler interface for a simultaneous macro
stage.  Repeating the resulting closed transaction over the successor-cardinal
stage order gives an actual monotone, fair `SuccessorClubStageRun`; no common
rank, monotonicity, or fairness certificate is assumed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace MarkerAbsorbedMacroRequest

variable {S : MarkerAbsorbedMacroSeed
  (Gamma := Gamma) (Y := Y) (kappa := kappa)}
variable {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}
variable {old : LinkageBlueprint Gamma Y kappa} {u x : V}

/-- Continuation data for any vertex uses the same marker-absorbed carrier,
independently of the scheduled vertex stored in its target route. -/
theorem continuation_targetPath_support
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u)
    (D : R.MacroStageContinuationData C old x) :
    D.targetPath.support ⊆ D₀.toClubStageUnionData.carrier := by
  exact D.targetPath_vertices

/-- Continuation data for any vertex uses the same marker-absorbed real
relation, independently of the scheduled vertex stored in its target route. -/
theorem continuation_targetPath_edges
    (R : MarkerAbsorbedMacroRequest S)
    (D : R.MacroStageContinuationData C old x) :
    D.targetPath.edgeSet ⊆ relationRealEdges (Gamma := Gamma)
      R.macroEdge := by
  exact D.targetPath_edges

/-- An honest continuation at `x` is an embedded route in the fixed anchor
transaction.  The key point is that `D₀` and `D` differ only in their stored
target paths; their inside relation, assignment, and carrier are the same
fixed objects constructed by `R`. -/
def embeddedTargetRoute
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u)
    (D : R.MacroStageContinuationData C old x) :
    EmbeddedTransactionTargetRoute D₀.toClubStageUnionData x where
  path := D.targetPath
  start := D.targetPath_start
  finish := D.targetPath_finish
  support := R.continuation_targetPath_support D₀ D
  edges := R.continuation_targetPath_edges D

/-- A common marker-absorbed request, one anchor continuation, and genuine
continuation data for every alleged unresolved real sink form a closed
simultaneous transaction.

The `resolve` argument is source-level path/row/closure data, rather than a
fairness or scheduler conclusion. -/
def toSingleGlobalClubStageTransaction
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u)
    (resolve : ∀ x,
      x ∈ R.inside.insideFamily.vertexSet →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) R.macroEdge) →
      x ∉ Gamma.target →
      Nonempty (R.MacroStageContinuationData C old x)) :
    SingleGlobalClubStageTransaction C where
  blueprint := old
  fractured := FracturedWarp.ofWarp
    (outsideReference S.later R.closureSet)
    (outsideReference_isWarp S.later_isWarp)
  assignment := R.assignment.assignment
  anchor := u
  data := D₀.toClubStageUnionData
  resolve := by
    intro x hx hno htarget
    obtain ⟨D⟩ := resolve x hx hno htarget
    exact ⟨R.embeddedTargetRoute D₀ D⟩

/-- Repeat the actually closed common macro transaction over the actual
successor-cardinal ladder.  Relation and carrier monotonicity are
definitional, and fairness is proved from the supplied target routes. -/
def toSuccessorClubStageRun
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u)
    (resolve : ∀ x,
      x ∈ R.inside.insideFamily.vertexSet →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) R.macroEdge) →
      x ∉ Gamma.target →
      Nonempty (R.MacroStageContinuationData C old x)) :
    SuccessorClubStageRun C := by
  let T := R.toSingleGlobalClubStageTransaction D₀ resolve
  exact {
    blueprint := fun _ ↦ T.blueprint
    fractured := fun _ ↦ T.fractured
    assignment := fun _ ↦ T.assignment
    scheduled := fun _ ↦ T.anchor
    data := fun _ ↦ T.data
    realEdge_mono := fun _ _ _ ↦ Set.Subset.rfl
    carrier_mono := fun _ _ _ ↦ Set.Subset.rfl
    fair := by
      intro x hx hno htarget
      exfalso
      apply T.no_nonTarget_sink x
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        exact hi
      · rintro ⟨y, hxy⟩
        apply hno
        exact ⟨y, Set.mem_iUnion.2 ⟨Classical.arbitrary _, hxy⟩⟩
      · exact htarget }

/-- The common transaction retains exactly the original-web filter of the
macro relation. -/
@[simp] theorem toSingleGlobalClubStageTransaction_realEdge
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u)
    (resolve : ∀ x,
      x ∈ R.inside.insideFamily.vertexSet →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) R.macroEdge) →
      x ∉ Gamma.target →
      Nonempty (R.MacroStageContinuationData C old x)) :
    (R.toSingleGlobalClubStageTransaction D₀ resolve).realEdge =
      relationRealEdges (Gamma := Gamma) R.macroEdge := rfl

/-- At every repeated successor stage, the exact carrier is the canonical
inside carrier of the marker-absorbed request. -/
@[simp] theorem toSingleGlobalClubStageTransaction_carrier
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u)
    (resolve : ∀ x,
      x ∈ R.inside.insideFamily.vertexSet →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) R.macroEdge) →
      x ∉ Gamma.target →
      Nonempty (R.MacroStageContinuationData C old x)) :
    (R.toSingleGlobalClubStageTransaction D₀ resolve).data.carrier =
      R.inside.insideFamily.vertexSet := rfl

/-- After passage to the cofinal union, the final real relation is still
exactly the real part of the fixed macro relation. -/
@[simp] theorem toSuccessorClubStageRun_finalEdge
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u)
    (resolve : ∀ x,
      x ∈ R.inside.insideFamily.vertexSet →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) R.macroEdge) →
      x ∉ Gamma.target →
      Nonempty (R.MacroStageContinuationData C old x))
    (hkappa : aleph0 ≤ kappa) :
    ((R.toSuccessorClubStageRun D₀ resolve).toCofinalRun hkappa).finalEdge =
      relationRealEdges (Gamma := Gamma) R.macroEdge := by
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
    exact hi
  · intro e he
    exact Set.mem_iUnion.2 ⟨Classical.arbitrary _, he⟩

/-- After passage to the cofinal union, the final carrier is still exactly
the fixed canonical inside carrier. -/
@[simp] theorem toSuccessorClubStageRun_finalCarrier
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u)
    (resolve : ∀ x,
      x ∈ R.inside.insideFamily.vertexSet →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) R.macroEdge) →
      x ∉ Gamma.target →
      Nonempty (R.MacroStageContinuationData C old x))
    (hkappa : aleph0 ≤ kappa) :
    ((R.toSuccessorClubStageRun D₀ resolve).toCofinalRun hkappa).finalCarrier =
      R.inside.insideFamily.vertexSet := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact hi
  · intro x hx
    exact Set.mem_iUnion.2 ⟨Classical.arbitrary _, hx⟩

/-- The fixed macro relation has no forward ray.  This is the genuine
finite-character geometry of the later row, not a consequence of deleting
imaginary edges. -/
theorem macroEdge_noDirectedRay
    (R : MarkerAbsorbedMacroRequest S) :
    ¬ ContainsDirectedRay R.macroEdge := by
  exact R.inside.macroFullRelation_noDirectedRay R.assignment
    S.later_isWarp S.later_finite R.outside_subset

/-- Consequently the exact final real relation of the repeated transaction
also has no forward ray. -/
theorem toSuccessorClubStageRun_finalEdge_noDirectedRay
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u)
    (resolve : ∀ x,
      x ∈ R.inside.insideFamily.vertexSet →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) R.macroEdge) →
      x ∉ Gamma.target →
      Nonempty (R.MacroStageContinuationData C old x))
    (hkappa : aleph0 ≤ kappa) :
    ¬ ContainsDirectedRay
      ((R.toSuccessorClubStageRun D₀ resolve).toCofinalRun hkappa).finalEdge := by
  rw [R.toSuccessorClubStageRun_finalEdge D₀ resolve hkappa]
  rintro ⟨r, hr⟩
  apply R.macroEdge_noDirectedRay
  refine ⟨r, ?_⟩
  intro e he
  exact (hr he).1

/-- Source coverage is retained by the exact common macro datum.  This is
the source-level `macroCoversSource` theorem transported to the scheduler
object, not a separate coverage assumption. -/
theorem toSingleGlobalClubStageTransaction_coversSource
    (R : MarkerAbsorbedMacroRequest S)
    (D₀ : R.MacroStageContinuationData C old u) :
    Gamma.source ⊆
      {x | x ∈ R.inside.insideFamily.vertexSet ∧
        ¬ ∃ y, (y, x) ∈ R.macroEdge} ∪
      Gamma.initialSet
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y R.inside.insideFamily.vertexSet) := by
  exact D₀.toClubStageUnionData.covers_source

end MarkerAbsorbedMacroRequest

end LinkageBlueprint
end Blueprint
end Erdos599
