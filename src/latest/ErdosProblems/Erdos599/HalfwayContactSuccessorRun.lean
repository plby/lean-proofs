/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayContactTransaction
import ErdosProblems.Erdos599.HalfwaySingleGlobalTransaction

/-!
# Repeating a retained contact transaction

This scheduler-facing adapter is kept separate from the contact splitter so
the finite contact-order and ownership construction can be checked without
depending on the global scheduler.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace SingleGlobalClubStageTransaction

variable {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}

/-- Repeat one genuinely closed global transaction over the actual
successor-cardinal stage order. -/
def successorRun (T : SingleGlobalClubStageTransaction C) :
    SuccessorClubStageRun C where
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
    · exact htarget

/-- The final real relation of the successor run is exactly the real
relation of the retained global transaction. -/
@[simp] theorem successorRun_finalEdge
    (T : SingleGlobalClubStageTransaction C) (hkappa : aleph0 ≤ kappa) :
    (T.successorRun.toCofinalRun hkappa).finalEdge = T.realEdge := by
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
    exact hi
  · intro e he
    exact Set.mem_iUnion.2 ⟨Classical.arbitrary _, he⟩

/-- The final carrier is exactly the retained transaction carrier. -/
@[simp] theorem successorRun_finalCarrier
    (T : SingleGlobalClubStageTransaction C) (hkappa : aleph0 ≤ kappa) :
    (T.successorRun.toCofinalRun hkappa).finalCarrier = T.data.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact hi
  · intro x hx
    exact Set.mem_iUnion.2 ⟨Classical.arbitrary _, hx⟩

end SingleGlobalClubStageTransaction

end LinkageBlueprint
end Blueprint
end Erdos599
