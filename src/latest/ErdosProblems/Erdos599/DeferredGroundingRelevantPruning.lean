/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingCutAvoidingSelection
import ErdosProblems.Erdos599.GroundingInputRelevantPruning

/-!
# Relevant-fragment pruning for a deferred cut-avoiding record

The generic pruning data is instantiated by the single grounded deferred
record whose whole auxiliary trace avoids the popular cut.  Its limiting
inessentiality excludes it from every essential-terminal fragment, and the
trace argument proves that a whole fragment on it cannot meet the relaxed
escape region.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
variable {K : GroundingSelection.Controls S}

namespace DeferredCutAvoidingRecord

/-- Input-level pruning data which deletes exactly the whole reserved
deferred record. -/
def relevantPruningData
    (R : DeferredCutAvoidingRecord L hL S K) :
    GroundingInputRelevantPruning.Data
      (popularAuxiliaryInput L hL.legal) S.cut where
  discarded := {R.record}
  discarded_not_essential := by
    intro p hp hessential
    have hpEq : p = R.record := Set.mem_singleton_iff.mp hp
    exact R.limit_inessential.2 (hpEq ▸ hessential)
  whole_discarded_not_meetsEscape := by
    intro P hfragment hwhole hdiscarded
    have hparent : P.parent = R.record :=
      Set.mem_singleton_iff.mp hdiscarded
    exact R.wholeRecord_not_meetsEscape P hfragment hparent hwhole

/-- The relevant deferred boundary attached to the actual cut-avoiding
record. -/
def relevantBB (R : DeferredCutAvoidingRecord L hL S K) : Set V :=
  (R.relevantPruningData).relevantBB

theorem relevantBB_subset_legacyBB
    (R : DeferredCutAvoidingRecord L hL S K) :
    R.relevantBB ⊆ GroundingCut.BB
      (popularAuxiliaryInput L hL.legal) S.cut :=
  R.relevantPruningData.relevantBB_subset_legacyBB

theorem fragment_meeting_escape_mem_relevantG0
    (R : DeferredCutAvoidingRecord L hL S K)
    (P : (popularAuxiliaryInput L hL.legal).Fragment)
    (hfragment : P ∈ GroundingCut.fragments
      (popularAuxiliaryInput L hL.legal) S.cut)
    (hescape : P.MeetsEscape
      (popularAuxiliaryInput L hL.legal) S.cut) :
    P ∈ R.relevantPruningData.relevantG0 :=
  R.relevantPruningData.fragment_meeting_escape_mem_relevantG0
    P hfragment hescape

end DeferredCutAvoidingRecord
end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.DeferredCutAvoidingRecord.relevantPruningData
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.DeferredCutAvoidingRecord.fragment_meeting_escape_mem_relevantG0
