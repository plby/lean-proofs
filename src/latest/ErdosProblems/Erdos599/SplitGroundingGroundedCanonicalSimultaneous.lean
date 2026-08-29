/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReservedControls

/-!
# Canonical reserved simultaneous switch for the grounded split branch

We first choose an omitted grounded stage for the unrefined strict controls,
then reserve its entire auxiliary carrier and reselect every request path.
The reservation itself proves that the same stage is still omitted.  This
breaks the apparent circularity between choosing the missing source and
protecting it from backward links.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingErasedDecode GroundingErasedSwitchRelation
  GroundingErasedForwardConflict
open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Initial stationary choice, made before the reserved-carrier refinement. -/
noncomputable def splitGroundedCanonicalBaseUnusedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    L.SplitGroundedUnusedRecord hL hground S
      (L.splitGroundedControls hL hground S) :=
  Classical.choice (L.exists_splitGroundedUnusedRecord hL hground S
    (L.splitGroundedControls hL hground S))

/-- Canonical final controls, with the omitted record fixed and protected. -/
noncomputable def splitGroundedCanonicalControls
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    GroundingSelection.Controls S :=
  splitGroundedReservedControls
    (L.splitGroundedCanonicalBaseUnusedRecord hL hground S)

/-- The same record, now certified unused for the final canonical controls. -/
noncomputable def splitGroundedCanonicalUnusedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    L.SplitGroundedUnusedRecord hL hground S
      (L.splitGroundedCanonicalControls hL hground S) :=
  (L.splitGroundedCanonicalBaseUnusedRecord hL hground S).forReservedControls

/-- Canonical final switch stopped at an ambient boundary. -/
abbrev splitGroundedCanonicalSwitchedEdgesAt
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (L.splitGroundedCanonicalControls hL hground S) T

theorem splitGroundedCanonicalSwitchedEdgesAt_subset_adj
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (T : Set V) :
    L.splitGroundedCanonicalSwitchedEdgesAt hL hground S T ⊆
      {e | Gamma.graph.Adj e.1 e.2} :=
  erasedSelectedSwitchedEdgesAt_subset_adj
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedCanonicalControls hL hground S) T

theorem splitGroundedCanonicalSwitchedEdgesAt_biUnique
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (T : Set V) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ L.splitGroundedCanonicalSwitchedEdgesAt hL hground S T) :=
  erasedSelectedSwitchedEdgesAt_biUnique
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedCanonicalControls hL hground S) T
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)

theorem splitGroundedCanonicalSwitchedEdgesAt_reachabilityAntichain
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (T : Set V) :
    IsReachabilityAntichain
      (L.splitGroundedCanonicalSwitchedEdgesAt hL hground S T) T := by
  intro b hb c _hc hbc
  exact GroundingBlockingReachability.eq_of_reflTransGen_of_noOutgoing
    (boundary_noOutgoing_switchedAt
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedCanonicalControls hL hground S) T hb) hbc

/-- Canonical backward-owner normalization.  A finally selected backward
link is never owned by the omitted record; its owner either has an
allowed-source prefix or is the explicit equal-stage hanging case. -/
theorem splitGroundedCanonicalBackwardOwner_rootPrefix_or_equalMatch
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (L.splitGroundedCanonicalControls hL hground S) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent) :
    (∃ q : DirectedPath.FinitePath Gamma.graph,
      q.start ∈ Gamma.source \ {
        (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial} ∧
      q.finish = l.path.start ∧ q.support ⊆ parent.support ∧
      q.edgeSet ⊆ parent.edgeSet) ∨
    let p := GroundingSimultaneousDecode.strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (L.splitGroundedCanonicalControls hL hground S) r
    let hp : p.start ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source :=
      (GroundingSimultaneousDecode.strongSelectedWarp
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (L.splitGroundedCanonicalControls hL hground S)).starts_in_source
            ⟨r, rfl⟩
    Nonempty (L.SplitGroundedAssertion819EqualMatch hL hground S r
      ((L.splitGroundedPopularAuxiliaryIndexed hL hground).f
        ⟨p.start, hp⟩)) := by
  let R0 := L.splitGroundedCanonicalBaseUnusedRecord hL hground S
  have h := splitGroundedReservedBackwardOwner_rootPrefix_or_equalMatch
    R0 r l hl hldir parent hparent hsub
  simpa only [splitGroundedCanonicalControls,
    splitGroundedCanonicalUnusedRecord,
    SplitGroundedUnusedRecord.forReservedControls] using h

/-- Canonical 8.22 output once the literal grounded boundary is rooted away
from the now protected omitted source. -/
theorem splitGroundedCanonicalAssertion822Output_of_BB_rooted
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (hroot : ∀ t ∈ GroundingCut.BB
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source \ {
          (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.splitGroundedCanonicalSwitchedEdgesAt hL hground S
              (GroundingCut.BB
                (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) := by
  let R := L.splitGroundedCanonicalUnusedRecord hL hground S
  let T := GroundingCut.BB
    (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut
    (L.splitGroundedCanonicalSwitchedEdgesAt hL hground S T)
    (Gamma.source \ {R.record.initial}) T
    (L.splitGroundedCanonicalSwitchedEdgesAt_subset_adj hL hground S T)
    (L.splitGroundedCanonicalSwitchedEdgesAt_biUnique hL hground S T)
    Set.sdiff_subset Subset.rfl
    (L.splitGroundedAssertion8_18 hL.legal S.cut S.separates)
    (L.splitGroundedCanonicalSwitchedEdgesAt_reachabilityAntichain
      hL hground S T)
    hroot R.record.initial R.grounded
  simp

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.splitGroundedCanonicalAssertion822Output_of_BB_rooted
