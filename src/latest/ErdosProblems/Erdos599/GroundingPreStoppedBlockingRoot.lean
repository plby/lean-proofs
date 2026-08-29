/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingBlockingPrefix
import ErdosProblems.Erdos599.GroundingPreStoppedRealization

/-!
# Rooting a blocking prefix in the pre-stopped switch

With stopping frontier `∅`, the only reasons a residual fragment edge can
be absent from the switched relation are selection as a backward edge or a
forward-incidence conflict.  This file packages that exact reduction for the
canonical prefix ending at a blocking point.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingBlockingPrefix

open GroundingErasedDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- A canonical residual prefix is contained in the pre-stopped relation
once it avoids the two genuine selected-route toggle classes. -/
theorem Data.edgeSet_subset_preStopped_of_disjoint_selected
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    {P : L.Fragment} (D : Data L S.cut P)
    (hbackward : Disjoint D.path.edgeSet
      (erasedSelectedDirectionEdgesAt U S K (∅ : Set V) .backward))
    (hconflict : Disjoint D.path.edgeSet
      (forwardConflictCutEdgesAt U S K (∅ : Set V))) :
    D.path.edgeSet ⊆ erasedSelectedSwitchedEdgesAt U S K ∅ := by
  rw [erasedSelectedSwitchedEdgesAt_empty_eq]
  intro e he
  left
  refine ⟨D.edgeSet_subset_residual he, ?_⟩
  rintro (heBackward | heConflict)
  · exact Set.disjoint_left.1 hbackward he heBackward
  · exact Set.disjoint_left.1 hconflict he heConflict

end GroundingBlockingPrefix

namespace DWeb.KappaLadder

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The blocking point of a retained fragment is pre-stopped-rooted from
any allowed root reaching the fragment initial, provided the canonical
prefix avoids the two selected toggle classes. -/
theorem UnusedGroundedRecord.exists_blockingPoint_rooted_preStopped
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hPblockable : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ L.assertion822ReservedPreStoppedEdges
          hL S R) a P.path.initial)
    (hbackward : Disjoint
      (GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P hPblockable).path.edgeSet
      (erasedSelectedDirectionEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V) .backward))
    (hconflict : Disjoint
      (GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P hPblockable).path.edgeSet
      (forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ L.assertion822ReservedPreStoppedEdges
          hL S R) a
        (GroundingCut.blockingPoint
          (L.popularAuxiliaryInput hL.legal) S.cut P) := by
  let D := GroundingBlockingPrefix.data
    (L.popularAuxiliaryInput hL.legal) S.cut P hPblockable
  obtain ⟨a, ha, haroot⟩ := hstart
  refine ⟨a, ha, haroot.trans ?_⟩
  have hpath : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ L.assertion822ReservedPreStoppedEdges
        hL S R) D.path.start D.path.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.path.edgeSet)
      (p := fun x y ↦ (x, y) ∈
        L.assertion822ReservedPreStoppedEdges hL S R)
    · intro x y hxy
      exact D.edgeSet_subset_preStopped_of_disjoint_selected
        (L.reservedGroundedControls hL S R) hbackward hconflict hxy
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet
        D.path.walk
  exact D.finish_eq ▸ (D.start_eq ▸ hpath)

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.GroundingBlockingPrefix.Data.edgeSet_subset_preStopped_of_disjoint_selected
#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.exists_blockingPoint_rooted_preStopped
