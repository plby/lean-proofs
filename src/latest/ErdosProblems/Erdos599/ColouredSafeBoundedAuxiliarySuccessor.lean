/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeAuxiliaryForwardContainment

/-!
# Actual auxiliary successors stay in the original saturation carrier

The successor is the existing single-source construction with its real
fragment witnesses retained. The original carrier need not be closed under
arbitrary forward owners: safe stopping supplies precisely the closure
needed by the fragment that this successor constructs.
-/

namespace Erdos599.Alternating.ColouredSafeBoundedAuxiliarySuccessor

open Set DirectedPath FiniteColouredOccurrenceWord ColouredSafeReverseReachability
open ColouredSafeAuxiliaryForwardContainment

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y C : Set Gamma.DPath}

theorem exists_successor_in_saturation
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hYC : Gamma.IsWarp (Y ∪ C)) (hYCfin : Gamma.HasFiniteCharacter (Y ∪ C))
    (hdisjoint : Disjoint (Gamma.vertexSet Y) (Gamma.vertexSet C))
    (hsource : Gamma.initialSet (Y ∪ C) ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet (Y ∪ C) ⊆
      Gamma.terminalFrontier (Y ∪ C))
    {J : Set (ExposedInitial W Y)}
    (hCtails : ∀ {x y}, (x, y) ∈ familyEdges C → x ∈ Subtype.val '' J)
    (hCV : Gamma.vertexSet C ⊆ Subtype.val '' J ∪ safeTerminalUnion J)
    (hinternal : ∀ {a b}, (a, b) ∈ familyEdges W → a ∈ Gamma.vertexSet Y →
      b ∈ Gamma.vertexSet Y → b ∉ Gamma.initialSet Y →
      a ∉ Gamma.terminalFrontier Y → (a, b) ∈ familyEdges Y)
    {s : V} (hsJ : s ∈ Subtype.val '' J) (hsOff : s ∉ Gamma.vertexSet (Y ∪ C))
    (S : SafePrefixState W (Y ∪ C) s)
    (hSH : S.word.vertexSet ⊆ finiteSaturationCarrier hW hY J) :
    ∃ T : SafePrefixState W (Y ∪ C) s,
      S.word.Prefix T.word ∧ S.word.length < T.word.length ∧
        T.word.vertexSet ⊆ finiteSaturationCarrier hW hY J := by
  have hs : s ∈ Gamma.initialSet W := by
    obtain ⟨r, _hrJ, rfl⟩ := hsJ
    exact r.2.1
  obtain ⟨T, hprefix, hlength, F, hFE, hTV⟩ := S.exists_successor_with_fragments
    hW hYC hWfin hYCfin hsource hterminal hs hsOff
  have hYI : Gamma.initialSet Y ⊆ Gamma.initialSet (Y ∪ C) := by
    rw [DWeb.initialSet_union]
    exact Set.subset_union_left
  have hYT : Gamma.terminalFrontier Y ⊆ Gamma.terminalFrontier (Y ∪ C) := by
    rw [DWeb.terminalFrontier_union]
    exact Set.subset_union_left
  have hFInternal : ∀ {a b}, (a, b) ∈ F.path.edgeSet → a ∈ Gamma.vertexSet Y →
      b ∈ Gamma.vertexSet Y → (a, b) ∈ familyEdges Y := by
    intro a b he ha hb
    have hpure := T.safe.endpoint_pure (hFE he)
    exact hinternal (F.edges he) ha hb (fun h ↦ hpure.1 (hYI h))
      (fun h ↦ hpure.2 (hYT h))
  have hstart : F.path.start ∈ Gamma.vertexSet (Y ∪ C) →
      HasOutgoing S.word.backwardEdges F.path.start := by
    intro haY
    rcases S.phase with ⟨_hzero, haFirst⟩ | hback
    · apply False.elim
      apply hsOff
      simpa only [← F.join, haFirst] using haY
    · simpa only [F.join] using hback
  have hFH : F.path.support ⊆ finiteSaturationCarrier hW hY J :=
    forward_support_subset_saturation hW hY hWfin hYfin hYC hYCfin hdisjoint
      hCtails hCV S.word S.safe
      (by simpa only [S.first_eq] using hsJ) (by simpa only [S.first_eq] using hsOff)
      hSH F.path F.nontrivial F.join F.edges F.fresh
      ⟨Sum.inl F.owner, F.owner_mem, F.finish_mem⟩ hstart F.contact_geometry hFInternal
  have hownerH : F.owner.support ⊆ finiteSaturationCarrier hW hY J := by
    rcases F.owner_mem with hpY | hpC
    · have hbound := finiteSaturationCarrier_referenceClosed hW hY J
        (hFH F.path.finish_mem_support)
      rw [coveredPathSupport_eq_of_mem hY hpY F.finish_mem] at hbound
      exact hbound
    · intro x hx
      exact source_or_safeTerminal_mem_saturation hW hY hWfin hYfin
        (hCV ⟨Sum.inl F.owner, hpC, hx⟩)
  refine ⟨T, hprefix, hlength, ?_⟩
  exact hTV.trans (Set.union_subset (Set.union_subset hSH hFH) hownerH)

#print axioms exists_successor_in_saturation

end Erdos599.Alternating.ColouredSafeBoundedAuxiliarySuccessor
