/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceSourceRestriction
import ErdosProblems.Erdos599.SingularFiniteAugmentationEndpointComponent
import ErdosProblems.Erdos599.Blueprint

/-!
# Finite endpoint count behind the fixed-forward Hall inequality

For two finite families, endpoint purity already gives the numerical Hall
inequality at the level of whole path owners.  Every reference initial is a
forward initial, and the forward initials lying on the reference carrier are
reference initials.  Dually, every forward terminal on the reference carrier
is a reference terminal.  Equality of initial and terminal counts in each
finite-character warp then leaves at least as many off-reference forward
terminals as exposed forward initials.

This theorem is only the owner-component counting part of the argument.  It
does not assert that the counted terminals have interval-safe occurrence-word
witnesses; the simultaneous owner-gap factorization must establish that.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath
open CardinalInduction.SingularFiniteAugmentationEndpointComponent

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

private theorem terminalFrontier_finite_of_family_finite
    (Z : Set Gamma.DPath) (hZ : Z.Finite) :
    (Gamma.terminalFrontier Z).Finite := by
  have himage : (Gamma.terminal? '' Z).Finite := hZ.image Gamma.terminal?
  have hpreimage : (some ⁻¹' (Gamma.terminal? '' Z)).Finite :=
    himage.preimage
      (Set.injOn_of_injective (Option.some_injective V))
  apply hpreimage.subset
  rintro x ⟨p, hpZ, hpx⟩
  exact ⟨p, hpZ, hpx⟩

/-- Finite whole-owner endpoint count.  The hypotheses are exactly the two
boundary-purity directions used by the safe occurrence construction. -/
theorem ncard_exposedInitial_le_offReferenceTerminal
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (hWfamily : W.Finite) (hYfamily : Y.Finite)
    (hinitial_sub : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial_pure : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal_pure : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y) :
    (Gamma.initialSet W \ Gamma.vertexSet Y).ncard ≤
      (Gamma.terminalFrontier W \ Gamma.vertexSet Y).ncard := by
  have hIWfinite : (Gamma.initialSet W).Finite := by
    simpa only [DWeb.initialSet] using
      hWfamily.image (fun p : Gamma.DPath ↦ p.initial)
  have hIYfinite : (Gamma.initialSet Y).Finite := by
    simpa only [DWeb.initialSet] using
      hYfamily.image (fun p : Gamma.DPath ↦ p.initial)
  have hTWfinite : (Gamma.terminalFrontier W).Finite :=
    terminalFrontier_finite_of_family_finite W hWfamily
  have hTYfinite : (Gamma.terminalFrontier Y).Finite :=
    terminalFrontier_finite_of_family_finite Y hYfamily
  have hIYeq : Gamma.initialSet Y =
      Gamma.initialSet W ∩ Gamma.vertexSet Y := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hinitial_sub hx, initialSet_subset_vertexSet Y hx⟩
    · exact hinitial_pure
  have hterminalCard :
      (Gamma.terminalFrontier W ∩ Gamma.vertexSet Y).ncard ≤
        (Gamma.terminalFrontier Y).ncard :=
    Set.ncard_le_ncard hterminal_pure hTYfinite
  have hWcount : (Gamma.initialSet W).ncard =
      (Gamma.terminalFrontier W).ncard :=
    ncard_initialSet_eq_terminalFrontier hW hWfin
  have hYcount : (Gamma.initialSet Y).ncard =
      (Gamma.terminalFrontier Y).ncard :=
    ncard_initialSet_eq_terminalFrontier hY hYfin
  have hInitialSplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (Gamma.initialSet W) (Gamma.vertexSet Y) hIWfinite
  have hTerminalSplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (Gamma.terminalFrontier W) (Gamma.vertexSet Y) hTWfinite
  rw [← hIYeq, hYcount] at hInitialSplit
  omega

/-- A finite carrier which is closed under both path families gives a
genuine finite whole-owner instance of the endpoint count.  This is the
finite-carrier bridge needed before an owner-gap factorization: no path is
truncated at an artificial initial or terminal. -/
theorem ncard_closedPart_exposedInitial_le_offReferenceTerminal
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {C : Set V} (hC : C.Finite)
    (hWclosed : _root_.Erdos599.Blueprint.ClosedUnderPaths Gamma W C)
    (hYclosed : _root_.Erdos599.Blueprint.ClosedUnderPaths Gamma Y C)
    (hinitial_sub : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial_pure : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal_pure : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y) :
    let WC := _root_.Erdos599.CardinalInduction.SliceCandidate.initialPart
      Gamma W C
    let YC := _root_.Erdos599.CardinalInduction.SliceCandidate.initialPart
      Gamma Y C
    (Gamma.initialSet WC \ Gamma.vertexSet YC).ncard ≤
      (Gamma.terminalFrontier WC \ Gamma.vertexSet YC).ncard := by
  let WC := _root_.Erdos599.CardinalInduction.SliceCandidate.initialPart
    Gamma W C
  let YC := _root_.Erdos599.CardinalInduction.SliceCandidate.initialPart
    Gamma Y C
  have hWCfinite : WC.Finite := by
    apply FamilyTools.finite_of_pairwiseDisjoint_of_meets
      (F := fun p : Gamma.DPath ↦ p.support) (S := C)
    · intro p hp q hq hpq
      exact hW hp.1 hq.1 hpq
    · exact hC
    · intro p hp
      exact ⟨p.initial, hp.2, p.initial_mem_support⟩
  have hYCfinite : YC.Finite := by
    apply FamilyTools.finite_of_pairwiseDisjoint_of_meets
      (F := fun p : Gamma.DPath ↦ p.support) (S := C)
    · intro p hp q hq hpq
      exact hY hp.1 hq.1 hpq
    · exact hC
    · intro p hp
      exact ⟨p.initial, hp.2, p.initial_mem_support⟩
  have hWCwarp : Gamma.IsWarp WC := fun p hp q hq hpq ↦
    hW hp.1 hq.1 hpq
  have hYCwarp : Gamma.IsWarp YC := fun p hp q hq hpq ↦
    hY hp.1 hq.1 hpq
  have hWCcharacter : Gamma.HasFiniteCharacter WC := fun {_p} hp ↦ hWfin hp.1
  have hYCcharacter : Gamma.HasFiniteCharacter YC := fun {_p} hp ↦ hYfin hp.1
  have hlocalInitialSub : Gamma.initialSet YC ⊆ Gamma.initialSet WC := by
    rw [_root_.Erdos599.CardinalInduction.SliceCandidate.initialSet_initialPart,
      _root_.Erdos599.CardinalInduction.SliceCandidate.initialSet_initialPart]
    rintro x ⟨hxY, hxC⟩
    exact ⟨hinitial_sub hxY, hxC⟩
  have hlocalInitialPure :
      Gamma.initialSet WC ∩ Gamma.vertexSet YC ⊆ Gamma.initialSet YC := by
    rintro x ⟨hxW, p, hpYC, hxp⟩
    rw [_root_.Erdos599.CardinalInduction.SliceCandidate.initialSet_initialPart]
      at hxW ⊢
    refine ⟨hinitial_pure ⟨hxW.1, ?_⟩, hxW.2⟩
    exact ⟨p, hpYC.1, hxp⟩
  have hlocalTerminalPure :
      Gamma.terminalFrontier WC ∩ Gamma.vertexSet YC ⊆
        Gamma.terminalFrontier YC := by
    rintro x ⟨⟨p, hpWC, hpx⟩, q, hqYC, hxq⟩
    have hxC : x ∈ C :=
      hWclosed p hpWC.1 ⟨p.initial, p.initial_mem_support, hpWC.2⟩
        (Gamma.terminal_mem_support hpx)
    have hxTY : x ∈ Gamma.terminalFrontier Y :=
      hterminal_pure ⟨⟨p, hpWC.1, hpx⟩, q, hqYC.1, hxq⟩
    obtain ⟨r, hrY, hrx⟩ := hxTY
    have hrC : r.support ⊆ C :=
      hYclosed r hrY ⟨x, Gamma.terminal_mem_support hrx, hxC⟩
    exact ⟨r, ⟨hrY, hrC r.initial_mem_support⟩, hrx⟩
  exact ncard_exposedInitial_le_offReferenceTerminal
    hWCwarp hYCwarp hWCcharacter hYCcharacter hWCfinite hYCfinite
    hlocalInitialSub hlocalInitialPure hlocalTerminalPure

#print axioms ncard_exposedInitial_le_offReferenceTerminal
#print axioms ncard_closedPart_exposedInitial_le_offReferenceTerminal

end Erdos599.Alternating.FiniteColouredOccurrenceWord
