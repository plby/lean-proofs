/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReducedCut

/-!
# The descent-relevant split grounding cut

The finite descent proving Assertion 8.18 does not use every blockable
fragment in the source-correct reduced family.  Its seed is the fragment
containing the terminal point of an essential limiting path, while every
fragment introduced recursively has a genuine relaxed escape.  We retain
exactly those two cases.

This removes finite escape-free fragments of inessential hanging parents.
Such fragments supplied artificial blocking points but no selected request
capable of rooting them in Assertion 8.22.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev RelevantInput (L : Gamma.KappaLadder kappa)
    (hL : L.IsSplitLegal) :=
  L.splitGroundedPopularAuxiliaryInput hL

private abbrev RelevantLV (L : Gamma.KappaLadder kappa)
    (_hL : L.IsSplitLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-- The part of reduced `G0` actually used by the last-fragment descent:
an escaping fragment, or a finite fragment ending at the global essential
terminal cut.  The displayed terminal equality already witnesses finiteness. -/
def splitGroundedRelevantG0
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) :
    Set (RelevantInput L hL).Fragment :=
  L.splitGroundedG0 hL C ∩
    {P | P.MeetsEscape (RelevantInput L hL) C ∨
      ∃ t : V, P.path.terminal? = some t ∧
        t ∈ (RelevantInput L hL).terminalCut}

/-- Blocking points of the descent-relevant fragments. -/
def splitGroundedRelevantBL
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) : Set V :=
  GroundingCut.blockingPoint (RelevantInput L hL) C ''
    L.splitGroundedRelevantG0 hL C

/-- The smaller ambient boundary used by the exact split 8.18 descent. -/
def splitGroundedRelevantBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) : Set V :=
  GroundingCut.CV (RelevantInput L hL) C ∪
    L.splitGroundedRelevantBL hL C

theorem splitGroundedRelevantG0_subset_reducedG0
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) :
    L.splitGroundedRelevantG0 hL C ⊆ L.splitGroundedG0 hL C :=
  fun _ hP => hP.1

theorem splitGroundedRelevantG0_subset_legacyG0
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) :
    L.splitGroundedRelevantG0 hL C ⊆
      GroundingCut.G0 (RelevantInput L hL) C :=
  (L.splitGroundedRelevantG0_subset_reducedG0 hL C).trans
    (L.splitGroundedG0_subset_legacyG0 hL C)

theorem splitGroundedRelevantBL_subset_reducedBL
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) :
    L.splitGroundedRelevantBL hL C ⊆ L.splitGroundedBL hL C := by
  rintro b ⟨P, hP, rfl⟩
  exact ⟨P, hP.1, rfl⟩

theorem splitGroundedRelevantBB_subset_reducedBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) :
    L.splitGroundedRelevantBB hL C ⊆ L.splitGroundedBB hL C := by
  rintro b (hb | hb)
  · exact L.splitGroundedCV_subset_BB hL C hb
  · exact L.splitGroundedBL_subset_BB hL C
      (L.splitGroundedRelevantBL_subset_reducedBL hL C hb)

theorem splitGroundedRelevantBB_subset_legacyBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) :
    L.splitGroundedRelevantBB hL C ⊆
      GroundingCut.BB (RelevantInput L hL) C :=
  (L.splitGroundedRelevantBB_subset_reducedBB hL C).trans
    (L.splitGroundedBB_subset_legacyBB hL C)

theorem splitGroundedCV_subset_relevantBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) :
    GroundingCut.CV (RelevantInput L hL) C ⊆
      L.splitGroundedRelevantBB hL C :=
  Set.subset_union_left

theorem splitGroundedRelevantBL_subset_BB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL)) :
    L.splitGroundedRelevantBL hL C ⊆
      L.splitGroundedRelevantBB hL C :=
  Set.subset_union_right

theorem splitGrounded_fragment_meeting_escape_mem_relevantG0
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL))
    (hC : Popular.IsSeparator (RelevantInput L hL).lambda C)
    (P : (RelevantInput L hL).Fragment)
    (hfragment : P ∈ GroundingCut.fragments (RelevantInput L hL) C)
    (hescape : P.MeetsEscape (RelevantInput L hL) C) :
    P ∈ L.splitGroundedRelevantG0 hL C := by
  exact ⟨L.splitGrounded_fragment_meeting_escape_mem_G0
    hL C hC P hfragment hescape, Or.inl hescape⟩

theorem splitGrounded_mem_relevantG0_of_mem_reduced_of_terminalCut
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL))
    (P : (RelevantInput L hL).Fragment)
    (hP : P ∈ L.splitGroundedG0 hL C)
    {t : V} (hterminal : P.path.terminal? = some t)
    (ht : t ∈ (RelevantInput L hL).terminalCut) :
    P ∈ L.splitGroundedRelevantG0 hL C :=
  ⟨hP, Or.inr ⟨t, hterminal, ht⟩⟩

/-- An escape-free relevant fragment is retained only by the essential
terminal clause.  In particular its blocking point is that terminal. -/
theorem splitGroundedRelevantG0_terminalCut_of_not_meetsEscape
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL))
    (P : (RelevantInput L hL).Fragment)
    (hP : P ∈ L.splitGroundedRelevantG0 hL C)
    (hnoEscape : ¬ P.MeetsEscape (RelevantInput L hL) C) :
    ∃ t : V, P.path.terminal? = some t ∧
      t ∈ (RelevantInput L hL).terminalCut ∧
      GroundingCut.blockingPoint (RelevantInput L hL) C P = t := by
  rcases hP.2 with hescape | ⟨t, hterminal, ht⟩
  · exact (hnoEscape hescape).elim
  · exact ⟨t, hterminal, ht,
      GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
        (RelevantInput L hL) C P hnoEscape hterminal⟩

/-- Consequently, every escape-free member of the relevant family belongs
to a component of the essential limiting warp. -/
theorem splitGroundedRelevantG0_parent_mem_essentialLadder_of_not_meetsEscape
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (RelevantLV L hL))
    (P : (RelevantInput L hL).Fragment)
    (hP : P ∈ L.splitGroundedRelevantG0 hL C)
    (hnoEscape : ¬ P.MeetsEscape (RelevantInput L hL) C) :
    P.parent ∈ (RelevantInput L hL).essentialLadder := by
  obtain ⟨t, hterminal, htCut, _hblocking⟩ :=
    L.splitGroundedRelevantG0_terminalCut_of_not_meetsEscape
      hL C P hP hnoEscape
  obtain ⟨q, hqEssential, hqTerminal⟩ := htCut
  have htPPath : t ∈ P.path.support :=
    P.path.terminal_mem_support t hterminal
  have htParent : t ∈ P.parent.support := P.support_subset htPPath
  have htQ : t ∈ q.support := Gamma.terminal_mem_support hqTerminal
  have hparentEq : P.parent = q :=
    _root_.Erdos599.Alternating.DWeb.IsWarp.eq_of_mem_support
      (RelevantInput L hL).ladder.disjoint P.parent_mem hqEssential.1
        htParent htQ
  exact hparentEq.symm ▸ hqEssential

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.splitGroundedRelevantBB_subset_reducedBB
#print axioms Erdos599.DWeb.KappaLadder.splitGrounded_fragment_meeting_escape_mem_relevantG0
#print axioms Erdos599.DWeb.KappaLadder.splitGroundedRelevantG0_parent_mem_essentialLadder_of_not_meetsEscape
