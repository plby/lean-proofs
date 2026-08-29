/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.GroundingRelaxedEscape

/-!
# Input-level relevant-fragment pruning

The source's `H_empty` deletion is independent of ladder bookkeeping once
the records which may be discarded are supplied explicitly.  A discardable
record is required to be inessential in the input ladder, and a surviving
whole fragment on it must not meet the relaxed escape region.  These are the
two exact facts used by Assertion 8.18.

The relevant family retains an escaping fragment or a finite fragment ending
at the essential terminal cut.  No split or deferred record type appears in
these definitions.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingInputRelevantPruning

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) :=
  PopularAuxiliary.Input Gamma I

variable {J : Input Gamma I} {C : Set J.LV}

/-- Exact input-level hypotheses for deleting whole unused source records. -/
structure Data (J : Input Gamma I) (C : Set J.LV) where
  discarded : Set Gamma.DPath
  discarded_not_essential : ∀ {p : Gamma.DPath},
    p ∈ discarded → p ∉ J.essentialLadder
  whole_discarded_not_meetsEscape :
    ∀ (P : J.Fragment),
      P ∈ GroundingCut.fragments J C →
      P.path = P.parent → P.parent ∈ discarded →
        ¬ P.MeetsEscape J C

namespace Data

/-- Whole unused source-record fragments removed before blocking points are
chosen. -/
def hEmpty (D : Data J C) : Set J.Fragment :=
  {P | P ∈ GroundingCut.fragments J C ∧
    P.path = P.parent ∧ P.parent ∈ D.discarded}

/-- Surviving fragments after the input-level `H_empty` deletion. -/
def gPrime (D : Data J C) : Set J.Fragment :=
  GroundingCut.fragments J C \ D.hEmpty

/-- Blockable surviving fragments. -/
def g0 (D : Data J C) : Set J.Fragment :=
  D.gPrime ∩ {P | GroundingCut.IsBlockable J C P}

/-- Descent-relevant fragments: genuine escapes or finite fragments ending
at the essential terminal cut. -/
def relevantG0 (D : Data J C) : Set J.Fragment :=
  D.g0 ∩ {P | P.MeetsEscape J C ∨
    ∃ t : V, P.path.terminal? = some t ∧ t ∈ J.terminalCut}

def relevantBL (D : Data J C) : Set V :=
  GroundingCut.blockingPoint J C '' D.relevantG0

/-- The input-level relevant boundary. -/
def relevantBB (D : Data J C) : Set V :=
  GroundingCut.CV J C ∪ D.relevantBL

theorem g0_subset_legacyG0 (D : Data J C) :
    D.g0 ⊆ GroundingCut.G0 J C := by
  rintro P ⟨⟨hfragment, _hnotEmpty⟩, hblockable⟩
  exact ⟨hfragment, hblockable⟩

theorem relevantG0_subset_g0 (D : Data J C) :
    D.relevantG0 ⊆ D.g0 := fun _ hP ↦ hP.1

theorem relevantG0_subset_legacyG0 (D : Data J C) :
    D.relevantG0 ⊆ GroundingCut.G0 J C :=
  D.relevantG0_subset_g0.trans D.g0_subset_legacyG0

theorem relevantBL_subset_legacyBL (D : Data J C) :
    D.relevantBL ⊆ GroundingCut.BL J C := by
  rintro b ⟨P, hP, rfl⟩
  exact ⟨P, D.relevantG0_subset_legacyG0 hP, rfl⟩

theorem relevantBB_subset_legacyBB (D : Data J C) :
    D.relevantBB ⊆ GroundingCut.BB J C := by
  rintro b (hb | hb)
  · exact GroundingCut.CV_subset_BB J C hb
  · exact GroundingCut.BL_subset_BB J C
      (D.relevantBL_subset_legacyBL hb)

theorem CV_subset_relevantBB (D : Data J C) :
    GroundingCut.CV J C ⊆ D.relevantBB := Set.subset_union_left

theorem relevantBL_subset_relevantBB (D : Data J C) :
    D.relevantBL ⊆ D.relevantBB := Set.subset_union_right

/-- Every escaping surviving fragment is retained after `H_empty` and is
therefore in the blockable domain. -/
theorem fragment_meeting_escape_mem_g0
    (D : Data J C) (P : J.Fragment)
    (hfragment : P ∈ GroundingCut.fragments J C)
    (hescape : P.MeetsEscape J C) :
    P ∈ D.g0 := by
  refine ⟨⟨hfragment, ?_⟩, Or.inl hescape⟩
  rintro ⟨hfragment', hwhole, hdiscarded⟩
  exact D.whole_discarded_not_meetsEscape
    P hfragment' hwhole hdiscarded hescape

theorem fragment_meeting_escape_mem_relevantG0
    (D : Data J C) (P : J.Fragment)
    (hfragment : P ∈ GroundingCut.fragments J C)
    (hescape : P.MeetsEscape J C) :
    P ∈ D.relevantG0 :=
  ⟨D.fragment_meeting_escape_mem_g0 P hfragment hescape, Or.inl hescape⟩

/-- An essential ladder component is not among the discarded inessential
records. -/
theorem essential_not_discarded
    (D : Data J C) {p : Gamma.DPath}
    (hp : p ∈ J.essentialLadder) : p ∉ D.discarded := by
  intro hdiscarded
  exact D.discarded_not_essential hdiscarded hp

/-- A blockable terminal fragment of an essential parent belongs to the
relevant family. -/
theorem terminal_fragment_mem_relevantG0
    (D : Data J C) (P : J.Fragment)
    (hfragment : P ∈ GroundingCut.fragments J C)
    (hparent : P.parent ∈ J.essentialLadder)
    (hblockable : GroundingCut.IsBlockable J C P)
    {t : V} (hterminal : P.path.terminal? = some t)
    (ht : t ∈ J.terminalCut) :
    P ∈ D.relevantG0 := by
  have hnotEmpty : P ∉ D.hEmpty := by
    rintro ⟨_hfragment, _hwhole, hdiscarded⟩
    exact D.essential_not_discarded hparent hdiscarded
  exact ⟨⟨⟨hfragment, hnotEmpty⟩, hblockable⟩,
    Or.inr ⟨t, hterminal, ht⟩⟩

end Data

end GroundingInputRelevantPruning
end Erdos599

#print axioms
  Erdos599.GroundingInputRelevantPruning.Data.fragment_meeting_escape_mem_relevantG0
#print axioms
  Erdos599.GroundingInputRelevantPruning.Data.terminal_fragment_mem_relevantG0
