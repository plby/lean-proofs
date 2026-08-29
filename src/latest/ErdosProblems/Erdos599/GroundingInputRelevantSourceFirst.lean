/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingInputRelevantDecoder
import ErdosProblems.Erdos599.GroundingLastContact

/-!
# A source-first frontier for input-level relevant pruning

The relevant boundary supplied by `GroundingInputRelevantPruning.Data` can
contain several points on one ambient source--target path.  This file keeps
only points which are displayed as the first relevant-boundary contact of a
roofed finite source prefix.  The finite descent decoder proves that this
smaller set is still a separator.

The construction is entirely input-generic.  In particular it can be used
with the final deferred selector and its simultaneously pruned reserved and
selected starting records.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingInputRelevantSourceFirst

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) :=
  PopularAuxiliary.Input Gamma I

variable {J : Input Gamma I} {C : Set J.LV}

abbrev Data (J : Input Gamma I) (C : Set J.LV) :=
  GroundingInputRelevantPruning.Data J C

/-- Points displayed as the first relevant-boundary contact on a roofed
finite path starting in the ambient source. -/
def sourceFirstBB (D : Data J C) : Set V :=
  {b | ∃ R : FinitePath Gamma.graph,
    R.start ∈ Gamma.source ∧
    R.finish = b ∧
    R.support ⊆ J.roofRegion ∧
    b ∈ D.relevantBB ∧
    ∀ x ∈ R.walk.support.dropLast, x ∉ D.relevantBB}

theorem sourceFirstBB_subset_relevantBB (D : Data J C) :
    sourceFirstBB D ⊆ D.relevantBB := by
  rintro b ⟨R, hsource, hfinish, hroof, hb, hfirst⟩
  exact hb

/-- Every finite ambient source--essential-terminal path meets the relevant
boundary whenever the input-level finite descent decoder is available. -/
theorem relevantBB_meets_source_terminalCut_path
    (D : Data J C)
    (hdecoder : GroundingInputRelevantDecoder.RelevantFiniteDescentDecoder D)
    (hC : Popular.IsSeparator J.lambda C)
    (R : FinitePath Gamma.graph)
    (hsource : R.start ∈ Gamma.source)
    (hterminal : R.finish ∈ J.terminalCut) :
    R.walk.Meets D.relevantBB := by
  by_contra hnotMeet
  have havoid : Gamma.Avoids R D.relevantBB :=
    (Gamma.avoids_iff_not_meets R D.relevantBB).2 hnotMeet
  obtain ⟨q, hqSource, hqTarget, hqAvoid⟩ :=
    hdecoder R hsource hterminal havoid
  exact PopularAuxiliary.Input.no_avoiding_source_target_path
    J.lambda C hC q hqSource hqTarget hqAvoid

/-- The source-first relevant frontier is an ambient separator. -/
theorem sourceFirstBB_isSeparator
    (D : Data J C)
    (hdecoder : GroundingInputRelevantDecoder.RelevantFiniteDescentDecoder D)
    (hterminalSep : Popular.IsSeparator Gamma J.terminalCut)
    (hC : Popular.IsSeparator J.lambda C) :
    Popular.IsSeparator Gamma (sourceFirstBB D) := by
  intro p hpSource hpTarget
  obtain ⟨z, hzp, hzTerminal⟩ := hterminalSep p hpSource hpTarget
  have hmeetTerminal : p.walk.Meets J.terminalCut := ⟨z, hzp, hzTerminal⟩
  let Q : FinitePath Gamma.graph := p.firstHit J.terminalCut hmeetTerminal
  have hQsource : Q.start ∈ Gamma.source := hpSource
  have hQterminal : Q.finish ∈ J.terminalCut :=
    p.firstHit_finish_mem J.terminalCut hmeetTerminal
  have hQroof : Q.support ⊆ J.roofRegion :=
    GroundingLastContact.support_subset_roofRegion_of_no_terminal_before
      J Q hterminalSep hQsource hQterminal
        (fun {_} hx ↦ p.firstHit_no_mem_before J.terminalCut hmeetTerminal hx)
  have hQmeet := relevantBB_meets_source_terminalCut_path
    D hdecoder hC Q hQsource hQterminal
  let R : FinitePath Gamma.graph := Q.firstHit D.relevantBB hQmeet
  have hRboundary : R.finish ∈ D.relevantBB :=
    Q.firstHit_finish_mem D.relevantBB hQmeet
  have hRfirst : ∀ x ∈ R.walk.support.dropLast, x ∉ D.relevantBB :=
    fun {_} hx ↦ Q.firstHit_no_mem_before D.relevantBB hQmeet hx
  have hRroof : R.support ⊆ J.roofRegion :=
    fun x hx ↦ hQroof (Q.firstHit_support_subset D.relevantBB hQmeet hx)
  have hRsource : R.start ∈ Gamma.source := hQsource
  have hRinP : R.finish ∈ p.support :=
    p.firstHit_support_subset J.terminalCut hmeetTerminal
      (Q.firstHit_support_subset D.relevantBB hQmeet R.finish_mem_support)
  exact ⟨R.finish, hRinP,
    ⟨R, hRsource, rfl, hRroof, hRboundary, hRfirst⟩⟩

end GroundingInputRelevantSourceFirst
end Erdos599

#print axioms
  Erdos599.GroundingInputRelevantSourceFirst.sourceFirstBB_isSeparator
