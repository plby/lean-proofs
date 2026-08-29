/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantSeparator818
import ErdosProblems.Erdos599.GroundingLastContact

/-!
# The source-first descent-relevant frontier

We retain exactly those points of `splitGroundedRelevantBB` which occur as
the first boundary point on a roofed finite path from the ambient source.
The finite descent proving Assertion 8.18 shows that this smaller family is
still an ambient separator.  Its membership certificate is the exact input
needed by endpoint-open escape normalization.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev SourceFirstInput (L : Gamma.KappaLadder kappa)
    (hL : L.IsSplitLegal) :=
  L.splitGroundedPopularAuxiliaryInput hL

private abbrev SourceFirstLV (L : Gamma.KappaLadder kappa)
    (_hL : L.IsSplitLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-- Boundary points carrying a roofed ambient source prefix with no earlier
descent-relevant boundary point. -/
def splitGroundedRelevantSourceFirstBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (SourceFirstLV L hL)) : Set V :=
  {b | ∃ R : FinitePath Gamma.graph,
    R.start ∈ Gamma.source ∧
    R.finish = b ∧
    R.support ⊆ (SourceFirstInput L hL).roofRegion ∧
    b ∈ L.splitGroundedRelevantBB hL C ∧
    ∀ x ∈ R.walk.support.dropLast,
      x ∉ L.splitGroundedRelevantBB hL C}

theorem splitGroundedRelevantSourceFirstBB_subset
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (SourceFirstLV L hL)) :
    L.splitGroundedRelevantSourceFirstBB hL C ⊆
      L.splitGroundedRelevantBB hL C := by
  rintro b ⟨R, hsource, hfinish, hroof, hb, hfirst⟩
  exact hb

/-- Every finite ambient source--essential-terminal path meets the relevant
boundary.  This is the pathwise content of the filtered decoder. -/
theorem splitGroundedRelevant_meets_source_terminalCut_path
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (SourceFirstLV L hL))
    (hC : Popular.IsSeparator (SourceFirstInput L hL).lambda C)
    (R : FinitePath Gamma.graph)
    (hsource : R.start ∈ Gamma.source)
    (hterminal : R.finish ∈ (SourceFirstInput L hL).terminalCut) :
    R.walk.Meets (L.splitGroundedRelevantBB hL C) := by
  by_contra hnotMeet
  have havoid : Gamma.Avoids R (L.splitGroundedRelevantBB hL C) :=
    (Gamma.avoids_iff_not_meets R
      (L.splitGroundedRelevantBB hL C)).2 hnotMeet
  obtain ⟨q, hqSource, hqTarget, hqAvoid⟩ :=
    L.splitGroundedRelevantFiniteDescentDecoder hL C hC
      R hsource hterminal havoid
  exact PopularAuxiliary.Input.no_avoiding_source_target_path
    (SourceFirstInput L hL).lambda C hC q
      hqSource hqTarget hqAvoid

/-- The source-first relevant frontier still separates the ambient source
from the ambient target. -/
theorem splitGroundedRelevantSourceFirstBB_isSeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (SourceFirstLV L hL))
    (hC : Popular.IsSeparator (SourceFirstInput L hL).lambda C) :
    Popular.IsSeparator Gamma
      (L.splitGroundedRelevantSourceFirstBB hL C) := by
  intro p hpSource hpTarget
  have hterminalSep :=
    splitGroundedPopularAuxiliary_terminalCut_isSeparator L hL
  obtain ⟨z, hzp, hzTerminal⟩ := hterminalSep p hpSource hpTarget
  have hmeetTerminal : p.walk.Meets (SourceFirstInput L hL).terminalCut :=
    ⟨z, hzp, hzTerminal⟩
  let Q : FinitePath Gamma.graph :=
    p.firstHit (SourceFirstInput L hL).terminalCut hmeetTerminal
  have hQsource : Q.start ∈ Gamma.source := hpSource
  have hQterminal : Q.finish ∈ (SourceFirstInput L hL).terminalCut :=
    p.firstHit_finish_mem (SourceFirstInput L hL).terminalCut hmeetTerminal
  have hQroof : Q.support ⊆ (SourceFirstInput L hL).roofRegion :=
    GroundingLastContact.support_subset_roofRegion_of_no_terminal_before
      (SourceFirstInput L hL) Q hterminalSep hQsource hQterminal
        (fun {_} hx ↦
          p.firstHit_no_mem_before
            (SourceFirstInput L hL).terminalCut hmeetTerminal hx)
  have hQmeet := L.splitGroundedRelevant_meets_source_terminalCut_path
    hL C hC Q hQsource hQterminal
  let R : FinitePath Gamma.graph :=
    Q.firstHit (L.splitGroundedRelevantBB hL C) hQmeet
  have hRboundary : R.finish ∈ L.splitGroundedRelevantBB hL C :=
    Q.firstHit_finish_mem (L.splitGroundedRelevantBB hL C) hQmeet
  have hRfirst : ∀ x ∈ R.walk.support.dropLast,
      x ∉ L.splitGroundedRelevantBB hL C :=
    fun {_} hx ↦ Q.firstHit_no_mem_before
      (L.splitGroundedRelevantBB hL C) hQmeet hx
  have hRroof : R.support ⊆ (SourceFirstInput L hL).roofRegion :=
    fun x hx ↦ hQroof
      (Q.firstHit_support_subset (L.splitGroundedRelevantBB hL C) hQmeet hx)
  have hRsource : R.start ∈ Gamma.source := hQsource
  have hRinP : R.finish ∈ p.support :=
    p.firstHit_support_subset (SourceFirstInput L hL).terminalCut
      hmeetTerminal
        (Q.firstHit_support_subset (L.splitGroundedRelevantBB hL C)
          hQmeet R.finish_mem_support)
  exact ⟨R.finish, hRinP,
    ⟨R, hRsource, rfl, hRroof, hRboundary, hRfirst⟩⟩

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.splitGroundedRelevantSourceFirstBB_isSeparator
