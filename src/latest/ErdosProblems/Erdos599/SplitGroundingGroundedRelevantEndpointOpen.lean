/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantSeparator818

/-!
# Endpoint-open descent at the relevant grounded boundary

Let an ambient finite path start in the original source and meet the
source-correct relevant boundary for the first time at its final vertex.
If that vertex is the blocking point of an escaping fragment, the escape
witness need not start at the ordinary vertex representing the blocker:
`RelaxedEscape` deliberately permits one virtual forward step out of an
unrepresented ladder vertex.

This file isolates the exact sound dichotomy.  An escape whose route starts
at the ordinary old vertex can be pushed through the finite last-contact
descent.  Unless the endpoint is itself an original source, this produces a
strictly earlier relevant-boundary point, contradicting first-hit.  The only
remaining case is the genuine virtual-forward occurrence, which is retained
with its actual route and edge certificate for the selected-route analysis.

No claim is made that the virtual branch is impossible from separator
geometry alone: two consecutive original forward edges cannot in general be
represented by the Section 8 auxiliary after the intervening ladder vertex
has been omitted.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

abbrev SplitGroundedRelevantEndpointInput (L : Gamma.KappaLadder kappa)
    (hL : L.IsSplitLegal) :=
  L.splitGroundedPopularAuxiliaryInput hL

abbrev SplitGroundedRelevantEndpointLV (L : Gamma.KappaLadder kappa)
    (_hL : L.IsSplitLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

private abbrev EndpointInput (L : Gamma.KappaLadder kappa)
    (hL : L.IsSplitLegal) :=
  SplitGroundedRelevantEndpointInput L hL

private abbrev EndpointLV (L : Gamma.KappaLadder kappa)
    (hL : L.IsSplitLegal) :=
  SplitGroundedRelevantEndpointLV L hL

/-- The irreducible endpoint-open branch: the actual escaping route begins
after one virtual original forward step out of the blocking point. -/
structure SplitGroundedRelevantVirtualEscape
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (SplitGroundedRelevantEndpointLV L hL)) (b : V) where
  escape : GroundingRelaxedEscape.RelaxedEscape
    (SplitGroundedRelevantEndpointInput L hL) C b
  virtual : (SplitGroundedRelevantEndpointInput L hL).RelaxedForwardStep
    b escape.route.start

private theorem getElem_mem_dropLast_of_lt
    (R : FinitePath Gamma.graph)
    (i j : Fin R.walk.support.length) (hij : i.1 < j.1) :
    R.walk.support[i] ∈ R.walk.support.dropLast := by
  have hi : i.1 < R.walk.support.dropLast.length := by
    rw [List.length_dropLast]
    omega
  change R.walk.support[i.1] ∈ R.walk.support.dropLast
  rw [← List.getElem_dropLast hi]
  exact List.getElem_mem hi

private theorem endpointOpen_old_not_mem_cut_before
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (EndpointLV L hL))
    (R : FinitePath Gamma.graph)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ L.splitGroundedRelevantBB hL C)
    (i : Fin R.walk.support.length) :
    ∀ m : Fin R.walk.support.length, m.1 < i.1 →
      (PopularAuxiliary.Input.LambdaVertex.old R.walk.support[m] :
        EndpointLV L hL) ∉ C := by
  intro m hmi hmC
  have hmBB : R.walk.support[m] ∈
      L.splitGroundedRelevantBB hL C :=
    L.splitGroundedCV_subset_relevantBB hL C (by
      simpa only [GroundingCut.mem_CV])
  exact hfirst (getElem_mem_dropLast_of_lt R m i hmi) hmBB

private theorem endpointOpen_state_position_ne_zero
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (EndpointLV L hL))
    (hC : Popular.IsSeparator (EndpointInput L hL).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hfinish : R.finish ∉ Gamma.source)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ L.splitGroundedRelevantBB hL C)
    (S : GroundingFiniteDescent.EscapeSuffixState
      (EndpointInput L hL) C R) :
    S.position.1 ≠ 0 := by
  intro hpos
  have hposFin : S.position =
      (⟨0, R.support_length_pos⟩ : Fin R.walk.support.length) := Fin.ext hpos
  have hxStart : R.walk.support[S.position] = R.start :=
    (congrArg (fun i : Fin R.walk.support.length ↦ R.walk.support[i])
      hposFin).trans R.support_getElem_zero
  have hstartNeFinish : R.start ≠ R.finish := by
    intro hEq
    exact hfinish (hEq ▸ hsource)
  have hstartDrop : R.start ∈ R.walk.support.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast R.start_mem_support (by
      simpa only [R.walk.getLast_support] using hstartNeFinish)
  obtain ⟨parent, hparent, hinitial⟩ :=
    hL.source_subset_initialSet_limitWarp hsource
  have hxParent : R.walk.support[S.position] ∈ parent.support := by
    rw [hxStart, ← hinitial]
    exact parent.initial_mem_support
  obtain ⟨Q, hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      (EndpointInput L hL) C hparent hxParent
  have hxInitial : Q.path.initial = R.walk.support[S.position] := by
    have hparentInitQ : Q.parent.initial ∈ Q.path.support := by
      simpa only [hQparent, hinitial, hxStart] using hxQ
    calc
      Q.path.initial = Q.parent.initial :=
        splitGroundedRelevant_fragment_initial_eq_parent_initial_of_mem
          hparentInitQ
      _ = parent.initial := congrArg DirectedPath.Path.initial hQparent
      _ = R.walk.support[S.position] := by rw [hinitial, hxStart]
  have hxNotC :
      (PopularAuxiliary.Input.LambdaVertex.old
        R.walk.support[S.position] : EndpointLV L hL) ∉ C := by
    intro hxC
    have hxBB : R.walk.support[S.position] ∈
        L.splitGroundedRelevantBB hL C :=
      L.splitGroundedCV_subset_relevantBB hL C (by
        simpa only [GroundingCut.mem_CV])
    exact hfirst (by simpa only [hxStart] using hstartDrop) hxBB
  let E : GroundingRelaxedEscape.RelaxedEscape
      (EndpointInput L hL) C R.walk.support[S.position] :=
    { route := S.suffix
      start_eq := Or.inl S.suffix_start
      target := S.suffix_target
      avoids := S.suffix_avoids
      old_not_mem := hxNotC }
  have hQescape : Q.MeetsEscape (EndpointInput L hL) C :=
    ⟨R.walk.support[S.position], hxQ, ⟨E⟩⟩
  have hQRelevant : Q ∈ L.splitGroundedRelevantG0 hL C :=
    L.splitGrounded_fragment_meeting_escape_mem_relevantG0
      hL C hC Q hQfragment hQescape
  have hblockBefore : GroundingCut.BeforeEq Q.path
      (GroundingCut.blockingPoint (EndpointInput L hL) C Q)
      R.walk.support[S.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      (EndpointInput L hL) C Q hQescape hxQ ⟨E⟩
  have hinitialBefore : GroundingCut.BeforeEq Q.path
      R.walk.support[S.position]
      (GroundingCut.blockingPoint (EndpointInput L hL) C Q) := by
    rw [← hxInitial]
    exact GroundingFragmentWarp.initial_beforeEq_of_mem
      (GroundingCut.blockingPoint_mem_support
        (EndpointInput L hL) C Q hQRelevant.1.2)
  have hblockEq : GroundingCut.blockingPoint
      (EndpointInput L hL) C Q = R.walk.support[S.position] :=
    GroundingCutDecoder.beforeEq_antisymm hblockBefore hinitialBefore
  have hxBB : R.walk.support[S.position] ∈
      L.splitGroundedRelevantBB hL C :=
    L.splitGroundedRelevantBL_subset_BB hL C
      ⟨Q, hQRelevant, hblockEq⟩
  exact hfirst (by simpa only [hxStart] using hstartDrop) hxBB

private theorem endpointOpen_exists_strictlyEarlier_state
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (EndpointLV L hL))
    (hC : Popular.IsSeparator (EndpointInput L hL).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hfinish : R.finish ∉ Gamma.source)
    (hroof : R.support ⊆ (EndpointInput L hL).roofRegion)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ L.splitGroundedRelevantBB hL C)
    (S : GroundingFiniteDescent.EscapeSuffixState
      (EndpointInput L hL) C R) :
    ∃ T : GroundingFiniteDescent.EscapeSuffixState
        (EndpointInput L hL) C R,
      T.position.1 < S.position.1 := by
  have hi : 0 < S.position.1 := Nat.pos_of_ne_zero
    (endpointOpen_state_position_ne_zero
      L hL C hC R hsource hfinish hfirst S)
  obtain ⟨J⟩ := exists_splitGroundedRelevantEarlierLadderContact
    L hL R hsource S.position hi
  obtain ⟨E⟩ := splitGroundedRelevant_relaxedEscape_of_offLadder_interval
    L hL C hC R J.position S.position J.lt_current
      (endpointOpen_old_not_mem_cut_before L hL C R hfirst S.position)
      (J.open_offLadder hroof)
      (Or.inr ⟨S.fragment.parent, S.fragment.parent_mem,
        S.fragment.support_subset S.contact_mem⟩)
      S.suffix S.suffix_start S.suffix_target S.suffix_avoids
  obtain ⟨parent, hparent, hxParent⟩ := J.mem_ladder
  obtain ⟨Q, _hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      (EndpointInput L hL) C hparent hxParent
  have hQescape : Q.MeetsEscape (EndpointInput L hL) C :=
    ⟨R.walk.support[J.position], hxQ, ⟨E⟩⟩
  have hQRelevant : Q ∈ L.splitGroundedRelevantG0 hL C :=
    L.splitGrounded_fragment_meeting_escape_mem_relevantG0
      hL C hC Q hQfragment hQescape
  have hQLegacy : Q ∈ GroundingCut.G0 (EndpointInput L hL) C :=
    L.splitGroundedRelevantG0_subset_legacyG0 hL C hQRelevant
  let b := GroundingCut.blockingPoint (EndpointInput L hL) C Q
  have hbEscape : b ∈ (EndpointInput L hL).escapeRegion C :=
    GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      (EndpointInput L hL) C Q hQescape
  have hbeforeEq : GroundingCut.BeforeEq Q.path b
      R.walk.support[J.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      (EndpointInput L hL) C Q hQescape hxQ ⟨E⟩
  by_cases hbeq : b = R.walk.support[J.position]
  · have hxBB : R.walk.support[J.position] ∈
        L.splitGroundedRelevantBB hL C :=
      L.splitGroundedRelevantBL_subset_BB hL C
        ⟨Q, hQRelevant, hbeq⟩
    exact False.elim
      (hfirst (getElem_mem_dropLast_of_lt R J.position S.position
        J.lt_current) hxBB)
  · obtain ⟨Eb⟩ := hbEscape
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ :=
      GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
        (EndpointInput L hL) C Q hQfragment ⟨hbeforeEq, hbeq⟩
        (endpointOpen_old_not_mem_cut_before
          L hL C R hfirst S.position J.position J.lt_current) Eb
    let T : GroundingFiniteDescent.EscapeSuffixState
        (EndpointInput L hL) C R :=
      { position := J.position
        fragment := Q
        fragment_mem := hQLegacy
        fragment_escape := hQescape
        contact_mem := hxQ
        suffix := q
        suffix_start := hqStart
        suffix_target := hqTarget
        suffix_avoids := hqAvoid }
    exact ⟨T, J.lt_current⟩

private theorem endpointOpen_ordinary_escape_implies_source
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (EndpointLV L hL))
    (hC : Popular.IsSeparator (EndpointInput L hL).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hroof : R.support ⊆ (EndpointInput L hL).roofRegion)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ L.splitGroundedRelevantBB hL C)
    (P : (EndpointInput L hL).Fragment)
    (hP : P ∈ L.splitGroundedRelevantG0 hL C)
    (hblock : GroundingCut.blockingPoint
      (EndpointInput L hL) C P = R.finish)
    (hescape : P.MeetsEscape (EndpointInput L hL) C)
    (E : GroundingRelaxedEscape.RelaxedEscape
      (EndpointInput L hL) C R.finish)
    (hordinary : E.route.start =
      PopularAuxiliary.Input.LambdaVertex.old R.finish) :
    R.finish ∈ Gamma.source := by
  by_contra hfinish
  let n := R.walk.support.length - 1
  have hn : n < R.walk.support.length := by
    have hpos := R.support_length_pos
    dsimp only [n]
    omega
  let i : Fin R.walk.support.length := ⟨n, hn⟩
  have hilast : ¬ n + 1 < R.walk.support.length := by
    dsimp only [n]
    omega
  have hiFinish : R.walk.support[i] = R.finish :=
    Alternating.RelationComponents.getElem_last_support_eq_finish
      R n hn hilast
  have hfinishP : R.finish ∈ P.path.support := by
    rw [← hblock]
    exact GroundingCut.blockingPoint_mem_support
      (EndpointInput L hL) C P hP.1.2
  let seed : GroundingFiniteDescent.EscapeSuffixState
      (EndpointInput L hL) C R :=
    { position := i
      fragment := P
      fragment_mem :=
        L.splitGroundedRelevantG0_subset_legacyG0 hL C hP
      fragment_escape := hescape
      contact_mem := by simpa only [hiFinish] using hfinishP
      suffix := E.route
      suffix_start := hordinary.trans
        (congrArg PopularAuxiliary.Input.LambdaVertex.old hiFinish.symm)
      suffix_target := E.target
      suffix_avoids := E.avoids }
  have impossible : ∀ m : Nat,
      ∀ S : GroundingFiniteDescent.EscapeSuffixState
        (EndpointInput L hL) C R,
      S.position.1 = m → False := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro S hSm
        obtain ⟨T, hTS⟩ := endpointOpen_exists_strictlyEarlier_state
          L hL C hC R hsource hfinish hroof hfirst S
        exact ih T.position.1 (by simpa only [hSm] using hTS) T rfl
  exact False.elim (impossible seed.position.1 seed rfl)

/-- Endpoint-open first-hit classification for an escaping relevant
blocking point.

If its actual relaxed escape starts at the ordinary old occurrence, finite
descent forces the endpoint itself to be an original source.  Otherwise the
result retains the exact virtual-forward route.  This is the strongest
separator-only conclusion: the virtual branch is the concrete input needed
by the subsequent selected-forward/control analysis. -/
theorem splitGroundedRelevant_sourceFirst_escapeBlocker_source_or_virtual
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (SplitGroundedRelevantEndpointLV L hL))
    (hC : Popular.IsSeparator
      (SplitGroundedRelevantEndpointInput L hL).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hroof : R.support ⊆
      (SplitGroundedRelevantEndpointInput L hL).roofRegion)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ L.splitGroundedRelevantBB hL C)
    (P : (SplitGroundedRelevantEndpointInput L hL).Fragment)
    (hP : P ∈ L.splitGroundedRelevantG0 hL C)
    (hblock : GroundingCut.blockingPoint
      (SplitGroundedRelevantEndpointInput L hL) C P = R.finish)
    (hescape : P.MeetsEscape
      (SplitGroundedRelevantEndpointInput L hL) C) :
    R.finish ∈ Gamma.source ∨
      Nonempty (SplitGroundedRelevantVirtualEscape L hL C R.finish) := by
  have hbEscape : R.finish ∈ (EndpointInput L hL).escapeRegion C := by
    rw [← hblock]
    exact GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      (EndpointInput L hL) C P hescape
  obtain ⟨E⟩ := hbEscape
  rcases E.start_eq with hordinary | hvirtual
  · exact Or.inl (endpointOpen_ordinary_escape_implies_source
      L hL C hC R hsource hroof hfirst P hP hblock hescape E hordinary)
  · exact Or.inr ⟨⟨E, hvirtual⟩⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedRelevant_sourceFirst_escapeBlocker_source_or_virtual
