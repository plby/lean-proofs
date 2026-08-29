/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorGeometry
import ErdosProblems.Erdos599.GroundingAssertion818Decoder

/-!
# Assertion 8.18 for the grounded split auxiliary

This is the representation-independent finite-contact descent from the split
proof, instantiated on exactly the grounded records.  No ordinary-legality
witness and no split-to-legacy coercion is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev GroundedAux (L : Gamma.KappaLadder kappa)
    (hL : L.IsSplitLegal) :=
  L.splitGroundedPopularAuxiliaryInput hL

private abbrev GroundedLV (L : Gamma.KappaLadder kappa)
    (_hL : L.IsSplitLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords


private theorem firstHit_avoids
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (GroundedLV L hL)) (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R (GroundingCut.BB (GroundedAux L hL) C))
    (hmeet : R.walk.Meets (GroundedAux L hL).terminalCut) :
    Gamma.Avoids (R.firstHit (GroundedAux L hL).terminalCut hmeet)
      (GroundingCut.BB (GroundedAux L hL) C) := by
  change Disjoint
    (R.firstHit (GroundedAux L hL).terminalCut hmeet).support
    (GroundingCut.BB (GroundedAux L hL) C)
  rw [Set.disjoint_left]
  intro x hx hcut
  exact Set.disjoint_left.1 havoid
    (R.firstHit_support_subset (GroundedAux L hL).terminalCut hmeet hx) hcut

private theorem support_subset_roofRegion_of_no_terminal_before
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hfinish : R.finish ∈ (GroundedAux L hL).terminalCut)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ (GroundedAux L hL).terminalCut) :
    R.support ⊆ (GroundedAux L hL).roofRegion := by
  have hseparator := splitGroundedPopularAuxiliary_terminalCut_isSeparator L hL
  have hstartRoof : R.start ∈ Gamma.roof (GroundedAux L hL).terminalCut := by
    intro p hp
    exact hseparator p (hp.1 ▸ hsource) hp.2
  have hterminal : ∀ t,
      Gamma.terminal? (.inl R : Gamma.DPath) = some t →
        t ∈ (GroundedAux L hL).terminalCut := by
    intro t ht
    have hrt : R.finish = t := Option.some.inj ht
    simpa only [hrt] using hfinish
  have hinter :
      (DirectedPath.Path.support (.inl R : Gamma.DPath) ∩
          (GroundedAux L hL).terminalCut) ⊆ ({R.finish} : Set V) := by
    intro x hx
    apply Set.mem_singleton_iff.2
    by_contra hxf
    have hxlast : x ≠ R.walk.support.getLast R.walk.support_ne_nil := by
      simpa only [R.walk.getLast_support] using hxf
    exact hfirst (List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxlast) hx.2
  exact Gamma.pathSupportRoof (.inl R : Gamma.DPath)
    (GroundedAux L hL).terminalCut hstartRoof hterminal hinter

private theorem exists_terminal_G0_fragment_meeting_escape
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (GroundedLV L hL)) (R : FinitePath Gamma.graph)
    (hterminal : R.finish ∈ (GroundedAux L hL).terminalCut)
    (havoid : Gamma.Avoids R (GroundingCut.BB (GroundedAux L hL) C)) :
    ∃ P : (GroundedAux L hL).Fragment,
      P ∈ GroundingCut.G0 (GroundedAux L hL) C ∧
        P ∈ GroundingCut.fragments (GroundedAux L hL) C ∧
        P.path.terminal? = some R.finish ∧
        R.finish ∈ P.path.support ∧
        PopularAuxiliary.Input.Fragment.MeetsEscape (GroundedAux L hL) C P := by
  obtain ⟨parent, hpEssential, hpTerminal⟩ := hterminal
  cases parent with
  | inl p =>
      have hpFinish : p.finish = R.finish := Option.some.inj hpTerminal
      have hfinishParent : R.finish ∈ p.support := by
        rw [← hpFinish]
        exact p.finish_mem_support
      obtain ⟨P, hparent, hPfragment, hfinishP⟩ :=
        GroundingFragmentPartition.exists_fragment_containing
          (GroundedAux L hL) C hpEssential.1 hfinishParent
      obtain ⟨hPfinite, hterminalP⟩ :=
        GroundingTerminalFragment.finite_and_terminal_eq_parent_finish
          (GroundedAux L hL) C p P hPfragment hparent
            (by simpa only [hpFinish] using hfinishP)
      have hPterminal : P.path.terminal? = some R.finish := by
        simpa only [hpFinish] using hterminalP
      have hPG0 : P ∈ GroundingCut.G0 (GroundedAux L hL) C :=
        ⟨hPfragment, Or.inr hPfinite⟩
      have hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
          (GroundedAux L hL) C P := by
        by_contra hnoEscape
        have hblock : GroundingCut.blockingPoint
            (GroundedAux L hL) C P = R.finish :=
          GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
            (GroundedAux L hL) C P hnoEscape hPterminal
        have hBL : R.finish ∈ GroundingCut.BL (GroundedAux L hL) C :=
          ⟨P, hPG0, hblock⟩
        exact Set.disjoint_left.1 havoid R.finish_mem_support
          (GroundingCut.BL_subset_BB (GroundedAux L hL) C hBL)
      exact ⟨P, hPG0, hPfragment, hPterminal,
        by simpa only [hpFinish] using hfinishP, hescape⟩
  | inr r =>
      change (none : Option V) = some R.finish at hpTerminal
      cases hpTerminal

private theorem exists_initialEscapeSuffixState
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (GroundedLV L hL)) (R : FinitePath Gamma.graph)
    (hterminal : R.finish ∈ (GroundedAux L hL).terminalCut)
    (havoid : Gamma.Avoids R (GroundingCut.BB (GroundedAux L hL) C)) :
    ∃ S : GroundingFiniteDescent.EscapeSuffixState (GroundedAux L hL) C R,
      ¬ S.position.1 + 1 < R.walk.support.length := by
  obtain ⟨P, hPG0, hPfragment, hPterminal, hfinishP, hPescape⟩ :=
    exists_terminal_G0_fragment_meeting_escape L hL C R hterminal havoid
  have hfinishNotBB :
      R.finish ∉ GroundingCut.BB (GroundedAux L hL) C := by
    intro hfinishBB
    exact Set.disjoint_left.1 havoid R.finish_mem_support hfinishBB
  obtain ⟨q, hqstart, hqtarget, hqavoid⟩ :=
    GroundingEscapeSuffix.exists_avoiding_terminal_escape_of_not_mem_BB
      (GroundedAux L hL) C P ⟨hPfragment, hPG0⟩ hPterminal
        hPescape hfinishNotBB
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
  refine ⟨{
    position := i
    fragment := P
    fragment_mem := hPG0
    fragment_escape := hPescape
    contact_mem := by simpa only [hiFinish] using hfinishP
    suffix := q
    suffix_start := hqstart.trans
      (congrArg PopularAuxiliary.Input.LambdaVertex.old hiFinish.symm)
    suffix_target := hqtarget
    suffix_avoids := hqavoid }, hilast⟩

private structure EarlierLadderContact
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (R : FinitePath Gamma.graph)
    (i : Fin R.walk.support.length) where
  position : Fin R.walk.support.length
  lt_current : position.1 < i.1
  mem_ladder : R.walk.support[position] ∈
    Gamma.vertexSet (GroundedAux L hL).ladder.paths
  open_not_ladder : ∀ m : Fin R.walk.support.length,
    position.1 < m.1 → m.1 < i.1 →
      R.walk.support[m] ∉ Gamma.vertexSet (GroundedAux L hL).ladder.paths

private theorem exists_last_earlier_ladder_contact
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (i : Fin R.walk.support.length) (hi : 0 < i.1) :
    Nonempty (EarlierLadderContact L hL R i) := by
  classical
  have hxInitial : R.start ∈ Gamma.initialSet L.limitWarp :=
    hL.source_subset_initialSet_limitWarp hsource
  obtain ⟨parent, hparent, hinitial⟩ := hxInitial
  have hzero : R.walk.support[0] ∈
      Gamma.vertexSet (GroundedAux L hL).ladder.paths := by
    refine ⟨parent, hparent, ?_⟩
    rw [R.support_getElem_zero, ← hinitial]
    exact parent.initial_mem_support
  let contacts : Finset (Fin R.walk.support.length) :=
    Finset.univ.filter fun j ↦ j.1 < i.1 ∧
      R.walk.support[j] ∈ Gamma.vertexSet (GroundedAux L hL).ladder.paths
  have hzeroMem : (⟨0, R.support_length_pos⟩ :
      Fin R.walk.support.length) ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi, hzero⟩
  let j : Fin R.walk.support.length := contacts.max' ⟨_, hzeroMem⟩
  have hjmem : j ∈ contacts := Finset.max'_mem contacts ⟨_, hzeroMem⟩
  have hj : j.1 < i.1 ∧ R.walk.support[j] ∈
      Gamma.vertexSet (GroundedAux L hL).ladder.paths := by
    simpa only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
      using hjmem
  refine ⟨{
    position := j
    lt_current := hj.1
    mem_ladder := hj.2
    open_not_ladder := ?_ }⟩
  intro m hjm hmi hmLadder
  have hmmem : m ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hmi, hmLadder⟩
  exact (not_le_of_gt hjm) (Finset.le_max' contacts m hmmem)

private theorem EarlierLadderContact.open_offLadder
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitLegal}
    {R : FinitePath Gamma.graph} {i : Fin R.walk.support.length}
    (J : EarlierLadderContact L hL R i)
    (hroof : R.support ⊆ (GroundedAux L hL).roofRegion) :
    ∀ m : Fin R.walk.support.length,
      J.position.1 < m.1 → m.1 < i.1 →
        R.walk.support[m] ∈ (GroundedAux L hL).offLadder := by
  intro m hjm hmi
  exact ⟨hroof (List.getElem_mem m.2), J.open_not_ladder m hjm hmi⟩

private theorem grounded_path_edge_head_ne_initial
    {p : Gamma.DPath} {u v : V} (he : (u, v) ∈ p.edgeSet) :
    v ≠ p.initial := by
  rcases p with p | r
  · exact
      _root_.Erdos599.Alternating.FinitePath.target_ne_start_of_mem_edgeSet
        p he
  · rintro rfl
    rcases he with ⟨n, hn⟩
    have hzero : n + 1 = 0 := by
      apply r.injective
      exact (congrArg Prod.snd hn).symm
    omega

private theorem fragment_initial_eq_parent_initial_of_mem
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    {P : (GroundedAux L hL).Fragment}
    (hinit : P.parent.initial ∈ P.path.support) :
    P.path.initial = P.parent.initial := by
  by_contra hne
  have hne' : P.parent.initial ≠ P.path.initial := fun h ↦ hne h.symm
  cases hpath : P.path with
  | inl p =>
      have hinit' : P.parent.initial ∈ p.support := by
        simpa only [hpath, DirectedPath.Path.support] using hinit
      have hne'' : P.parent.initial ≠ p.start := by
        simpa only [hpath, DirectedPath.Path.initial] using hne'
      obtain ⟨y, hy⟩ :=
        _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          p hinit' hne''
      exact grounded_path_edge_head_ne_initial (P.edges_subset (by
        simpa only [hpath, DirectedPath.Path.edgeSet] using hy)) rfl
  | inr r =>
      have hinit' : P.parent.initial ∈ r.support := by
        simpa only [hpath, DirectedPath.Path.support] using hinit
      have hne'' : P.parent.initial ≠ r.initial := by
        simpa only [hpath, DirectedPath.Path.initial] using hne'
      obtain ⟨y, hy⟩ :=
        _root_.Erdos599.Alternating.Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial
          r hinit' hne''
      exact grounded_path_edge_head_ne_initial (P.edges_subset (by
        simpa only [hpath, DirectedPath.Path.edgeSet] using hy)) rfl

private theorem escapeSuffixState_position_ne_zero
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (GroundedLV L hL)) (hC : Popular.IsSeparator
      (GroundedAux L hL).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (havoid : Gamma.Avoids R (GroundingCut.BB (GroundedAux L hL) C))
    (S : GroundingFiniteDescent.EscapeSuffixState (GroundedAux L hL) C R) :
    S.position.1 ≠ 0 := by
  intro hpos
  have hposFin : S.position =
      (⟨0, R.support_length_pos⟩ : Fin R.walk.support.length) := Fin.ext hpos
  have hxStart : R.walk.support[S.position] = R.start :=
    (congrArg (fun i : Fin R.walk.support.length ↦
      R.walk.support[i]) hposFin).trans R.support_getElem_zero
  obtain ⟨parent, hparent, hinitial⟩ :=
    hL.source_subset_initialSet_limitWarp hsource
  have hxParent : R.walk.support[S.position] ∈ parent.support := by
    rw [hxStart, ← hinitial]
    exact parent.initial_mem_support
  obtain ⟨Q, hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      (GroundedAux L hL) C hparent hxParent
  have hxInitial : Q.path.initial = R.walk.support[S.position] := by
    have hparentInitQ : Q.parent.initial ∈ Q.path.support := by
      simpa only [hQparent, hinitial, hxStart] using hxQ
    calc
      Q.path.initial = Q.parent.initial :=
        fragment_initial_eq_parent_initial_of_mem L hL hparentInitQ
      _ = parent.initial := congrArg DirectedPath.Path.initial hQparent
      _ = R.walk.support[S.position] := by rw [hinitial, hxStart]
  let E : GroundingRelaxedEscape.RelaxedEscape
      (GroundedAux L hL) C R.walk.support[S.position] :=
    { route := S.suffix
      start_eq := Or.inl S.suffix_start
      target := S.suffix_target
      avoids := S.suffix_avoids
      old_not_mem := GroundingRelaxedCorridor.old_not_mem_cut_of_ambient_avoids
        (GroundedAux L hL) C R havoid S.position }
  have hQescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      (GroundedAux L hL) C Q := ⟨R.walk.support[S.position], hxQ, ⟨E⟩⟩
  have hQG0 : Q ∈ GroundingCut.G0 (GroundedAux L hL) C :=
    GroundingCut.fragment_meeting_escape_mem_G0
      (GroundedAux L hL) C Q hQfragment hQescape
  have hblockBefore : GroundingCut.BeforeEq Q.path
      (GroundingCut.blockingPoint (GroundedAux L hL) C Q)
      R.walk.support[S.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      (GroundedAux L hL) C Q hQescape hxQ ⟨E⟩
  have hinitialBefore : GroundingCut.BeforeEq Q.path
      R.walk.support[S.position]
      (GroundingCut.blockingPoint (GroundedAux L hL) C Q) := by
    rw [← hxInitial]
    exact GroundingFragmentWarp.initial_beforeEq_of_mem
      (GroundingCut.blockingPoint_mem_support
        (GroundedAux L hL) C Q hQG0.2)
  have hblockEq : GroundingCut.blockingPoint (GroundedAux L hL) C Q =
      R.walk.support[S.position] :=
    GroundingCutDecoder.beforeEq_antisymm hblockBefore hinitialBefore
  have hxBB : R.walk.support[S.position] ∈
      GroundingCut.BB (GroundedAux L hL) C :=
    GroundingCut.BL_subset_BB (GroundedAux L hL) C ⟨Q, hQG0, hblockEq⟩
  exact Set.disjoint_left.1 havoid
    (List.getElem_mem S.position.2) hxBB

private theorem exists_strictlyEarlier_escapeSuffixState
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (GroundedLV L hL))
    (hC : Popular.IsSeparator (GroundedAux L hL).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hroof : R.support ⊆ (GroundedAux L hL).roofRegion)
    (havoid : Gamma.Avoids R (GroundingCut.BB (GroundedAux L hL) C))
    (S : GroundingFiniteDescent.EscapeSuffixState (GroundedAux L hL) C R) :
    ∃ T : GroundingFiniteDescent.EscapeSuffixState (GroundedAux L hL) C R,
      T.position.1 < S.position.1 := by
  have hi : 0 < S.position.1 := Nat.pos_of_ne_zero
    (escapeSuffixState_position_ne_zero L hL C hC R hsource havoid S)
  obtain ⟨J⟩ := exists_last_earlier_ladder_contact
    L hL R hsource S.position hi
  obtain ⟨E⟩ :=
    GroundingRelaxedCorridor.relaxedEscape_of_offLadder_interval
      (GroundedAux L hL) C hC R havoid J.position S.position
        J.lt_current (J.open_offLadder hroof)
        (Or.inr ⟨S.fragment.parent, S.fragment.parent_mem,
          S.fragment.support_subset S.contact_mem⟩)
        S.suffix S.suffix_start S.suffix_target S.suffix_avoids
  obtain ⟨parent, hparent, hxParent⟩ := J.mem_ladder
  obtain ⟨Q, _hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      (GroundedAux L hL) C hparent hxParent
  have hQescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      (GroundedAux L hL) C Q :=
    ⟨R.walk.support[J.position], hxQ, ⟨E⟩⟩
  have hQG0 : Q ∈ GroundingCut.G0 (GroundedAux L hL) C :=
    GroundingCut.fragment_meeting_escape_mem_G0
      (GroundedAux L hL) C Q hQfragment hQescape
  let b := GroundingCut.blockingPoint (GroundedAux L hL) C Q
  have hbQ : b ∈ Q.path.support :=
    GroundingCut.blockingPoint_mem_support (GroundedAux L hL) C Q hQG0.2
  have hbEscape : b ∈ (GroundedAux L hL).escapeRegion C :=
    GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      (GroundedAux L hL) C Q hQescape
  have hbeforeEq : GroundingCut.BeforeEq Q.path b
      R.walk.support[J.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      (GroundedAux L hL) C Q hQescape hxQ ⟨E⟩
  by_cases hbeq : b = R.walk.support[J.position]
  · have hxBB : R.walk.support[J.position] ∈
        GroundingCut.BB (GroundedAux L hL) C :=
      GroundingCut.BL_subset_BB (GroundedAux L hL) C ⟨Q, hQG0, hbeq⟩
    exact False.elim (Set.disjoint_left.1 havoid
      (List.getElem_mem J.position.2) hxBB)
  · obtain ⟨Eb⟩ := hbEscape
    exact GroundingRelaxedCorridor.exists_strictlyEarlier_escapeSuffixState
      (GroundedAux L hL) C R havoid S J.position J.lt_current Q hQG0
        hbQ ⟨hbeforeEq, hbeq⟩ Eb

/-- The split auxiliary has the genuine finite descent decoder used in
Assertion 8.18. -/
theorem splitGroundedFiniteDescentDecoder
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (GroundedLV L hL))
    (hC : Popular.IsSeparator (GroundedAux L hL).lambda C) :
    GroundingCut.FiniteDescentDecoder (GroundedAux L hL) C := by
  intro R hsource hterminal havoid
  have hmeet : R.walk.Meets (GroundedAux L hL).terminalCut :=
    ⟨R.finish, R.finish_mem_support, hterminal⟩
  let Q : FinitePath Gamma.graph :=
    R.firstHit (GroundedAux L hL).terminalCut hmeet
  have hQsource : Q.start ∈ Gamma.source := hsource
  have hQterminal : Q.finish ∈ (GroundedAux L hL).terminalCut :=
    R.firstHit_finish_mem (GroundedAux L hL).terminalCut hmeet
  have hQavoid : Gamma.Avoids Q
      (GroundingCut.BB (GroundedAux L hL) C) :=
    firstHit_avoids L hL C R havoid hmeet
  have hQroof : Q.support ⊆ (GroundedAux L hL).roofRegion := by
    apply support_subset_roofRegion_of_no_terminal_before
      L hL Q hQsource hQterminal
    intro x hx
    exact R.firstHit_no_mem_before (GroundedAux L hL).terminalCut hmeet hx
  obtain ⟨seed, _⟩ :=
    exists_initialEscapeSuffixState L hL C Q hQterminal hQavoid
  let D : GroundingFiniteDescent.LastFragmentDescentSystem
      (GroundedAux L hL) C Q :=
    { seed := seed
      resolve := fun S ↦ Or.inr
        (exists_strictlyEarlier_escapeSuffixState
          L hL C hC Q hQsource hQroof hQavoid S) }
  exact D.exists_avoiding_source_target_path

/-- Split Assertion 8.18: the canonical boundary `BB` separates the ambient
source from the ambient target. -/
theorem splitGroundedAssertion8_18
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (GroundedLV L hL))
    (hC : Popular.IsSeparator (GroundedAux L hL).lambda C) :
    Popular.IsSeparator Gamma (GroundingCut.BB (GroundedAux L hL) C) :=
  GroundingCut.assertion8_18 (GroundedAux L hL) C hC
    (splitGroundedPopularAuxiliary_terminalCut_isSeparator L hL)
    (splitGroundedFiniteDescentDecoder L hL C hC)

end DWeb.KappaLadder
end Erdos599

