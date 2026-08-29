/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingInputRelevantPruning
import ErdosProblems.Erdos599.GroundingRelaxedCorridor
import ErdosProblems.Erdos599.GroundingTerminalFragment
import ErdosProblems.Erdos599.GroundingFragmentPartition
import ErdosProblems.Erdos599.GroundingEscapeSuffix
import ErdosProblems.Erdos599.GroundingFiniteDescent
import ErdosProblems.Erdos599.GroundingFragmentWarp
import ErdosProblems.Erdos599.GroundingPointwiseSwitch
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Input-level finite descent for the relevant pruned boundary

This is Assertion 8.18 with no ladder-bookkeeping type in its statement.
The only ambient geometry supplied by a concrete input is:

* every original source is the initial vertex of an input-ladder member;
* the input's essential terminal cut separates the ambient web.

Fragment deletion and relevance are provided by
`GroundingInputRelevantPruning.Data`.  The proof is the finite last-contact
descent through relaxed corridors.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace GroundingInputRelevantDecoder

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) :=
  PopularAuxiliary.Input Gamma I

variable {J : Input Gamma I} {C : Set J.LV}

abbrev Data (J : Input Gamma I) (C : Set J.LV) :=
  GroundingInputRelevantPruning.Data J C

/-- Source coverage needed by the last-contact choice. -/
def SourceCovered (J : Input Gamma I) : Prop :=
  Gamma.source ⊆ Gamma.initialSet J.ladder.paths

/-- Decoder property for the smaller relevant boundary. -/
def RelevantFiniteDescentDecoder (D : Data J C) : Prop :=
  ∀ R : FinitePath Gamma.graph,
    R.start ∈ Gamma.source → R.finish ∈ J.terminalCut →
    Gamma.Avoids R D.relevantBB →
      ∃ q : FinitePath J.lambda.graph,
        q.start ∈ J.lambda.source ∧ q.finish ∈ J.lambda.target ∧
          J.lambda.Avoids q C

private theorem firstHit_avoids
    (D : Data J C) (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R D.relevantBB)
    (hmeet : R.walk.Meets J.terminalCut) :
    Gamma.Avoids (R.firstHit J.terminalCut hmeet) D.relevantBB := by
  change Disjoint (R.firstHit J.terminalCut hmeet).support D.relevantBB
  rw [Set.disjoint_left]
  intro x hx hcut
  exact Set.disjoint_left.1 havoid
    (R.firstHit_support_subset J.terminalCut hmeet hx) hcut

private theorem old_not_mem_cut_of_avoids
    (D : Data J C) (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R D.relevantBB)
    (i : Fin R.walk.support.length) :
    (PopularAuxiliary.Input.LambdaVertex.old R.walk.support[i] : J.LV) ∉ C := by
  intro hiC
  have hiBB : R.walk.support[i] ∈ D.relevantBB :=
    D.CV_subset_relevantBB (by simpa only [GroundingCut.mem_CV])
  exact Set.disjoint_left.1 havoid (List.getElem_mem i.2) hiBB

private theorem support_subset_roofRegion_of_no_terminal_before
    (hterminalSep : Popular.IsSeparator Gamma J.terminalCut)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hfinish : R.finish ∈ J.terminalCut)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ J.terminalCut) :
    R.support ⊆ J.roofRegion := by
  have hstartRoof : R.start ∈ Gamma.roof J.terminalCut := by
    intro p hp
    exact hterminalSep p (hp.1 ▸ hsource) hp.2
  have hterminal : ∀ t,
      Gamma.terminal? (.inl R : Gamma.DPath) = some t →
        t ∈ J.terminalCut := by
    intro t ht
    have hrt : R.finish = t := Option.some.inj ht
    simpa only [hrt] using hfinish
  have hinter :
      (DirectedPath.Path.support (.inl R : Gamma.DPath) ∩ J.terminalCut) ⊆
        ({R.finish} : Set V) := by
    intro x hx
    apply Set.mem_singleton_iff.2
    by_contra hxf
    have hxlast : x ≠ R.walk.support.getLast R.walk.support_ne_nil := by
      simpa only [R.walk.getLast_support] using hxf
    exact hfirst (List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxlast) hx.2
  exact Gamma.pathSupportRoof (.inl R : Gamma.DPath)
    J.terminalCut hstartRoof hterminal hinter

/-- The essential terminal component supplies the initial escaping state in
the relevant pruned family. -/
private theorem exists_terminal_relevant_fragment_meeting_escape
    (D : Data J C) (R : FinitePath Gamma.graph)
    (hterminal : R.finish ∈ J.terminalCut)
    (havoid : Gamma.Avoids R D.relevantBB) :
    ∃ P : J.Fragment,
      P ∈ D.relevantG0 ∧ P.path.terminal? = some R.finish ∧
      R.finish ∈ P.path.support ∧ P.MeetsEscape J C := by
  have hfinishTerminalCut := hterminal
  obtain ⟨parent, hpEssential, hpTerminal⟩ := hterminal
  cases parent with
  | inr r =>
      change (none : Option V) = some R.finish at hpTerminal
      cases hpTerminal
  | inl p =>
      have hpFinish : p.finish = R.finish := Option.some.inj hpTerminal
      have hfinishParent : R.finish ∈ p.support := by
        rw [← hpFinish]
        exact p.finish_mem_support
      obtain ⟨P, hparent, hPfragment, hfinishP⟩ :=
        GroundingFragmentPartition.exists_fragment_containing
          J C hpEssential.1 hfinishParent
      obtain ⟨hPfinite, hterminalP⟩ :=
        GroundingTerminalFragment.finite_and_terminal_eq_parent_finish
          J C p P hPfragment hparent
            (by simpa only [hpFinish] using hfinishP)
      have hPterminal : P.path.terminal? = some R.finish := by
        simpa only [hpFinish] using hterminalP
      have hparentEssential : P.parent ∈ J.essentialLadder := by
        simpa only [hparent] using hpEssential
      have hPG0 : P ∈ D.relevantG0 :=
        D.terminal_fragment_mem_relevantG0 P hPfragment hparentEssential
          (Or.inr hPfinite) hPterminal hfinishTerminalCut
      have hescape : P.MeetsEscape J C := by
        by_contra hnoEscape
        have hblock : GroundingCut.blockingPoint J C P = R.finish :=
          GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
            J C P hnoEscape hPterminal
        have hBL : R.finish ∈ D.relevantBL := ⟨P, hPG0, hblock⟩
        exact Set.disjoint_left.1 havoid R.finish_mem_support
          (D.relevantBL_subset_relevantBB hBL)
      exact ⟨P, hPG0, hPterminal,
        by simpa only [hpFinish] using hfinishP, hescape⟩

private theorem exists_initialEscapeSuffixState
    (D : Data J C) (R : FinitePath Gamma.graph)
    (hterminal : R.finish ∈ J.terminalCut)
    (havoid : Gamma.Avoids R D.relevantBB) :
    ∃ S : GroundingFiniteDescent.EscapeSuffixState J C R,
      ¬ S.position.1 + 1 < R.walk.support.length := by
  obtain ⟨P, hPRelevant, hPterminal, hfinishP, hPescape⟩ :=
    exists_terminal_relevant_fragment_meeting_escape D R hterminal havoid
  have hPLegacy : P ∈ GroundingCut.G0 J C :=
    D.relevantG0_subset_legacyG0 hPRelevant
  have hfinishNotBB : R.finish ∉ D.relevantBB := by
    intro hfinishBB
    exact Set.disjoint_left.1 havoid R.finish_mem_support hfinishBB
  have hfinishNotC :
      (PopularAuxiliary.Input.LambdaVertex.old R.finish : J.LV) ∉ C := by
    intro hfinishC
    exact hfinishNotBB (D.CV_subset_relevantBB (by
      simpa only [GroundingCut.mem_CV]))
  have hblockNe : GroundingCut.blockingPoint J C P ≠ R.finish := by
    intro hblock
    exact hfinishNotBB
      (D.relevantBL_subset_relevantBB ⟨P, hPRelevant, hblock⟩)
  obtain ⟨q, hqstart, hqtarget, hqavoid⟩ :=
    GroundingEscapeSuffix.exists_avoiding_terminal_escape
      J C P ⟨hPLegacy.1, hPLegacy⟩ hPterminal hPescape
        hfinishNotC hblockNe
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
    fragment_mem := hPLegacy
    fragment_escape := hPescape
    contact_mem := by simpa only [hiFinish] using hfinishP
    suffix := q
    suffix_start := hqstart.trans
      (congrArg PopularAuxiliary.Input.LambdaVertex.old hiFinish.symm)
    suffix_target := hqtarget
    suffix_avoids := hqavoid }, hilast⟩

/-- Last input-ladder contact before a displayed path position. -/
structure EarlierLadderContact
    (R : FinitePath Gamma.graph) (i : Fin R.walk.support.length) where
  position : Fin R.walk.support.length
  lt_current : position.1 < i.1
  mem_ladder : R.walk.support[position] ∈
    Gamma.vertexSet J.ladder.paths
  open_not_ladder : ∀ m : Fin R.walk.support.length,
    position.1 < m.1 → m.1 < i.1 →
      R.walk.support[m] ∉ Gamma.vertexSet J.ladder.paths

private theorem exists_earlierLadderContact
    (hcovered : SourceCovered J) (R : FinitePath Gamma.graph)
    (hsource : R.start ∈ Gamma.source)
    (i : Fin R.walk.support.length) (hi : 0 < i.1) :
    Nonempty (EarlierLadderContact (J := J) R i) := by
  classical
  obtain ⟨parent, hparent, hinitial⟩ := hcovered hsource
  have hzero : R.walk.support[0] ∈ Gamma.vertexSet J.ladder.paths := by
    refine ⟨parent, hparent, ?_⟩
    rw [R.support_getElem_zero, ← hinitial]
    exact parent.initial_mem_support
  let contacts : Finset (Fin R.walk.support.length) :=
    Finset.univ.filter fun j ↦ j.1 < i.1 ∧
      R.walk.support[j] ∈ Gamma.vertexSet J.ladder.paths
  have hzeroMem : (⟨0, R.support_length_pos⟩ :
      Fin R.walk.support.length) ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi, hzero⟩
  let j : Fin R.walk.support.length := contacts.max' ⟨_, hzeroMem⟩
  have hjmem : j ∈ contacts := Finset.max'_mem contacts ⟨_, hzeroMem⟩
  have hj : j.1 < i.1 ∧ R.walk.support[j] ∈
      Gamma.vertexSet J.ladder.paths := by
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

theorem EarlierLadderContact.open_offLadder
    {R : FinitePath Gamma.graph} {i : Fin R.walk.support.length}
    (K : EarlierLadderContact (J := J) R i)
    (hroof : R.support ⊆ J.roofRegion) :
    ∀ m : Fin R.walk.support.length,
      K.position.1 < m.1 → m.1 < i.1 →
        R.walk.support[m] ∈ J.offLadder := by
  intro m hjm hmi
  exact ⟨hroof (List.getElem_mem m.2), K.open_not_ladder m hjm hmi⟩

private theorem path_edge_head_ne_initial
    {p : Gamma.DPath} {u w : V} (he : (u, w) ∈ p.edgeSet) :
    w ≠ p.initial := by
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
    {P : J.Fragment} (hinit : P.parent.initial ∈ P.path.support) :
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
      exact path_edge_head_ne_initial (P.edges_subset (by
        simpa only [hpath, DirectedPath.Path.edgeSet] using hy)) rfl
  | inr r =>
      have hinit' : P.parent.initial ∈ r.support := by
        simpa only [hpath, DirectedPath.Path.support] using hinit
      have hne'' : P.parent.initial ≠ r.initial := by
        simpa only [hpath, DirectedPath.Path.initial] using hne'
      obtain ⟨y, hy⟩ :=
        _root_.Erdos599.Alternating.Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial
          r hinit' hne''
      exact path_edge_head_ne_initial (P.edges_subset (by
        simpa only [hpath, DirectedPath.Path.edgeSet] using hy)) rfl

private theorem walk_adj_getElem_succ {a b : V}
    (p : Walk Gamma.graph a b) (n : ℕ)
    (hn : n + 1 < p.support.length) :
    Gamma.graph.Adj p.support[n] p.support[n + 1] := by
  induction p generalizing n with
  | nil => simp at hn
  | @cons a c b e p ih =>
      cases n with
      | zero =>
          have hp0 : 0 < p.support.length :=
            List.length_pos_iff.mpr p.support_ne_nil
          have h0 : p.support[0] = c := by
            calc
              p.support[0] = p.support.head p.support_ne_nil :=
                List.getElem_zero hp0
              _ = c := p.head_support
          simpa [h0] using e
      | succ n =>
          have hn' : n + 1 < p.support.length := by simpa using hn
          simpa only [Walk.support_cons, List.getElem_cons_succ,
            Nat.add_assoc] using ih n hn'

/-- Endpoint-aware corridor compilation for the smaller relevant boundary. -/
private theorem relaxedEscape_of_offLadder_interval
    (D : Data J C) (hC : Popular.IsSeparator J.lambda C)
    (R : FinitePath Gamma.graph)
    (j i : Fin R.walk.support.length) (hji : j.1 < i.1)
    (hnotC : ∀ m : Fin R.walk.support.length, m.1 < i.1 →
      (PopularAuxiliary.Input.LambdaVertex.old R.walk.support[m] : J.LV) ∉ C)
    (hInterior : ∀ m : Fin R.walk.support.length,
      j.1 < m.1 → m.1 < i.1 → R.walk.support[m] ∈ J.offLadder)
    (hiBoundary : R.walk.support[i] ∈ J.offLadder ∪ J.targetMarkers ∨
      R.walk.support[i] ∈ Gamma.vertexSet J.ladder.paths)
    (q : FinitePath J.lambda.graph)
    (hqStart : q.start = .old R.walk.support[i])
    (hqTarget : q.finish ∈ J.lambda.target)
    (hqAvoid : J.lambda.Avoids q C) :
    Nonempty (GroundingRelaxedEscape.RelaxedEscape
      J C R.walk.support[j]) := by
  let m : Fin R.walk.support.length := ⟨j.1 + 1, by omega⟩
  have hjm : j.1 < m.1 := by simp only [m]; omega
  have hAdj : Gamma.graph.Adj R.walk.support[j] R.walk.support[m] := by
    simpa [m] using walk_adj_getElem_succ R.walk j.1 (by omega)
  by_cases hmi : m.1 = i.1
  · have hmiFin : m = i := Fin.ext hmi
    exact GroundingRelaxedCorridor.relaxedEscape_of_adjacent_ordinary
      J C hC (by simpa only [hmiFin] using hAdj) (hnotC j hji)
      hiBoundary q hqStart hqTarget hqAvoid
  · have hmiLt : m.1 < i.1 := by
      dsimp only [m] at hmi ⊢
      omega
    have hmOff : R.walk.support[m] ∈ J.offLadder :=
      hInterior m hjm hmiLt
    have hInterior' : ∀ l : Fin R.walk.support.length,
        m.1 < l.1 → l.1 < i.1 → R.walk.support[l] ∈ J.offLadder := by
      intro l hml hli
      exact hInterior l (hjm.trans hml) hli
    obtain ⟨Em⟩ := relaxedEscape_of_offLadder_interval
      D hC R m i hmiLt hnotC hInterior' hiBoundary
        q hqStart hqTarget hqAvoid
    obtain ⟨qm, hqmStart, hqmTarget, hqmAvoid⟩ :=
      GroundingRelaxedCorridor.exists_ordinaryEscape_of_relaxed_of_start_mem
        J C (Or.inl hmOff) Em
    exact GroundingRelaxedCorridor.relaxedEscape_of_adjacent_ordinary
      J C hC hAdj (hnotC j hji) (Or.inl (Or.inl hmOff))
        qm hqmStart hqmTarget hqmAvoid
termination_by i.1 - j.1
decreasing_by omega

private theorem escapeSuffixState_position_ne_zero
    (D : Data J C) (hcovered : SourceCovered J)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (havoid : Gamma.Avoids R D.relevantBB)
    (A : GroundingFiniteDescent.EscapeSuffixState J C R) :
    A.position.1 ≠ 0 := by
  intro hpos
  have hposFin : A.position =
      (⟨0, R.support_length_pos⟩ : Fin R.walk.support.length) := Fin.ext hpos
  have hxStart : R.walk.support[A.position] = R.start :=
    (congrArg (fun i : Fin R.walk.support.length ↦ R.walk.support[i])
      hposFin).trans R.support_getElem_zero
  obtain ⟨parent, hparent, hinitial⟩ := hcovered hsource
  have hxParent : R.walk.support[A.position] ∈ parent.support := by
    rw [hxStart, ← hinitial]
    exact parent.initial_mem_support
  obtain ⟨Q, hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      J C hparent hxParent
  have hxInitial : Q.path.initial = R.walk.support[A.position] := by
    have hparentInitQ : Q.parent.initial ∈ Q.path.support := by
      simpa only [hQparent, hinitial, hxStart] using hxQ
    calc
      Q.path.initial = Q.parent.initial :=
        fragment_initial_eq_parent_initial_of_mem hparentInitQ
      _ = parent.initial := congrArg DirectedPath.Path.initial hQparent
      _ = R.walk.support[A.position] := by rw [hinitial, hxStart]
  let E : GroundingRelaxedEscape.RelaxedEscape
      J C R.walk.support[A.position] :=
    { route := A.suffix
      start_eq := Or.inl A.suffix_start
      target := A.suffix_target
      avoids := A.suffix_avoids
      old_not_mem := old_not_mem_cut_of_avoids D R havoid A.position }
  have hQescape : Q.MeetsEscape J C :=
    ⟨R.walk.support[A.position], hxQ, ⟨E⟩⟩
  have hQRelevant : Q ∈ D.relevantG0 :=
    D.fragment_meeting_escape_mem_relevantG0 Q hQfragment hQescape
  have hblockBefore : GroundingCut.BeforeEq Q.path
      (GroundingCut.blockingPoint J C Q) R.walk.support[A.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      J C Q hQescape hxQ ⟨E⟩
  have hinitialBefore : GroundingCut.BeforeEq Q.path
      R.walk.support[A.position] (GroundingCut.blockingPoint J C Q) := by
    rw [← hxInitial]
    exact GroundingFragmentWarp.initial_beforeEq_of_mem
      (GroundingCut.blockingPoint_mem_support J C Q hQRelevant.1.2)
  have hblockEq : GroundingCut.blockingPoint J C Q =
      R.walk.support[A.position] :=
    GroundingCutDecoder.beforeEq_antisymm hblockBefore hinitialBefore
  have hxBB : R.walk.support[A.position] ∈ D.relevantBB :=
    D.relevantBL_subset_relevantBB ⟨Q, hQRelevant, hblockEq⟩
  exact Set.disjoint_left.1 havoid
    (List.getElem_mem A.position.2) hxBB

private theorem exists_strictlyEarlier_escapeSuffixState
    (D : Data J C) (hcovered : SourceCovered J)
    (hC : Popular.IsSeparator J.lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hroof : R.support ⊆ J.roofRegion)
    (havoid : Gamma.Avoids R D.relevantBB)
    (A : GroundingFiniteDescent.EscapeSuffixState J C R) :
    ∃ B : GroundingFiniteDescent.EscapeSuffixState J C R,
      B.position.1 < A.position.1 := by
  have hi : 0 < A.position.1 := Nat.pos_of_ne_zero
    (escapeSuffixState_position_ne_zero D hcovered R hsource havoid A)
  obtain ⟨K⟩ := exists_earlierLadderContact
    hcovered R hsource A.position hi
  obtain ⟨E⟩ := relaxedEscape_of_offLadder_interval
    D hC R K.position A.position K.lt_current
      (fun m _hm ↦ old_not_mem_cut_of_avoids D R havoid m)
      (K.open_offLadder hroof)
      (Or.inr ⟨A.fragment.parent, A.fragment.parent_mem,
        A.fragment.support_subset A.contact_mem⟩)
      A.suffix A.suffix_start A.suffix_target A.suffix_avoids
  obtain ⟨parent, hparent, hxParent⟩ := K.mem_ladder
  obtain ⟨Q, _hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      J C hparent hxParent
  have hQescape : Q.MeetsEscape J C :=
    ⟨R.walk.support[K.position], hxQ, ⟨E⟩⟩
  have hQRelevant : Q ∈ D.relevantG0 :=
    D.fragment_meeting_escape_mem_relevantG0 Q hQfragment hQescape
  have hQLegacy : Q ∈ GroundingCut.G0 J C :=
    D.relevantG0_subset_legacyG0 hQRelevant
  let b := GroundingCut.blockingPoint J C Q
  have hbQ : b ∈ Q.path.support :=
    GroundingCut.blockingPoint_mem_support J C Q hQRelevant.1.2
  have hbEscape : b ∈ J.escapeRegion C :=
    GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      J C Q hQescape
  have hbeforeEq : GroundingCut.BeforeEq Q.path b
      R.walk.support[K.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      J C Q hQescape hxQ ⟨E⟩
  by_cases hbeq : b = R.walk.support[K.position]
  · have hxBB : R.walk.support[K.position] ∈ D.relevantBB :=
      D.relevantBL_subset_relevantBB ⟨Q, hQRelevant, hbeq⟩
    exact False.elim (Set.disjoint_left.1 havoid
      (List.getElem_mem K.position.2) hxBB)
  · obtain ⟨Eb⟩ := hbEscape
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ :=
      GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
        J C Q hQfragment ⟨hbeforeEq, hbeq⟩
        (old_not_mem_cut_of_avoids D R havoid K.position) Eb
    let B : GroundingFiniteDescent.EscapeSuffixState J C R :=
      { position := K.position
        fragment := Q
        fragment_mem := hQLegacy
        fragment_escape := hQescape
        contact_mem := hxQ
        suffix := q
        suffix_start := hqStart
        suffix_target := hqTarget
        suffix_avoids := hqAvoid }
    exact ⟨B, K.lt_current⟩

/-- Generic finite descent for the relevant boundary. -/
theorem relevantFiniteDescentDecoder
    (D : Data J C) (hcovered : SourceCovered J)
    (hterminalSep : Popular.IsSeparator Gamma J.terminalCut)
    (hC : Popular.IsSeparator J.lambda C) :
    RelevantFiniteDescentDecoder D := by
  intro R hsource hterminal havoid
  have hmeet : R.walk.Meets J.terminalCut :=
    ⟨R.finish, R.finish_mem_support, hterminal⟩
  let Q : FinitePath Gamma.graph := R.firstHit J.terminalCut hmeet
  have hQsource : Q.start ∈ Gamma.source := hsource
  have hQterminal : Q.finish ∈ J.terminalCut :=
    R.firstHit_finish_mem J.terminalCut hmeet
  have hQavoid : Gamma.Avoids Q D.relevantBB :=
    firstHit_avoids D R havoid hmeet
  have hQroof : Q.support ⊆ J.roofRegion := by
    apply support_subset_roofRegion_of_no_terminal_before
      hterminalSep Q hQsource hQterminal
    intro x hx
    exact R.firstHit_no_mem_before J.terminalCut hmeet hx
  obtain ⟨seed, _⟩ :=
    exists_initialEscapeSuffixState D Q hQterminal hQavoid
  let A : GroundingFiniteDescent.LastFragmentDescentSystem J C Q :=
    { seed := seed
      resolve := fun T ↦ Or.inr
        (exists_strictlyEarlier_escapeSuffixState
          D hcovered hC Q hQsource hQroof hQavoid T) }
  exact A.exists_avoiding_source_target_path

/-- The relevant decoder also supplies the canonical coarse-`BB` decoder
used by the public deferred switch output. -/
theorem finiteDescentDecoder
    (D : Data J C) (hcovered : SourceCovered J)
    (hterminalSep : Popular.IsSeparator Gamma J.terminalCut)
    (hC : Popular.IsSeparator J.lambda C) :
    GroundingCut.FiniteDescentDecoder J C := by
  have H := relevantFiniteDescentDecoder D hcovered hterminalSep hC
  intro R hsource hterminal havoid
  exact H R hsource hterminal
    (havoid.mono_right D.relevantBB_subset_legacyBB)

/-- The smaller relevant boundary is itself an ambient separator. -/
theorem relevantBB_isSeparator
    (D : Data J C) (hcovered : SourceCovered J)
    (hterminalSep : Popular.IsSeparator Gamma J.terminalCut)
    (hC : Popular.IsSeparator J.lambda C) :
    Popular.IsSeparator Gamma D.relevantBB := by
  apply PopularSwitching.isSeparator_of_meets_paths_to_separator hterminalSep
  intro R hsource hterminal
  by_contra hnotMeet
  have havoid : Gamma.Avoids R D.relevantBB :=
    (Gamma.avoids_iff_not_meets R D.relevantBB).2 hnotMeet
  obtain ⟨q, hqsource, hqtarget, hqavoid⟩ :=
    relevantFiniteDescentDecoder D hcovered hterminalSep hC
      R hsource hterminal havoid
  exact PopularAuxiliary.Input.no_avoiding_source_target_path
    J.lambda C hC q hqsource hqtarget hqavoid

/-! ## Endpoint-open descent for source-first relevant points -/

/-- The exact irreducible endpoint branch: the relaxed escape begins after
one virtual original forward step out of the first relevant-boundary point. -/
structure RelevantVirtualEscape
    (J : Input Gamma I) (C : Set J.LV) (b : V) where
  escape : GroundingRelaxedEscape.RelaxedEscape J C b
  virtual : J.RelaxedForwardStep b escape.route.start

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
    (D : Data J C) (R : FinitePath Gamma.graph)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ D.relevantBB)
    (i : Fin R.walk.support.length) :
    ∀ m : Fin R.walk.support.length, m.1 < i.1 →
      (PopularAuxiliary.Input.LambdaVertex.old R.walk.support[m] : J.LV) ∉ C := by
  intro m hmi hmC
  have hmBB : R.walk.support[m] ∈ D.relevantBB :=
    D.CV_subset_relevantBB (by simpa only [GroundingCut.mem_CV])
  exact hfirst (getElem_mem_dropLast_of_lt R m i hmi) hmBB

private theorem endpointOpen_state_position_ne_zero
    (D : Data J C) (hcovered : SourceCovered J)
    (hC : Popular.IsSeparator J.lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hfinish : R.finish ∉ Gamma.source)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ D.relevantBB)
    (A : GroundingFiniteDescent.EscapeSuffixState J C R) :
    A.position.1 ≠ 0 := by
  intro hpos
  have hposFin : A.position =
      (⟨0, R.support_length_pos⟩ : Fin R.walk.support.length) := Fin.ext hpos
  have hxStart : R.walk.support[A.position] = R.start :=
    (congrArg (fun i : Fin R.walk.support.length ↦ R.walk.support[i])
      hposFin).trans R.support_getElem_zero
  have hstartNeFinish : R.start ≠ R.finish := by
    intro hEq
    exact hfinish (hEq ▸ hsource)
  have hstartDrop : R.start ∈ R.walk.support.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast R.start_mem_support (by
      simpa only [R.walk.getLast_support] using hstartNeFinish)
  obtain ⟨parent, hparent, hinitial⟩ := hcovered hsource
  have hxParent : R.walk.support[A.position] ∈ parent.support := by
    rw [hxStart, ← hinitial]
    exact parent.initial_mem_support
  obtain ⟨Q, hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      J C hparent hxParent
  have hxInitial : Q.path.initial = R.walk.support[A.position] := by
    have hparentInitQ : Q.parent.initial ∈ Q.path.support := by
      simpa only [hQparent, hinitial, hxStart] using hxQ
    calc
      Q.path.initial = Q.parent.initial :=
        fragment_initial_eq_parent_initial_of_mem hparentInitQ
      _ = parent.initial := congrArg DirectedPath.Path.initial hQparent
      _ = R.walk.support[A.position] := by rw [hinitial, hxStart]
  have hxNotC :
      (PopularAuxiliary.Input.LambdaVertex.old
        R.walk.support[A.position] : J.LV) ∉ C := by
    intro hxC
    have hxBB : R.walk.support[A.position] ∈ D.relevantBB :=
      D.CV_subset_relevantBB (by simpa only [GroundingCut.mem_CV])
    exact hfirst (by simpa only [hxStart] using hstartDrop) hxBB
  let E : GroundingRelaxedEscape.RelaxedEscape
      J C R.walk.support[A.position] :=
    { route := A.suffix
      start_eq := Or.inl A.suffix_start
      target := A.suffix_target
      avoids := A.suffix_avoids
      old_not_mem := hxNotC }
  have hQescape : Q.MeetsEscape J C :=
    ⟨R.walk.support[A.position], hxQ, ⟨E⟩⟩
  have hQRelevant : Q ∈ D.relevantG0 :=
    D.fragment_meeting_escape_mem_relevantG0 Q hQfragment hQescape
  have hblockBefore : GroundingCut.BeforeEq Q.path
      (GroundingCut.blockingPoint J C Q) R.walk.support[A.position] :=
    GroundingCut.blockingPoint_beforeEq_escape J C Q hQescape hxQ ⟨E⟩
  have hinitialBefore : GroundingCut.BeforeEq Q.path
      R.walk.support[A.position] (GroundingCut.blockingPoint J C Q) := by
    rw [← hxInitial]
    exact GroundingFragmentWarp.initial_beforeEq_of_mem
      (GroundingCut.blockingPoint_mem_support J C Q hQRelevant.1.2)
  have hblockEq : GroundingCut.blockingPoint J C Q =
      R.walk.support[A.position] :=
    GroundingCutDecoder.beforeEq_antisymm hblockBefore hinitialBefore
  have hxBB : R.walk.support[A.position] ∈ D.relevantBB :=
    D.relevantBL_subset_relevantBB ⟨Q, hQRelevant, hblockEq⟩
  exact hfirst (by simpa only [hxStart] using hstartDrop) hxBB

private theorem endpointOpen_exists_strictlyEarlier_state
    (D : Data J C) (hcovered : SourceCovered J)
    (hC : Popular.IsSeparator J.lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hfinish : R.finish ∉ Gamma.source)
    (hroof : R.support ⊆ J.roofRegion)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ D.relevantBB)
    (A : GroundingFiniteDescent.EscapeSuffixState J C R) :
    ∃ B : GroundingFiniteDescent.EscapeSuffixState J C R,
      B.position.1 < A.position.1 := by
  have hi : 0 < A.position.1 := Nat.pos_of_ne_zero
    (endpointOpen_state_position_ne_zero
      D hcovered hC R hsource hfinish hfirst A)
  obtain ⟨K⟩ := exists_earlierLadderContact hcovered R hsource A.position hi
  obtain ⟨E⟩ := relaxedEscape_of_offLadder_interval
    D hC R K.position A.position K.lt_current
      (endpointOpen_old_not_mem_cut_before D R hfirst A.position)
      (K.open_offLadder hroof)
      (Or.inr ⟨A.fragment.parent, A.fragment.parent_mem,
        A.fragment.support_subset A.contact_mem⟩)
      A.suffix A.suffix_start A.suffix_target A.suffix_avoids
  obtain ⟨parent, hparent, hxParent⟩ := K.mem_ladder
  obtain ⟨Q, _hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      J C hparent hxParent
  have hQescape : Q.MeetsEscape J C :=
    ⟨R.walk.support[K.position], hxQ, ⟨E⟩⟩
  have hQRelevant : Q ∈ D.relevantG0 :=
    D.fragment_meeting_escape_mem_relevantG0 Q hQfragment hQescape
  have hQLegacy : Q ∈ GroundingCut.G0 J C :=
    D.relevantG0_subset_legacyG0 hQRelevant
  let b := GroundingCut.blockingPoint J C Q
  have hbEscape : b ∈ J.escapeRegion C :=
    GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      J C Q hQescape
  have hbeforeEq : GroundingCut.BeforeEq Q.path b
      R.walk.support[K.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      J C Q hQescape hxQ ⟨E⟩
  by_cases hbeq : b = R.walk.support[K.position]
  · have hxBB : R.walk.support[K.position] ∈ D.relevantBB :=
      D.relevantBL_subset_relevantBB ⟨Q, hQRelevant, hbeq⟩
    exact False.elim
      (hfirst (getElem_mem_dropLast_of_lt R K.position A.position
        K.lt_current) hxBB)
  · obtain ⟨Eb⟩ := hbEscape
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ :=
      GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
        J C Q hQfragment ⟨hbeforeEq, hbeq⟩
        (endpointOpen_old_not_mem_cut_before
          D R hfirst A.position K.position K.lt_current) Eb
    let B : GroundingFiniteDescent.EscapeSuffixState J C R :=
      { position := K.position
        fragment := Q
        fragment_mem := hQLegacy
        fragment_escape := hQescape
        contact_mem := hxQ
        suffix := q
        suffix_start := hqStart
        suffix_target := hqTarget
        suffix_avoids := hqAvoid }
    exact ⟨B, K.lt_current⟩

/-- An ordinary escape at a source-first relevant blocker forces that
blocker to be an ambient source, by strict finite endpoint-open descent. -/
theorem endpointOpen_ordinary_escape_implies_source
    (D : Data J C) (hcovered : SourceCovered J)
    (hC : Popular.IsSeparator J.lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hroof : R.support ⊆ J.roofRegion)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ D.relevantBB)
    (P : J.Fragment) (hP : P ∈ D.relevantG0)
    (hblock : GroundingCut.blockingPoint J C P = R.finish)
    (hescape : P.MeetsEscape J C)
    (E : GroundingRelaxedEscape.RelaxedEscape J C R.finish)
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
    exact GroundingCut.blockingPoint_mem_support J C P hP.1.2
  let seed : GroundingFiniteDescent.EscapeSuffixState J C R :=
    { position := i
      fragment := P
      fragment_mem := D.relevantG0_subset_legacyG0 hP
      fragment_escape := hescape
      contact_mem := by simpa only [hiFinish] using hfinishP
      suffix := E.route
      suffix_start := hordinary.trans
        (congrArg PopularAuxiliary.Input.LambdaVertex.old hiFinish.symm)
      suffix_target := E.target
      suffix_avoids := E.avoids }
  have impossible : ∀ m : Nat,
      ∀ A : GroundingFiniteDescent.EscapeSuffixState J C R,
      A.position.1 = m → False := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro A hAm
        obtain ⟨B, hBA⟩ := endpointOpen_exists_strictlyEarlier_state
          D hcovered hC R hsource hfinish hroof hfirst A
        exact ih B.position.1 (by simpa only [hAm] using hBA) B rfl
  exact False.elim (impossible seed.position.1 seed rfl)

/-- An escaping relevant blocker displayed as a source-first endpoint is
either itself an ambient source, or has an actual virtual-forward relaxed
escape.  The ordinary escape branch is eliminated by strict finite descent. -/
theorem sourceFirst_escapeBlocker_source_or_virtual
    (D : Data J C) (hcovered : SourceCovered J)
    (hC : Popular.IsSeparator J.lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hroof : R.support ⊆ J.roofRegion)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ D.relevantBB)
    (P : J.Fragment) (hP : P ∈ D.relevantG0)
    (hblock : GroundingCut.blockingPoint J C P = R.finish)
    (hescape : P.MeetsEscape J C) :
    R.finish ∈ Gamma.source ∨
      Nonempty (RelevantVirtualEscape J C R.finish) := by
  have hbEscape : R.finish ∈ J.escapeRegion C := by
    rw [← hblock]
    exact GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      J C P hescape
  obtain ⟨E⟩ := hbEscape
  rcases E.start_eq with hordinary | hvirtual
  · exact Or.inl (endpointOpen_ordinary_escape_implies_source
      D hcovered hC R hsource hroof hfirst P hP hblock hescape E hordinary)
  · exact Or.inr ⟨⟨E, hvirtual⟩⟩

end GroundingInputRelevantDecoder
end Erdos599

#print axioms
  Erdos599.GroundingInputRelevantDecoder.relevantFiniteDescentDecoder
#print axioms
  Erdos599.GroundingInputRelevantDecoder.finiteDescentDecoder
#print axioms
  Erdos599.GroundingInputRelevantDecoder.sourceFirst_escapeBlocker_source_or_virtual
