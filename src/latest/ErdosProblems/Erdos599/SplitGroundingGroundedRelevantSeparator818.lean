/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantCut
import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorGeometry
import ErdosProblems.Erdos599.GroundingRelaxedCorridor
import ErdosProblems.Erdos599.GroundingTerminalFragment
import ErdosProblems.Erdos599.GroundingFragmentPartition
import ErdosProblems.Erdos599.GroundingEscapeSuffix
import ErdosProblems.Erdos599.GroundingFiniteDescent

/-!
# Assertion 8.18 for the source-correct filtered split cut

This repeats the finite last-contact descent with avoidance of
`splitGroundedRelevantBB`, whose blocking family first removes `H_empty`.  The
well-founded state still stores membership in the legacy coarse `G0`; every
fragment constructed here belongs to the filtered family and is therefore
converted to that weaker fact.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev ReducedInput (L : Gamma.KappaLadder kappa)
    (hL : L.IsSplitLegal) :=
  L.splitGroundedPopularAuxiliaryInput hL

private abbrev ReducedLV (L : Gamma.KappaLadder kappa)
    (_hL : L.IsSplitLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-- The literal decoder property for the filtered boundary. -/
def SplitGroundedRelevantFiniteDescentDecoder
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) : Prop :=
  ∀ R : FinitePath Gamma.graph,
    R.start ∈ Gamma.source →
    R.finish ∈ (ReducedInput L hL).terminalCut →
    Gamma.Avoids R (L.splitGroundedRelevantBB hL C) →
    ∃ q : FinitePath (ReducedInput L hL).lambda.graph,
      q.start ∈ (ReducedInput L hL).lambda.source ∧
      q.finish ∈ (ReducedInput L hL).lambda.target ∧
      (ReducedInput L hL).lambda.Avoids q C

private theorem firstHit_avoids
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R (L.splitGroundedRelevantBB hL C))
    (hmeet : R.walk.Meets (ReducedInput L hL).terminalCut) :
    Gamma.Avoids (R.firstHit (ReducedInput L hL).terminalCut hmeet)
      (L.splitGroundedRelevantBB hL C) := by
  change Disjoint
    (R.firstHit (ReducedInput L hL).terminalCut hmeet).support
    (L.splitGroundedRelevantBB hL C)
  rw [Set.disjoint_left]
  intro x hx hcut
  exact Set.disjoint_left.1 havoid
    (R.firstHit_support_subset (ReducedInput L hL).terminalCut hmeet hx) hcut

private theorem old_not_mem_cut_of_reduced_avoids
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R (L.splitGroundedRelevantBB hL C))
    (i : Fin R.walk.support.length) :
    (PopularAuxiliary.Input.LambdaVertex.old R.walk.support[i] :
      ReducedLV L hL) ∉ C := by
  intro hiC
  have hiBB : R.walk.support[i] ∈ L.splitGroundedRelevantBB hL C :=
    L.splitGroundedCV_subset_relevantBB hL C (by
      simpa only [GroundingCut.mem_CV])
  exact Set.disjoint_left.1 havoid (List.getElem_mem i.2) hiBB

private theorem support_subset_roofRegion_of_no_terminal_before
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hfinish : R.finish ∈ (ReducedInput L hL).terminalCut)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ (ReducedInput L hL).terminalCut) :
    R.support ⊆ (ReducedInput L hL).roofRegion := by
  have hseparator := splitGroundedPopularAuxiliary_terminalCut_isSeparator L hL
  have hstartRoof : R.start ∈ Gamma.roof
      (ReducedInput L hL).terminalCut := by
    intro p hp
    exact hseparator p (hp.1 ▸ hsource) hp.2
  have hterminal : ∀ t,
      Gamma.terminal? (.inl R : Gamma.DPath) = some t →
        t ∈ (ReducedInput L hL).terminalCut := by
    intro t ht
    have hrt : R.finish = t := Option.some.inj ht
    simpa only [hrt] using hfinish
  have hinter :
      (DirectedPath.Path.support (.inl R : Gamma.DPath) ∩
          (ReducedInput L hL).terminalCut) ⊆ ({R.finish} : Set V) := by
    intro x hx
    apply Set.mem_singleton_iff.2
    by_contra hxf
    have hxlast : x ≠ R.walk.support.getLast R.walk.support_ne_nil := by
      simpa only [R.walk.getLast_support] using hxf
    exact hfirst (List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxlast) hx.2
  exact Gamma.pathSupportRoof (.inl R : Gamma.DPath)
    (ReducedInput L hL).terminalCut hstartRoof hterminal hinter

private theorem exists_terminal_relevant_fragment_meeting_escape
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) (R : FinitePath Gamma.graph)
    (hterminal : R.finish ∈ (ReducedInput L hL).terminalCut)
    (havoid : Gamma.Avoids R (L.splitGroundedRelevantBB hL C)) :
    ∃ P : (ReducedInput L hL).Fragment,
      P ∈ L.splitGroundedRelevantG0 hL C ∧
      P.path.terminal? = some R.finish ∧
      R.finish ∈ P.path.support ∧
      P.MeetsEscape (ReducedInput L hL) C := by
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
          (ReducedInput L hL) C hpEssential.1 hfinishParent
      obtain ⟨hPfinite, hterminalP⟩ :=
        GroundingTerminalFragment.finite_and_terminal_eq_parent_finish
          (ReducedInput L hL) C p P hPfragment hparent
            (by simpa only [hpFinish] using hfinishP)
      have hPterminal : P.path.terminal? = some R.finish := by
        simpa only [hpFinish] using hterminalP
      have hparentEssential :
          P.parent ∈ (ReducedInput L hL).essentialLadder := by
        simpa only [hparent] using hpEssential
      have hPnotEmpty : P ∉ L.splitGroundedHEmpty hL C := by
        rintro ⟨_hfragment, _hwhole, hrecord, _hcase⟩
        exact L.splitGrounded_essential_not_recorded hL hparentEssential hrecord
      have hPReduced : P ∈ L.splitGroundedG0 hL C :=
        ⟨⟨hPfragment, hPnotEmpty⟩, Or.inr hPfinite⟩
      have hPG0 : P ∈ L.splitGroundedRelevantG0 hL C :=
        L.splitGrounded_mem_relevantG0_of_mem_reduced_of_terminalCut
          hL C P hPReduced hPterminal hfinishTerminalCut
      have hescape : P.MeetsEscape (ReducedInput L hL) C := by
        by_contra hnoEscape
        have hblock : GroundingCut.blockingPoint
            (ReducedInput L hL) C P = R.finish :=
          GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
            (ReducedInput L hL) C P hnoEscape hPterminal
        have hBL : R.finish ∈ L.splitGroundedRelevantBL hL C :=
          ⟨P, hPG0, hblock⟩
        exact Set.disjoint_left.1 havoid R.finish_mem_support
          (L.splitGroundedRelevantBL_subset_BB hL C hBL)
      exact ⟨P, hPG0, hPterminal,
        by simpa only [hpFinish] using hfinishP, hescape⟩

private theorem exists_initialEscapeSuffixState
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) (R : FinitePath Gamma.graph)
    (hterminal : R.finish ∈ (ReducedInput L hL).terminalCut)
    (havoid : Gamma.Avoids R (L.splitGroundedRelevantBB hL C)) :
    ∃ S : GroundingFiniteDescent.EscapeSuffixState
        (ReducedInput L hL) C R,
      ¬ S.position.1 + 1 < R.walk.support.length := by
  obtain ⟨P, hPReduced, hPterminal, hfinishP, hPescape⟩ :=
    exists_terminal_relevant_fragment_meeting_escape
      L hL C R hterminal havoid
  have hPLegacy : P ∈ GroundingCut.G0 (ReducedInput L hL) C :=
    L.splitGroundedRelevantG0_subset_legacyG0 hL C hPReduced
  have hfinishNotBB : R.finish ∉ L.splitGroundedRelevantBB hL C := by
    intro hfinishBB
    exact Set.disjoint_left.1 havoid R.finish_mem_support hfinishBB
  have hfinishNotC :
      (PopularAuxiliary.Input.LambdaVertex.old R.finish : ReducedLV L hL) ∉ C := by
    intro hfinishC
    exact hfinishNotBB (L.splitGroundedCV_subset_relevantBB hL C (by
      simpa only [GroundingCut.mem_CV]))
  have hblockNe : GroundingCut.blockingPoint
      (ReducedInput L hL) C P ≠ R.finish := by
    intro hblock
    exact hfinishNotBB (L.splitGroundedRelevantBL_subset_BB hL C
      ⟨P, hPReduced, hblock⟩)
  obtain ⟨q, hqstart, hqtarget, hqavoid⟩ :=
    GroundingEscapeSuffix.exists_avoiding_terminal_escape
      (ReducedInput L hL) C P ⟨hPLegacy.1, hPLegacy⟩ hPterminal
        hPescape hfinishNotC hblockNe
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

/-- The last ladder contact strictly before a displayed ambient-path
position.  This public form is reused by endpoint-open first-hit descent. -/
structure SplitGroundedRelevantEarlierLadderContact
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (R : FinitePath Gamma.graph)
    (i : Fin R.walk.support.length) where
  position : Fin R.walk.support.length
  lt_current : position.1 < i.1
  mem_ladder : R.walk.support[position] ∈
    Gamma.vertexSet (ReducedInput L hL).ladder.paths
  open_not_ladder : ∀ m : Fin R.walk.support.length,
    position.1 < m.1 → m.1 < i.1 →
      R.walk.support[m] ∉ Gamma.vertexSet (ReducedInput L hL).ladder.paths

theorem exists_splitGroundedRelevantEarlierLadderContact
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (i : Fin R.walk.support.length) (hi : 0 < i.1) :
    Nonempty (SplitGroundedRelevantEarlierLadderContact L hL R i) := by
  classical
  have hxInitial : R.start ∈ Gamma.initialSet L.limitWarp :=
    hL.source_subset_initialSet_limitWarp hsource
  obtain ⟨parent, hparent, hinitial⟩ := hxInitial
  have hzero : R.walk.support[0] ∈
      Gamma.vertexSet (ReducedInput L hL).ladder.paths := by
    refine ⟨parent, hparent, ?_⟩
    rw [R.support_getElem_zero, ← hinitial]
    exact parent.initial_mem_support
  let contacts : Finset (Fin R.walk.support.length) :=
    Finset.univ.filter fun j ↦ j.1 < i.1 ∧
      R.walk.support[j] ∈ Gamma.vertexSet (ReducedInput L hL).ladder.paths
  have hzeroMem : (⟨0, R.support_length_pos⟩ :
      Fin R.walk.support.length) ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi, hzero⟩
  let j : Fin R.walk.support.length := contacts.max' ⟨_, hzeroMem⟩
  have hjmem : j ∈ contacts := Finset.max'_mem contacts ⟨_, hzeroMem⟩
  have hj : j.1 < i.1 ∧ R.walk.support[j] ∈
      Gamma.vertexSet (ReducedInput L hL).ladder.paths := by
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

theorem SplitGroundedRelevantEarlierLadderContact.open_offLadder
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitLegal}
    {R : FinitePath Gamma.graph} {i : Fin R.walk.support.length}
    (J : SplitGroundedRelevantEarlierLadderContact L hL R i)
    (hroof : R.support ⊆ (ReducedInput L hL).roofRegion) :
    ∀ m : Fin R.walk.support.length,
      J.position.1 < m.1 → m.1 < i.1 →
        R.walk.support[m] ∈ (ReducedInput L hL).offLadder := by
  intro m hjm hmi
  exact ⟨hroof (List.getElem_mem m.2), J.open_not_ladder m hjm hmi⟩

private theorem reduced_path_edge_head_ne_initial
    {p : Gamma.DPath} {u v : V} (he : (u, v) ∈ p.edgeSet) :
    v ≠ p.initial := by
  rcases p with p | r
  · exact Alternating.FinitePath.target_ne_start_of_mem_edgeSet p he
  · rintro rfl
    rcases he with ⟨n, hn⟩
    have hzero : n + 1 = 0 := by
      apply r.injective
      exact (congrArg Prod.snd hn).symm
    omega

theorem splitGroundedRelevant_fragment_initial_eq_parent_initial_of_mem
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitLegal}
    {P : (ReducedInput L hL).Fragment}
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
        Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          p hinit' hne''
      exact reduced_path_edge_head_ne_initial (P.edges_subset (by
        simpa only [hpath, DirectedPath.Path.edgeSet] using hy)) rfl
  | inr r =>
      have hinit' : P.parent.initial ∈ r.support := by
        simpa only [hpath, DirectedPath.Path.support] using hinit
      have hne'' : P.parent.initial ≠ r.initial := by
        simpa only [hpath, DirectedPath.Path.initial] using hne'
      obtain ⟨y, hy⟩ :=
        Alternating.Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial
          r hinit' hne''
      exact reduced_path_edge_head_ne_initial (P.edges_subset (by
        simpa only [hpath, DirectedPath.Path.edgeSet] using hy)) rfl

private theorem reduced_walk_adj_getElem_succ {a b : V}
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

/-- Compile an open ordinary corridor backwards from `i` to `j`.  The
endpoint-aware form asks only that old vertices strictly before `i` avoid
the auxiliary cut; the vertex at `i` itself may be the allowed first
boundary hit. -/
theorem splitGroundedRelevant_relaxedEscape_of_offLadder_interval
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL))
    (hC : Popular.IsSeparator (ReducedInput L hL).lambda C)
    (R : FinitePath Gamma.graph)
    (j i : Fin R.walk.support.length) (hji : j.1 < i.1)
    (hnotC : ∀ m : Fin R.walk.support.length, m.1 < i.1 →
      (PopularAuxiliary.Input.LambdaVertex.old R.walk.support[m] :
        ReducedLV L hL) ∉ C)
    (hInterior : ∀ m : Fin R.walk.support.length,
      j.1 < m.1 → m.1 < i.1 →
        R.walk.support[m] ∈ (ReducedInput L hL).offLadder)
    (hiBoundary :
      R.walk.support[i] ∈ (ReducedInput L hL).offLadder ∪
          (ReducedInput L hL).targetMarkers ∨
        R.walk.support[i] ∈ Gamma.vertexSet (ReducedInput L hL).ladder.paths)
    (q : FinitePath (ReducedInput L hL).lambda.graph)
    (hqStart : q.start = .old R.walk.support[i])
    (hqTarget : q.finish ∈ (ReducedInput L hL).lambda.target)
    (hqAvoid : (ReducedInput L hL).lambda.Avoids q C) :
    Nonempty (GroundingRelaxedEscape.RelaxedEscape
      (ReducedInput L hL) C R.walk.support[j]) := by
  let m : Fin R.walk.support.length := ⟨j.1 + 1, by omega⟩
  have hjm : j.1 < m.1 := by simp only [m]; omega
  have hAdj : Gamma.graph.Adj R.walk.support[j] R.walk.support[m] := by
    simpa [m] using reduced_walk_adj_getElem_succ R.walk j.1 (by omega)
  by_cases hmi : m.1 = i.1
  · have hmiFin : m = i := Fin.ext hmi
    exact GroundingRelaxedCorridor.relaxedEscape_of_adjacent_ordinary
      (ReducedInput L hL) C hC (by simpa only [hmiFin] using hAdj)
      (hnotC j hji)
      hiBoundary q hqStart hqTarget hqAvoid
  · have hmiLt : m.1 < i.1 := by
      dsimp only [m] at hmi ⊢
      omega
    have hmOff : R.walk.support[m] ∈ (ReducedInput L hL).offLadder :=
      hInterior m hjm hmiLt
    have hInterior' : ∀ l : Fin R.walk.support.length,
        m.1 < l.1 → l.1 < i.1 →
          R.walk.support[l] ∈ (ReducedInput L hL).offLadder := by
      intro l hml hli
      exact hInterior l (hjm.trans hml) hli
    obtain ⟨Em⟩ := splitGroundedRelevant_relaxedEscape_of_offLadder_interval
      L hL C hC R m i hmiLt hnotC hInterior' hiBoundary
        q hqStart hqTarget hqAvoid
    obtain ⟨qm, hqmStart, hqmTarget, hqmAvoid⟩ :=
      GroundingRelaxedCorridor.exists_ordinaryEscape_of_relaxed_of_start_mem
        (ReducedInput L hL) C (Or.inl hmOff) Em
    exact GroundingRelaxedCorridor.relaxedEscape_of_adjacent_ordinary
      (ReducedInput L hL) C hC hAdj
      (hnotC j hji)
      (Or.inl (Or.inl hmOff)) qm hqmStart hqmTarget hqmAvoid
termination_by i.1 - j.1
decreasing_by omega

private theorem escapeSuffixState_position_ne_zero
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL))
    (hC : Popular.IsSeparator (ReducedInput L hL).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (havoid : Gamma.Avoids R (L.splitGroundedRelevantBB hL C))
    (S : GroundingFiniteDescent.EscapeSuffixState
      (ReducedInput L hL) C R) :
    S.position.1 ≠ 0 := by
  intro hpos
  have hposFin : S.position =
      (⟨0, R.support_length_pos⟩ : Fin R.walk.support.length) := Fin.ext hpos
  have hxStart : R.walk.support[S.position] = R.start :=
    (congrArg (fun i : Fin R.walk.support.length ↦ R.walk.support[i])
      hposFin).trans R.support_getElem_zero
  obtain ⟨parent, hparent, hinitial⟩ :=
    hL.source_subset_initialSet_limitWarp hsource
  have hxParent : R.walk.support[S.position] ∈ parent.support := by
    rw [hxStart, ← hinitial]
    exact parent.initial_mem_support
  obtain ⟨Q, hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      (ReducedInput L hL) C hparent hxParent
  have hxInitial : Q.path.initial = R.walk.support[S.position] := by
    have hparentInitQ : Q.parent.initial ∈ Q.path.support := by
      simpa only [hQparent, hinitial, hxStart] using hxQ
    calc
      Q.path.initial = Q.parent.initial :=
        splitGroundedRelevant_fragment_initial_eq_parent_initial_of_mem
          hparentInitQ
      _ = parent.initial := congrArg DirectedPath.Path.initial hQparent
      _ = R.walk.support[S.position] := by rw [hinitial, hxStart]
  let E : GroundingRelaxedEscape.RelaxedEscape
      (ReducedInput L hL) C R.walk.support[S.position] :=
    { route := S.suffix
      start_eq := Or.inl S.suffix_start
      target := S.suffix_target
      avoids := S.suffix_avoids
      old_not_mem := old_not_mem_cut_of_reduced_avoids
        L hL C R havoid S.position }
  have hQescape : Q.MeetsEscape (ReducedInput L hL) C :=
    ⟨R.walk.support[S.position], hxQ, ⟨E⟩⟩
  have hQReduced : Q ∈ L.splitGroundedRelevantG0 hL C :=
    L.splitGrounded_fragment_meeting_escape_mem_relevantG0
      hL C hC Q hQfragment hQescape
  have hblockBefore : GroundingCut.BeforeEq Q.path
      (GroundingCut.blockingPoint (ReducedInput L hL) C Q)
      R.walk.support[S.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      (ReducedInput L hL) C Q hQescape hxQ ⟨E⟩
  have hinitialBefore : GroundingCut.BeforeEq Q.path
      R.walk.support[S.position]
      (GroundingCut.blockingPoint (ReducedInput L hL) C Q) := by
    rw [← hxInitial]
    exact GroundingFragmentWarp.initial_beforeEq_of_mem
      (GroundingCut.blockingPoint_mem_support
        (ReducedInput L hL) C Q hQReduced.1.2)
  have hblockEq : GroundingCut.blockingPoint
      (ReducedInput L hL) C Q = R.walk.support[S.position] :=
    GroundingCutDecoder.beforeEq_antisymm hblockBefore hinitialBefore
  have hxBB : R.walk.support[S.position] ∈ L.splitGroundedRelevantBB hL C :=
    L.splitGroundedRelevantBL_subset_BB hL C ⟨Q, hQReduced, hblockEq⟩
  exact Set.disjoint_left.1 havoid
    (List.getElem_mem S.position.2) hxBB

private theorem exists_strictlyEarlier_escapeSuffixState
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL))
    (hC : Popular.IsSeparator (ReducedInput L hL).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hroof : R.support ⊆ (ReducedInput L hL).roofRegion)
    (havoid : Gamma.Avoids R (L.splitGroundedRelevantBB hL C))
    (S : GroundingFiniteDescent.EscapeSuffixState
      (ReducedInput L hL) C R) :
    ∃ T : GroundingFiniteDescent.EscapeSuffixState
        (ReducedInput L hL) C R,
      T.position.1 < S.position.1 := by
  have hi : 0 < S.position.1 := Nat.pos_of_ne_zero
    (escapeSuffixState_position_ne_zero L hL C hC R hsource havoid S)
  obtain ⟨J⟩ := exists_splitGroundedRelevantEarlierLadderContact
    L hL R hsource S.position hi
  obtain ⟨E⟩ := splitGroundedRelevant_relaxedEscape_of_offLadder_interval
    L hL C hC R J.position S.position J.lt_current
      (fun m _hm ↦ old_not_mem_cut_of_reduced_avoids L hL C R havoid m)
      (J.open_offLadder hroof)
      (Or.inr ⟨S.fragment.parent, S.fragment.parent_mem,
        S.fragment.support_subset S.contact_mem⟩)
      S.suffix S.suffix_start S.suffix_target S.suffix_avoids
  obtain ⟨parent, hparent, hxParent⟩ := J.mem_ladder
  obtain ⟨Q, _hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      (ReducedInput L hL) C hparent hxParent
  have hQescape : Q.MeetsEscape (ReducedInput L hL) C :=
    ⟨R.walk.support[J.position], hxQ, ⟨E⟩⟩
  have hQReduced : Q ∈ L.splitGroundedRelevantG0 hL C :=
    L.splitGrounded_fragment_meeting_escape_mem_relevantG0
      hL C hC Q hQfragment hQescape
  have hQLegacy : Q ∈ GroundingCut.G0 (ReducedInput L hL) C :=
    L.splitGroundedRelevantG0_subset_legacyG0 hL C hQReduced
  let b := GroundingCut.blockingPoint (ReducedInput L hL) C Q
  have hbQ : b ∈ Q.path.support :=
    GroundingCut.blockingPoint_mem_support
      (ReducedInput L hL) C Q hQReduced.1.2
  have hbEscape : b ∈ (ReducedInput L hL).escapeRegion C :=
    GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      (ReducedInput L hL) C Q hQescape
  have hbeforeEq : GroundingCut.BeforeEq Q.path b
      R.walk.support[J.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      (ReducedInput L hL) C Q hQescape hxQ ⟨E⟩
  by_cases hbeq : b = R.walk.support[J.position]
  · have hxBB : R.walk.support[J.position] ∈ L.splitGroundedRelevantBB hL C :=
      L.splitGroundedRelevantBL_subset_BB hL C ⟨Q, hQReduced, hbeq⟩
    exact False.elim (Set.disjoint_left.1 havoid
      (List.getElem_mem J.position.2) hxBB)
  · obtain ⟨Eb⟩ := hbEscape
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ :=
      GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
        (ReducedInput L hL) C Q hQfragment ⟨hbeforeEq, hbeq⟩
        (old_not_mem_cut_of_reduced_avoids
          L hL C R havoid J.position) Eb
    let T : GroundingFiniteDescent.EscapeSuffixState
        (ReducedInput L hL) C R :=
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

/-- The genuine finite descent decoder for the source-correct filtered
boundary. -/
theorem splitGroundedRelevantFiniteDescentDecoder
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL))
    (hC : Popular.IsSeparator (ReducedInput L hL).lambda C) :
    SplitGroundedRelevantFiniteDescentDecoder L hL C := by
  intro R hsource hterminal havoid
  have hmeet : R.walk.Meets (ReducedInput L hL).terminalCut :=
    ⟨R.finish, R.finish_mem_support, hterminal⟩
  let Q : FinitePath Gamma.graph :=
    R.firstHit (ReducedInput L hL).terminalCut hmeet
  have hQsource : Q.start ∈ Gamma.source := hsource
  have hQterminal : Q.finish ∈ (ReducedInput L hL).terminalCut :=
    R.firstHit_finish_mem (ReducedInput L hL).terminalCut hmeet
  have hQavoid : Gamma.Avoids Q (L.splitGroundedRelevantBB hL C) :=
    firstHit_avoids L hL C R havoid hmeet
  have hQroof : Q.support ⊆ (ReducedInput L hL).roofRegion := by
    apply support_subset_roofRegion_of_no_terminal_before
      L hL Q hQsource hQterminal
    intro x hx
    exact R.firstHit_no_mem_before (ReducedInput L hL).terminalCut hmeet hx
  obtain ⟨seed, _⟩ :=
    exists_initialEscapeSuffixState L hL C Q hQterminal hQavoid
  let D : GroundingFiniteDescent.LastFragmentDescentSystem
      (ReducedInput L hL) C Q :=
    { seed := seed
      resolve := fun S ↦ Or.inr
        (exists_strictlyEarlier_escapeSuffixState
          L hL C hC Q hQsource hQroof hQavoid S) }
  exact D.exists_avoiding_source_target_path

/-- Source-correct split Assertion 8.18. -/
theorem splitGroundedRelevantAssertion8_18
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL))
    (hC : Popular.IsSeparator (ReducedInput L hL).lambda C) :
    Popular.IsSeparator Gamma (L.splitGroundedRelevantBB hL C) := by
  apply PopularSwitching.isSeparator_of_meets_paths_to_separator
    (splitGroundedPopularAuxiliary_terminalCut_isSeparator L hL)
  intro R hsource hcut
  by_contra hnotMeet
  have havoid : Gamma.Avoids R (L.splitGroundedRelevantBB hL C) :=
    (Gamma.avoids_iff_not_meets R (L.splitGroundedRelevantBB hL C)).2 hnotMeet
  obtain ⟨q, hqsource, hqtarget, hqavoid⟩ :=
    splitGroundedRelevantFiniteDescentDecoder L hL C hC
      R hsource hcut havoid
  exact PopularAuxiliary.Input.no_avoiding_source_target_path
    (ReducedInput L hL).lambda C hC q hqsource hqtarget hqavoid

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.splitGroundedRelevantFiniteDescentDecoder
#print axioms Erdos599.DWeb.KappaLadder.splitGroundedRelevantAssertion8_18
