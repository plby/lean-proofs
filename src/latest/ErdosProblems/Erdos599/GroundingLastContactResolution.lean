/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion817
import ErdosProblems.Erdos599.GroundingFragmentWarp
import ErdosProblems.Erdos599.GroundingFragmentPartition
import ErdosProblems.Erdos599.GroundingPointwiseSwitch

/-!
# The last ladder contact in the finite grounding descent

This file supplies the literal decreasing step in Assertion 8.18.  Given an
escaping suffix based at a noninitial position of an ambient finite path, we
choose the last earlier vertex which lies on the limiting ladder.  All
vertices in the intervening open interval are therefore `offLadder`; the
forward-corridor compiler turns the old suffix into a relaxed escape at the
chosen contact.  Assertion 8.17 retains the fragment through that contact.
Its first escaping point is either the contact itself, contradicting
avoidance of `BL`, or lies strictly earlier on the fragment and yields a new
escape-suffix state at a strictly smaller ambient position.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace GroundingLastContactResolution

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

abbrev Aux (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :=
  L.popularAuxiliaryInput hlegal

abbrev LV (L : Gamma.KappaLadder kappa) (_hlegal : L.IsLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-- Legality covers every original source by the initial vertex of a
grounded parent in the limiting ladder. -/
theorem source_has_grounded_ladder_parent
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {x : V} (hx : x ∈ Gamma.source) :
    ∃ p ∈ (Aux L hlegal).ladder.paths,
      p.initial = x ∧ p.initial ∈ Gamma.source := by
  have hlimitOrd : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hlegal.regular.aleph0_le
  obtain ⟨D, hstage, hlimit⟩ :=
    hlegal.limitStages (Ladder.finalStage kappa) hlimitOrd
  let i : Set.Iio kappa.ord := ⟨0, hlegal.regular.ord_pos⟩
  have hxi : x ∈ Gamma.initialSet (D.stage i) := by
    rw [hstage i]
    change x ∈ Gamma.initialSet (L.accumulated (Ladder.zeroStage kappa))
    rw [hlegal.initialStage, Gamma.initialSet_trivialWave]
    exact hx
  have hxInitial : x ∈ Gamma.initialSet L.limitWarp := by
    change x ∈ Gamma.initialSet (L.accumulated (Ladder.finalStage kappa))
    rw [hlimit, D.initialSet_limitPaths Gamma]
    exact Set.mem_iUnion.2 ⟨i, hxi⟩
  obtain ⟨p, hp, hpx⟩ := hxInitial
  exact ⟨p, hp, hpx, hpx ▸ hx⟩

/-- A last ladder contact strictly before the displayed current position.
The open interval after it contains no ladder vertex. -/
structure EarlierLadderContact
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (R : FinitePath Gamma.graph)
    (i : Fin R.walk.support.length) where
  position : Fin R.walk.support.length
  lt_current : position.1 < i.1
  mem_ladder : R.walk.support[position] ∈
    Gamma.vertexSet (Aux L hlegal).ladder.paths
  open_not_ladder : ∀ k : Fin R.walk.support.length,
    position.1 < k.1 → k.1 < i.1 →
      R.walk.support[k] ∉ Gamma.vertexSet (Aux L hlegal).ladder.paths

/-- Legality makes position zero a ladder contact: the ambient path starts
at an original source, and every original source is the initial point of a
parent in the limiting ladder. -/
theorem zero_mem_ladder
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source) :
    R.walk.support[0] ∈ Gamma.vertexSet (Aux L hlegal).ladder.paths := by
  obtain ⟨parent, hparent, hinitial, _hground⟩ :=
    source_has_grounded_ladder_parent L hlegal hsource
  refine ⟨parent, hparent, ?_⟩
  rw [R.support_getElem_zero, ← hinitial]
  exact parent.initial_mem_support

/-- Choose the last ladder contact strictly before a noninitial position.
This is the finite maximality operation used by the source proof. -/
theorem exists_last_earlier_ladder_contact
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (i : Fin R.walk.support.length) (hi : 0 < i.1) :
    Nonempty (EarlierLadderContact L hlegal R i) := by
  classical
  let contacts : Finset (Fin R.walk.support.length) :=
    Finset.univ.filter fun j ↦
      j.1 < i.1 ∧ R.walk.support[j] ∈
        Gamma.vertexSet (Aux L hlegal).ladder.paths
  have hzero : (⟨0, R.support_length_pos⟩ :
      Fin R.walk.support.length) ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi, zero_mem_ladder L hlegal R hsource⟩
  let j : Fin R.walk.support.length := contacts.max' ⟨_, hzero⟩
  have hjmem : j ∈ contacts := Finset.max'_mem contacts ⟨_, hzero⟩
  have hj : j.1 < i.1 ∧ R.walk.support[j] ∈
      Gamma.vertexSet (Aux L hlegal).ladder.paths := by
    simpa only [contacts, Finset.mem_filter, Finset.mem_univ,
      true_and] using hjmem
  refine ⟨{
    position := j
    lt_current := hj.1
    mem_ladder := hj.2
    open_not_ladder := ?_ }⟩
  intro m hjm hmi hmLadder
  have hmmem : m ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hmi, hmLadder⟩
  have hmj : m ≤ j := Finset.le_max' contacts m hmmem
  exact (not_le_of_gt hjm) hmj

/-- If the whole ambient path lies under the terminal roof, maximality of
the last ladder contact upgrades the intervening noncontacts to the exact
`offLadder` hypothesis expected by the corridor compiler. -/
theorem EarlierLadderContact.open_offLadder
    {L : Gamma.KappaLadder kappa} {hlegal : L.IsLegal}
    {R : FinitePath Gamma.graph} {i : Fin R.walk.support.length}
    (J : EarlierLadderContact L hlegal R i)
    (hroof : R.support ⊆ (Aux L hlegal).roofRegion) :
    ∀ m : Fin R.walk.support.length,
      J.position.1 < m.1 → m.1 < i.1 →
        R.walk.support[m] ∈ (Aux L hlegal).offLadder := by
  intro m hjm hmi
  exact ⟨hroof (List.getElem_mem m.2), J.open_not_ladder m hjm hmi⟩

/-- The head of a directed edge of a finite path or ray is not that path's
initial vertex. -/
private theorem path_edge_head_ne_initial
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

/-- A fragment containing the initial vertex of its parent starts there.
Otherwise the fragment has an incoming edge at the parent initial vertex;
edge containment would make that an edge of the parent, impossible for a
directed finite path or ray. -/
theorem fragment_initial_eq_parent_initial_of_mem
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {P : (Aux L hlegal).Fragment}
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
    have hyParent : (y, P.parent.initial) ∈ P.parent.edgeSet := by
      apply P.edges_subset
      simpa only [hpath, DirectedPath.Path.edgeSet] using hy
    exact path_edge_head_ne_initial hyParent rfl
  | inr r =>
    have hinit' : P.parent.initial ∈ r.support := by
      simpa only [hpath, DirectedPath.Path.support] using hinit
    have hne'' : P.parent.initial ≠ r.initial := by
      simpa only [hpath, DirectedPath.Path.initial] using hne'
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial
        r hinit' hne''
    have hyParent : (y, P.parent.initial) ∈ P.parent.edgeSet := by
      apply P.edges_subset
      simpa only [hpath, DirectedPath.Path.edgeSet] using hy
    exact path_edge_head_ne_initial hyParent rfl

/-- The initial ambient vertex cannot support an escape-suffix state.  The
fragment through a legal ladder parent initial meets the relaxed escape
given by the state's ordinary suffix, hence is in `G0` by Assertion 8.17.
Its blocking point must equal that initial contact and so belongs to
`BL ⊆ BB`, contradicting ambient avoidance. -/
theorem escapeSuffixState_position_ne_zero
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (hC : Popular.IsSeparator (Aux L hlegal).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (havoid : Gamma.Avoids R (GroundingCut.BB (Aux L hlegal) C))
    (S : GroundingFiniteDescent.EscapeSuffixState
      (Aux L hlegal) C R) :
    S.position.1 ≠ 0 := by
  intro hpos
  have hposFin : S.position =
      (⟨0, R.support_length_pos⟩ : Fin R.walk.support.length) :=
    Fin.ext hpos
  have hxStart : R.walk.support[S.position] = R.start := by
    exact (congrArg (fun i : Fin R.walk.support.length ↦
      R.walk.support[i]) hposFin).trans R.support_getElem_zero
  obtain ⟨parent, hparent, hinitial, _hground⟩ :=
    source_has_grounded_ladder_parent L hlegal hsource
  have hxParent : R.walk.support[S.position] ∈ parent.support := by
    rw [hxStart, ← hinitial]
    exact parent.initial_mem_support
  obtain ⟨Q, hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      (Aux L hlegal) C hparent hxParent
  have hxInitial : Q.path.initial = R.walk.support[S.position] := by
    have hparentInitQ : Q.parent.initial ∈ Q.path.support := by
      simpa only [hQparent, hinitial, hxStart] using hxQ
    calc
      Q.path.initial = Q.parent.initial :=
        fragment_initial_eq_parent_initial_of_mem L hlegal hparentInitQ
      _ = parent.initial := congrArg DirectedPath.Path.initial hQparent
      _ = R.walk.support[S.position] := by rw [hinitial, hxStart]
  let E : GroundingRelaxedEscape.RelaxedEscape
      (Aux L hlegal) C R.walk.support[S.position] :=
    { route := S.suffix
      start_eq := Or.inl S.suffix_start
      target := S.suffix_target
      avoids := S.suffix_avoids
      old_not_mem := GroundingRelaxedCorridor.old_not_mem_cut_of_ambient_avoids
        (Aux L hlegal) C R havoid S.position }
  have hQescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      (Aux L hlegal) C Q := ⟨R.walk.support[S.position], hxQ, ⟨E⟩⟩
  have hQG0 : Q ∈ GroundingCut.G0 (Aux L hlegal) C :=
    GroundingAssertion817.fragment_meeting_relaxedEscape_mem_G0
      L hlegal C hC Q hQfragment hQescape
  have hblockBefore : GroundingCut.BeforeEq Q.path
      (GroundingCut.blockingPoint (Aux L hlegal) C Q)
      R.walk.support[S.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      (Aux L hlegal) C Q hQescape hxQ ⟨E⟩
  have hinitialBefore : GroundingCut.BeforeEq Q.path
      R.walk.support[S.position]
      (GroundingCut.blockingPoint (Aux L hlegal) C Q) := by
    rw [← hxInitial]
    exact GroundingFragmentWarp.initial_beforeEq_of_mem
      (GroundingCut.blockingPoint_mem_support
        (Aux L hlegal) C Q hQG0.2)
  have hblockEq :
      GroundingCut.blockingPoint (Aux L hlegal) C Q =
        R.walk.support[S.position] :=
    GroundingCutDecoder.beforeEq_antisymm hblockBefore hinitialBefore
  have hxBB : R.walk.support[S.position] ∈
      GroundingCut.BB (Aux L hlegal) C :=
    GroundingCut.BL_subset_BB (Aux L hlegal) C
      ⟨Q, hQG0, hblockEq⟩
  exact Set.disjoint_left.1 havoid
    (List.getElem_mem S.position.2) hxBB

/-- The exact recursive last-contact step.  Under the terminal-roof
invariant on the ambient path, every escape-suffix state produces another
one at a strictly smaller ambient position.  The apparent equality case
for the fragment blocking point is impossible because the ambient path
avoids `BL`. -/
theorem exists_strictlyEarlier_escapeSuffixState
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (hC : Popular.IsSeparator (Aux L hlegal).lambda C)
    (R : FinitePath Gamma.graph) (hsource : R.start ∈ Gamma.source)
    (hroof : R.support ⊆ (Aux L hlegal).roofRegion)
    (havoid : Gamma.Avoids R (GroundingCut.BB (Aux L hlegal) C))
    (S : GroundingFiniteDescent.EscapeSuffixState
      (Aux L hlegal) C R) :
    ∃ T : GroundingFiniteDescent.EscapeSuffixState
        (Aux L hlegal) C R,
      T.position.1 < S.position.1 := by
  have hi : 0 < S.position.1 :=
    Nat.pos_of_ne_zero
      (escapeSuffixState_position_ne_zero
        L hlegal C hC R hsource havoid S)
  obtain ⟨J⟩ := exists_last_earlier_ladder_contact
    L hlegal R hsource S.position hi
  obtain ⟨E⟩ :=
    GroundingRelaxedCorridor.relaxedEscape_of_offLadder_interval
      (Aux L hlegal) C hC R havoid J.position S.position
        J.lt_current (J.open_offLadder hroof)
        (Or.inr (by
          exact ⟨S.fragment.parent, S.fragment.parent_mem,
            S.fragment.support_subset S.contact_mem⟩))
        S.suffix S.suffix_start S.suffix_target S.suffix_avoids
  obtain ⟨parent, hparent, hxParent⟩ := J.mem_ladder
  obtain ⟨Q, _hQparent, hQfragment, hxQ⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      (Aux L hlegal) C hparent hxParent
  have hQescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      (Aux L hlegal) C Q :=
    ⟨R.walk.support[J.position], hxQ, ⟨E⟩⟩
  have hQG0 : Q ∈ GroundingCut.G0 (Aux L hlegal) C :=
    GroundingAssertion817.fragment_meeting_relaxedEscape_mem_G0
      L hlegal C hC Q hQfragment hQescape
  let b := GroundingCut.blockingPoint (Aux L hlegal) C Q
  have hbQ : b ∈ Q.path.support :=
    GroundingCut.blockingPoint_mem_support
      (Aux L hlegal) C Q hQG0.2
  have hbEscape : b ∈ (Aux L hlegal).escapeRegion C :=
    GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      (Aux L hlegal) C Q hQescape
  have hbeforeEq : GroundingCut.BeforeEq Q.path b
      R.walk.support[J.position] :=
    GroundingCut.blockingPoint_beforeEq_escape
      (Aux L hlegal) C Q hQescape hxQ ⟨E⟩
  by_cases hbeq : b = R.walk.support[J.position]
  · have hxBB : R.walk.support[J.position] ∈
        GroundingCut.BB (Aux L hlegal) C :=
      GroundingCut.BL_subset_BB (Aux L hlegal) C
        ⟨Q, hQG0, hbeq⟩
    exact False.elim (Set.disjoint_left.1 havoid
      (List.getElem_mem J.position.2) hxBB)
  · obtain ⟨Eb⟩ := hbEscape
    exact GroundingRelaxedCorridor.exists_strictlyEarlier_escapeSuffixState
      (Aux L hlegal) C R havoid S J.position J.lt_current Q hQG0
        hbQ ⟨hbeforeEq, hbeq⟩ Eb

end GroundingLastContactResolution
end Erdos599
