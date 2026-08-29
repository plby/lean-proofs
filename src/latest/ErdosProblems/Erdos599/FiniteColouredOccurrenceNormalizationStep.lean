/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceNormalizationForward

/-!
# A genuine fixed-word normalization step

At a new reference contact, the forward fragment constructed in
`FiniteColouredOccurrenceNormalizationForward` determines an incoming edge
of the fixed removed relation.  The full-lower anchored interval choice then
constructs the fresh backward fragment.  This file appends both fragments
and rebuilds the complete fixed-prefix state, including the interval
invariant on every reference owner.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- A strict constructed successor, with the literal occurrence-word prefix
certificate retained for the eventual finite-branching tree. -/
structure FixedSafePrefixSuccessor
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total) where
  next : FixedSafePrefixState total
  forward : FixedNextForward S
  forward_contact : forward.path.finish ∈ Gamma.vertexSet Y \
    SwitchingCore.RelationalInterval.removedInterior S.word.backwardEdges
  referenceOwner : FinitePath Gamma.graph
  referenceOwner_mem : (Sum.inl referenceOwner : Gamma.DPath) ∈ Y
  backward : FullAnchoredBackwardChoice referenceOwner total.backwardEdges
    S.word.backwardEdges forward.path.finish
  literal_extension :
    ∃ (hforward : forward.path.edgeSet ⊆ familyEdges W)
      (hbackward : backward.extension.edgeSet ⊆ familyEdges Y)
      (hjoin :
        (S.word.appendForwardPath forward.path forward.join hforward
          forward.fresh).vertex
            (Fin.last (S.word.appendForwardPath forward.path forward.join
              hforward forward.fresh).length) = backward.extension.finish)
      (hfresh : Disjoint backward.extension.edgeSet
        (S.word.appendForwardPath forward.path forward.join hforward
          forward.fresh).backwardEdges),
      next.word =
        (S.word.appendForwardPath forward.path forward.join hforward
          forward.fresh).appendBackwardPath backward.extension hjoin
            hbackward hfresh
  next_forwardEdges : next.word.forwardEdges =
    S.word.forwardEdges ∪ forward.path.edgeSet
  next_backwardEdges : next.word.backwardEdges =
    S.word.backwardEdges ∪ backward.extension.edgeSet
  next_vertexSet : next.word.vertexSet =
    S.word.vertexSet ∪ forward.path.support ∪ backward.extension.support
  next_length : next.word.length = S.word.length +
    forward.path.walk.length + backward.extension.walk.length
  next_last : next.word.vertex (Fin.last next.word.length) =
    backward.extension.start
  embedding : Prefix (S.word) (next.word)
  length_lt : (S.word).length < (next.word).length

/-- The literal forward-then-backward append is safe under the contact-step
hypotheses.  This is the exact-word form of
`exists_forward_backward_extension`; it is useful when a later construction
must remember occurrence order, not merely the two edge sets. -/
theorem IsIntervalSafe.appendForwardBackwardPath
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (p : FinitePath Gamma.graph)
    (hjoin : Q.vertex (Fin.last Q.length) = p.start)
    (hp : p.edgeSet ⊆ familyEdges W)
    (hfresh : Disjoint p.edgeSet Q.forwardEdges)
    (hstart : p.start ∈ Gamma.vertexSet Y → HasOutgoing Q.backwardEdges p.start)
    (hcontact : p.support ∩ Gamma.vertexSet Y ⊆
      {p.start, p.finish} ∪ removedInterior Q.backwardEdges)
    (owner : Gamma.DPath) (howner : owner ∈ Y)
    (old r : FinitePath Gamma.graph)
    (hold : old.IsSubpathOf owner) (hr : r.IsSubpathOf owner)
    (holdjoin : old.finish = r.start)
    (holdR : Q.backwardEdges ∩ owner.edgeSet = old.edgeSet)
    (hrend : r.finish = p.finish) (hrne : r.start ≠ r.finish) :
    let QF := Q.appendForwardPath p hjoin hp hfresh
    let hrY : r.edgeSet ⊆ familyEdges Y := fun e he ↦ by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨owner, howner, hr.2 he⟩
    let hRjoin : QF.vertex (Fin.last QF.length) = r.finish := by
      rw [Q.appendForwardPath_last p hjoin hp hfresh, hrend]
    let hRfresh : Disjoint r.edgeSet QF.backwardEdges := by
      rw [Q.appendForwardPath_backwardEdges p hjoin hp hfresh]
      exact (backward_interval_extension hY
        Q.backwardEdges_subset_familyEdges hQ.intervals owner howner old r
        hold hr holdjoin holdR).1
    (QF.appendBackwardPath r hRjoin hrY hRfresh).IsIntervalSafe := by
  dsimp only
  obtain ⟨hrfresh, _hRsub, hintervals⟩ := backward_interval_extension hY
    Q.backwardEdges_subset_familyEdges hQ.intervals owner howner old r
      hold hr holdjoin holdR
  let QF := Q.appendForwardPath p hjoin hp hfresh
  have hQFback : QF.backwardEdges = Q.backwardEdges :=
    Q.appendForwardPath_backwardEdges p hjoin hp hfresh
  have hQFforward : QF.forwardEdges = Q.forwardEdges ∪ p.edgeSet :=
    Q.appendForwardPath_forwardEdges p hjoin hp hfresh
  let hrY : r.edgeSet ⊆ familyEdges Y := fun e he ↦ by
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨owner, howner, hr.2 he⟩
  have hRjoin : QF.vertex (Fin.last QF.length) = r.finish := by
    rw [show QF.vertex (Fin.last QF.length) = p.finish from
      Q.appendForwardPath_last p hjoin hp hfresh, hrend]
  have hRfresh : Disjoint r.edgeSet QF.backwardEdges := by
    rwa [hQFback]
  let Q' := QF.appendBackwardPath r hRjoin hrY hRfresh
  have hQ'forward : Q'.forwardEdges = Q.forwardEdges ∪ p.edgeSet := by
    rw [show Q'.forwardEdges = QF.forwardEdges from
      QF.appendBackwardPath_forwardEdges r hRjoin hrY hRfresh, hQFforward]
  have hQ'back : Q'.backwardEdges = Q.backwardEdges ∪ r.edgeSet := by
    rw [show Q'.backwardEdges = QF.backwardEdges ∪ r.edgeSet from
      QF.appendBackwardPath_backwardEdges r hRjoin hrY hRfresh, hQFback]
  have hfinish : HasIncoming r.edgeSet p.finish := by
    obtain ⟨x, hx⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start r
      r.finish_mem_support hrne.symm
    exact ⟨x, hrend ▸ hx⟩
  have hnewInc := new_forward_conflicting_edges_removed hY
    Q.backwardEdges_subset_familyEdges hrY p hstart (fun _ ↦ hfinish) hcontact
  have hnewPure : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y :=
    new_forward_endpoint_pure hY hYfin Q.backwardEdges_subset_familyEdges hrY
      p hstart (fun _ ↦ hfinish) hcontact
  constructor
  · intro a b x hax hbx
    rw [hQ'forward] at hax
    rw [hQ'back]
    exact hax.elim (fun h ↦ Or.inl (hQ.incoming_removed h hbx))
      (fun h ↦ hnewInc.1 h hbx)
  · intro x a b hxa hxb
    rw [hQ'forward] at hxa
    rw [hQ'back]
    exact hxa.elim (fun h ↦ Or.inl (hQ.outgoing_removed h hxb))
      (fun h ↦ hnewInc.2 h hxb)
  · intro q hqY
    rw [hQ'back]
    exact hintervals q hqY
  · intro x y hxy
    rw [hQ'forward] at hxy
    exact hxy.elim (fun h ↦ hQ.endpoint_pure h) (fun h ↦ hnewPure h)

/-- A normalized finite word which has reached the fixed total terminal. -/
structure FixedNormalizedTerminal
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total) where
  word : FiniteColouredOccurrenceWord W Y
  safe : word.IsIntervalSafe
  first_eq : word.vertex 0 = total.vertex 0
  last_eq : word.vertex (Fin.last word.length) =
    total.vertex (Fin.last total.length)
  forward_subset : word.forwardEdges ⊆ total.forwardEdges
  backward_subset : word.backwardEdges ⊆ total.backwardEdges
  embedding : Prefix (S.word) word
  length_le : (S.word).length ≤ word.length

/-- The nontrivial final forward suffix, retained literally rather than
forgotten behind the terminal word's edge-set equations. -/
structure FixedNormalizedTerminalExtension
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total) where
  terminal : FixedNormalizedTerminal S
  path : FinitePath Gamma.graph
  join : S.word.vertex (Fin.last S.word.length) = path.start
  nontrivial : path.start ≠ path.finish
  edges_forward : path.edgeSet ⊆ familyEdges W
  fresh : Disjoint path.edgeSet S.word.forwardEdges
  word_eq : terminal.word =
    S.word.appendForwardPath path join edges_forward fresh

/-- One genuine normalization move either finishes at the fixed terminal or
produces a longer full-anchored prefix state. -/
inductive FixedNormalizationStep
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total) where
  | terminal : FixedNormalizedTerminalExtension S → FixedNormalizationStep S
  | successor : FixedSafePrefixSuccessor S → FixedNormalizationStep S

/-- The current endpoint starts the next forward fragment with the removed
reference incidence required by the contact-step constructor. -/
private theorem FixedSafePrefixState.forward_start_removed
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    {p : FinitePath Gamma.graph}
    (hjoin : S.word.vertex (Fin.last S.word.length) = p.start) :
    p.start ∈ Gamma.vertexSet Y →
      HasOutgoing S.word.backwardEdges p.start := by
  intro hpY
  rcases S.phase with hzero | hback
  · apply False.elim
    apply hfirstOff
    have hpStart : p.start = total.vertex 0 := hjoin.symm.trans hzero.2
    simpa only [hpStart] using hpY
  · simpa only [hjoin] using hback

/-- A contact outcome produces the next full-lower-anchored safe state.
Every new forward/backward edge remains in the one fixed total word. -/
theorem FixedSafePrefixState.exists_successor_of_contact
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (htotal : total.IsIntervalSafe)
    (S : FixedSafePrefixState total)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (F : FixedNextForward S)
    (hcontact : F.path.finish ∈ Gamma.vertexSet Y \
      removedInterior S.word.backwardEdges) :
    Nonempty (FixedSafePrefixSuccessor S) := by
  classical
  obtain ⟨ownerPath, hownerY, hwOwner⟩ := hcontact.1
  obtain ⟨owner, rfl⟩ := hYfin hownerY
  have hlastEdge : HasIncoming F.path.edgeSet F.path.finish :=
    FinitePath.exists_incoming_edge_of_mem_support_of_ne_start F.path
      F.path.finish_mem_support F.nontrivial.symm
  obtain ⟨z, hzPath⟩ := hlastEdge
  have hzTotalF : (z, F.path.finish) ∈ total.forwardEdges :=
    F.edges_total hzPath
  have hfinishNotInitial : F.path.finish ∉ Gamma.initialSet Y :=
    (htotal.endpoint_pure hzTotalF).1
  have hfinishNeStart : F.path.finish ≠ owner.start := by
    intro heq
    apply hfinishNotInitial
    exact ⟨.inl owner, hownerY, heq.symm⟩
  obtain ⟨y, _hyOrder, hyOwner⟩ :=
    ColouredSafeReverseReachability.exists_predecessor_occurrence_edge
      owner hwOwner hfinishNeStart
  have hyY : (y, F.path.finish) ∈ familyEdges Y := by
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨.inl owner, hownerY, hyOwner⟩
  have hyTotalR : (y, F.path.finish) ∈ total.backwardEdges :=
    htotal.incoming_removed hzTotalF hyY
  obtain ⟨K⟩ := exists_fullAnchoredBackwardChoice
    (htotal.intervals (.inl owner) hownerY) (S.intervals owner hownerY)
    ⟨hyTotalR, hyOwner⟩ hcontact.2 F.incoming_unused
  have hpathW : F.path.edgeSet ⊆ familyEdges W :=
    F.edges_total.trans total.forwardEdges_subset_familyEdges
  have hpathY : K.extension.edgeSet ⊆ familyEdges Y :=
    K.extension_edges_total.trans total.backwardEdges_subset_familyEdges
  have hstart := S.forward_start_removed hfirstOff F.join
  let QF := S.word.appendForwardPath F.path F.join hpathW F.fresh
  have hRjoin : QF.vertex (Fin.last QF.length) = K.extension.finish := by
    rw [show QF.vertex (Fin.last QF.length) = F.path.finish from
      S.word.appendForwardPath_last F.path F.join hpathW F.fresh,
      K.extension_finish]
  have hRfresh : Disjoint K.extension.edgeSet QF.backwardEdges := by
    rw [S.word.appendForwardPath_backwardEdges F.path F.join hpathW F.fresh]
    exact K.fresh
  let Q' := QF.appendBackwardPath K.extension hRjoin hpathY hRfresh
  have hQ'safe : Q'.IsIntervalSafe := by
    exact S.safe.appendForwardBackwardPath hY hYfin F.path F.join hpathW
      F.fresh hstart F.contact_geometry (.inl owner) hownerY K.old K.extension
      K.old_isSubpath_owner K.extension_isSubpath_owner K.join
      K.prefix_removed_eq K.extension_finish K.extension_nontrivial
  have hQ'first : Q'.vertex 0 = S.word.vertex 0 := by
    dsimp only [Q']
    rw [QF.appendBackwardPath_first K.extension hRjoin hpathY hRfresh]
    exact S.word.appendForwardPath_first F.path F.join hpathW F.fresh
  have hQ'last : Q'.vertex (Fin.last Q'.length) = K.extension.start := by
    exact QF.appendBackwardPath_last K.extension hRjoin hpathY hRfresh
  have hQ'length : Q'.length = S.word.length + F.path.walk.length +
      K.extension.walk.length := by
    dsimp only [Q', QF]
    simp only [appendBackwardPath_length, appendForwardPath_length]
  have hQ'vertices : Q'.vertexSet = S.word.vertexSet ∪ F.path.support ∪
      K.extension.support := by
    dsimp only [Q']
    rw [QF.appendBackwardPath_vertexSet K.extension hRjoin hpathY hRfresh]
    dsimp only [QF]
    rw [S.word.appendForwardPath_vertexSet F.path F.join hpathW F.fresh]
  have hQ'forward : Q'.forwardEdges = S.word.forwardEdges ∪
      F.path.edgeSet := by
    dsimp only [Q']
    rw [QF.appendBackwardPath_forwardEdges K.extension hRjoin hpathY hRfresh]
    exact S.word.appendForwardPath_forwardEdges F.path F.join hpathW F.fresh
  have hQ'backward : Q'.backwardEdges = S.word.backwardEdges ∪
      K.extension.edgeSet := by
    dsimp only [Q']
    rw [QF.appendBackwardPath_backwardEdges K.extension hRjoin hpathY hRfresh,
      S.word.appendForwardPath_backwardEdges F.path F.join hpathW F.fresh]
  have hprefix : S.word.Prefix Q' :=
    (S.word.prefix_appendForwardPath F.path F.join hpathW F.fresh).trans
      (QF.prefix_appendBackwardPath K.extension hRjoin hpathY hRfresh)
  have hforwardSub : Q'.forwardEdges ⊆ total.forwardEdges := by
    rw [hQ'forward]
    exact Set.union_subset S.forward_subset F.edges_total
  have hbackwardSub : Q'.backwardEdges ⊆ total.backwardEdges := by
    rw [hQ'backward]
    exact Set.union_subset S.backward_subset K.extension_edges_total
  have hfinishIncomingNew : HasIncoming Q'.forwardEdges F.path.finish := by
    refine ⟨z, ?_⟩
    rw [hQ'forward]
    exact Or.inr hzPath
  have hupdated := K.exists_updatedPrior hfinishIncomingNew
  have hextDisjoint (q : FinitePath Gamma.graph)
      (hqY : (Sum.inl q : Gamma.DPath) ∈ Y) (hne : q ≠ owner) :
      Disjoint K.extension.edgeSet q.edgeSet := by
    apply Set.disjoint_left.2
    intro e heK heq
    have heOwner := K.extension_isSubpath_owner.2 heK
    have hxOwner := owner.edgeSet_subset_support_prod heOwner |>.1
    have hxq := q.edgeSet_subset_support_prod heq |>.1
    have hEq : (Sum.inl owner : Gamma.DPath) = .inl q :=
      DWeb.IsWarp.eq_of_mem_support hY hownerY hqY hxOwner hxq
    exact hne (Sum.inl.inj hEq).symm
  have hintervals (q : FinitePath Gamma.graph)
      (hqY : (Sum.inl q : Gamma.DPath) ∈ Y) :
      Q'.backwardEdges ∩ q.edgeSet = ∅ ∨
        Nonempty (FullAnchoredPriorInterval q total.backwardEdges
          Q'.backwardEdges Q'.forwardEdges) := by
    by_cases hq : q = owner
    · subst q
      right
      simpa only [hQ'backward] using hupdated
    · have hdisj := hextDisjoint q hqY hq
      have hextInter : K.extension.edgeSet ∩ q.edgeSet = ∅ :=
        by
          ext e
          constructor
          · rintro ⟨heK, heq⟩
            exact False.elim (Set.disjoint_left.1 hdisj heK heq)
          · simp
      have hbackInter : Q'.backwardEdges ∩ q.edgeSet =
          S.word.backwardEdges ∩ q.edgeSet := by
        rw [hQ'backward, Set.union_inter_distrib_right, hextInter,
          Set.union_empty]
      rcases S.intervals q hqY with hempty | hprior
      · exact Or.inl (hbackInter.trans hempty)
      · right
        let A := hprior.some
        refine ⟨{
          full := A.full
          prior := A.prior
          full_isSubpath := A.full_isSubpath
          prior_isSubpath_full := A.prior_isSubpath_full
          total_removed_eq := A.total_removed_eq
          prefix_removed_eq := hbackInter.trans A.prefix_removed_eq
          same_start := A.same_start
          finish_incoming := ?_ }⟩
        obtain ⟨x, hx⟩ := A.finish_incoming
        exact ⟨x, by rw [hQ'forward]; exact Or.inl hx⟩
  have hphase : HasOutgoing Q'.backwardEdges
      (Q'.vertex (Fin.last Q'.length)) := by
    obtain ⟨x, hx⟩ :=
      FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        K.extension K.extension.start_mem_support K.extension_nontrivial
    refine ⟨x, ?_⟩
    rw [hQ'last, hQ'backward]
    exact Or.inr hx
  let S' : FixedSafePrefixState total := {
    word := Q'
    safe := hQ'safe
    first_eq := hQ'first.trans S.first_eq
    forward_subset := hforwardSub
    backward_subset := hbackwardSub
    phase := Or.inr hphase
    intervals := hintervals }
  refine ⟨{
    next := S'
    forward := F
    forward_contact := hcontact
    referenceOwner := owner
    referenceOwner_mem := hownerY
    backward := K
    literal_extension := ⟨hpathW, hpathY, hRjoin, hRfresh, rfl⟩
    next_forwardEdges := hQ'forward
    next_backwardEdges := hQ'backward
    next_vertexSet := hQ'vertices
    next_length := hQ'length
    next_last := hQ'last
    embedding := hprefix
    length_lt := ?_ }⟩
  dsimp only [S']
  rw [hQ'length]
  have hpPositive : 0 < F.path.walk.length := by
    exact Nat.pos_of_ne_zero (fun h ↦
      F.nontrivial (Walk.endpoints_eq_of_length_eq_zero F.path.walk h))
  omega

/-- A terminal outcome appends its literal forward suffix and gives a safe
normalized word ending at the same fixed target. -/
theorem FixedSafePrefixState.exists_terminalExtension_of_forward
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (F : FixedNextForward S)
    (hterminal : F.path.finish = total.vertex (Fin.last total.length)) :
    Nonempty (FixedNormalizedTerminalExtension S) := by
  let hp : F.path.edgeSet ⊆ familyEdges W :=
    F.edges_total.trans total.forwardEdges_subset_familyEdges
  have hfinishOff : F.path.finish ∉ Gamma.vertexSet Y := by
    simpa only [hterminal] using hlastOff
  have hstart := S.forward_start_removed hfirstOff F.join
  let Q' := S.word.appendForwardPath F.path F.join hp F.fresh
  have hsafe : Q'.IsIntervalSafe :=
    S.safe.appendForwardPath_of_terminal_offReference hY hYfin F.path
      F.join hp F.fresh hfinishOff hstart F.contact_geometry
  refine ⟨{
    terminal := {
      word := Q'
      safe := hsafe
      first_eq := (S.word.appendForwardPath_first F.path F.join hp F.fresh).trans
        S.first_eq
      last_eq := (S.word.appendForwardPath_last F.path F.join hp F.fresh).trans
        hterminal
      forward_subset := ?_
      backward_subset := ?_
      embedding := S.word.prefix_appendForwardPath F.path F.join hp F.fresh
      length_le := ?_ }
    path := F.path
    join := F.join
    nontrivial := F.nontrivial
    edges_forward := hp
    fresh := F.fresh
    word_eq := rfl }⟩
  · rw [S.word.appendForwardPath_forwardEdges F.path F.join hp F.fresh]
    exact Set.union_subset S.forward_subset F.edges_total
  · rw [S.word.appendForwardPath_backwardEdges F.path F.join hp F.fresh]
    exact S.backward_subset
  · rw [S.word.appendForwardPath_length F.path F.join hp F.fresh]
    have hpPositive : 0 < F.path.walk.length := by
      exact Nat.pos_of_ne_zero (fun h ↦
        F.nontrivial (Walk.endpoints_eq_of_length_eq_zero F.path.walk h))
    omega

/-- Compatibility wrapper retaining the historical result type. -/
theorem FixedSafePrefixState.exists_terminal_of_forward
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (F : FixedNextForward S)
    (hterminal : F.path.finish = total.vertex (Fin.last total.length)) :
    Nonempty (FixedNormalizedTerminal S) := by
  obtain ⟨E⟩ := S.exists_terminalExtension_of_forward hY hYfin
    hfirstOff hlastOff F hterminal
  exact ⟨E.terminal⟩

/-- The complete local normalization step is constructed without a next-step
oracle: balance selects the forward suffix, and the contact case selects the
anchored backward interval. -/
theorem FixedSafePrefixState.exists_normalizationStep
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (htotal : total.IsIntervalSafe)
    (S : FixedSafePrefixState total)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (hcurrentNe : S.word.vertex (Fin.last S.word.length) ≠
      total.vertex (Fin.last total.length)) :
    Nonempty (FixedNormalizationStep S) := by
  obtain ⟨F⟩ := S.exists_fixedNextForward hW hY hWfin hYfin hfirst
    hfirstOff hlast hlastOff hcurrentNe
  rcases F.outcome with hterminal | hcontact
  · obtain ⟨T⟩ := S.exists_terminalExtension_of_forward hY hYfin
      hfirstOff hlastOff
      F hterminal
    exact ⟨.terminal T⟩
  · obtain ⟨N⟩ := S.exists_successor_of_contact hW hY hYfin htotal
      hfirstOff F hcontact.1
    exact ⟨.successor N⟩

#print axioms FixedSafePrefixState.exists_successor_of_contact
#print axioms FixedSafePrefixState.exists_terminalExtension_of_forward
#print axioms FixedSafePrefixState.exists_terminal_of_forward
#print axioms FixedSafePrefixState.exists_normalizationStep

end Erdos599.Alternating.FiniteColouredOccurrenceWord
