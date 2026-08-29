/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceNormalizationTree

/-!
# Normalization to an internal forward-warp endpoint

The fixed-word normalization previously followed a finite forward owner to
its terminal unless it met a new reference contact.  That unnecessarily
required the prescribed last occurrence to be a terminal of the forward
warp.  Here the forward step also stops at the first upper boundary of the
fixed total forward-edge relation.  The edge-balance identity says that such
a boundary is either the prescribed last occurrence or a new reference
contact.  Thus the complete normalization and its literal reachability in
the common local tree remain valid when the last occurrence is merely
covered by the forward warp.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Along a finite forward-warp path, the first omitted edge after a used
incoming edge gives a strict upper boundary of the used relation. -/
private theorem finitePath_exists_upperBoundary_of_not_subset
    (hW : Gamma.IsWarp W) {F : Set (V × V)}
    (hF : F ⊆ familyEdges W) (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) (hne : p.start ≠ p.finish)
    (hstart : HasOutgoing F p.start) (hnot : ¬ p.edgeSet ⊆ F) :
    ∃ x ∈ p.support, x ≠ p.start ∧ HasIncoming F x ∧
      ¬ HasOutgoing F x ∧ HasOutgoing p.edgeSet x := by
  obtain ⟨c, hac, q, hw⟩ :=
    RelationalRoof.exists_cons_of_start_ne_finish Gamma.graph.Adj p.walk hne
  have hacW : (p.start, c) ∈ familyEdges W := hp (by
    change (p.start, c) ∈ p.walk.edgeSet
    rw [hw]
    simp [Walk.edgeSet])
  obtain ⟨z, haz⟩ := hstart
  have hzc : z = c := (IsWarp.familyEdges_biUnique hW).2 (hF haz) hacW
  have hacF : (p.start, c) ∈ F := hzc ▸ haz
  have hqW : q.edgeSet ⊆ familyEdges W := by
    intro e he
    apply hp
    change e ∈ p.walk.edgeSet
    rw [hw]
    simp [Walk.edgeSet, he]
  have hqNot : ¬ q.edgeSet ⊆ F := by
    intro hsub
    apply hnot
    intro e he
    change e ∈ p.walk.edgeSet at he
    rw [hw] at he
    simp only [Walk.edgeSet_cons, Set.mem_union,
      Set.mem_singleton_iff] at he
    exact he.elim (fun h ↦ h ▸ hacF) (fun h ↦ hsub h)
  have walkBoundary : ∀ {a b : V} (q : Walk Gamma.graph a b),
      q.edgeSet ⊆ familyEdges W → HasIncoming F a →
      ¬ q.edgeSet ⊆ F →
      ∃ x ∈ q.support, HasIncoming F x ∧ ¬ HasOutgoing F x ∧
        HasOutgoing q.edgeSet x := by
    intro a b q
    induction q with
    | nil =>
        intro _ _ hnotq
        exact False.elim (hnotq (by simp [Walk.edgeSet]))
    | @cons a d b had q ih =>
        intro hqEdges hFin hnotq
        have hadW : (a, d) ∈ familyEdges W := hqEdges (by
          simp [Walk.edgeSet])
        by_cases hadF : (a, d) ∈ F
        · have htailW : q.edgeSet ⊆ familyEdges W := by
            intro e he
            exact hqEdges (by simp [Walk.edgeSet, he])
          have htailNot : ¬ q.edgeSet ⊆ F := by
            intro hsub
            apply hnotq
            intro e he
            simp only [Walk.edgeSet_cons, Set.mem_union,
              Set.mem_singleton_iff] at he
            exact he.elim (fun h ↦ h ▸ hadF) (fun h ↦ hsub h)
          obtain ⟨x, hx, hxin, hxout, hqx⟩ :=
            ih htailW ⟨a, hadF⟩ htailNot
          exact ⟨x, by simp [Walk.support, hx], hxin, hxout, by
            obtain ⟨y, hxy⟩ := hqx
            exact ⟨y, by simp [Walk.edgeSet, hxy]⟩⟩
        · have hnoOut : ¬ HasOutgoing F a := by
            rintro ⟨y, hay⟩
            have hyd : y = d :=
              (IsWarp.familyEdges_biUnique hW).2 (hF hay) hadW
            exact hadF (hyd ▸ hay)
          exact ⟨a, by simp [Walk.support], hFin, hnoOut,
            ⟨d, by simp [Walk.edgeSet]⟩⟩
  obtain ⟨x, hxq, hxin, hxout, hqx⟩ :=
    walkBoundary q hqW ⟨p.start, hacF⟩ hqNot
  have hx : x ∈ p.support := by
    change x ∈ p.walk.support
    rw [hw]
    simp [Walk.support, hxq]
  have hxne : x ≠ p.start := by
    intro hxa
    have hnodup : (p.start :: q.support).Nodup := by
      have hpath := p.isPath
      change p.walk.support.Nodup at hpath
      rw [hw] at hpath
      exact hpath
    exact (List.nodup_cons.mp hnodup).1 (hxa ▸ hxq)
  exact ⟨x, hx, hxne, hxin, hxout, by
    obtain ⟨y, hxy⟩ := hqx
    exact ⟨y, by
      change (x, y) ∈ p.walk.edgeSet
      rw [hw]
      simp [Walk.edgeSet, hxy]⟩⟩

/-- The next normalization fragment exists when the fixed last occurrence
is any forward-warp vertex outside the reference warp. -/
theorem FixedSafePrefixState.exists_fixedNextForward_of_last_mem
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (hcurrentNe : S.word.vertex (Fin.last S.word.length) ≠
      total.vertex (Fin.last total.length)) :
    Nonempty (FixedNextForward S) := by
  classical
  let s := total.vertex 0
  let t := total.vertex (Fin.last total.length)
  let a := S.word.vertex (Fin.last S.word.length)
  have htotalOut : HasOutgoing total.forwardEdges a :=
    (S.current_eq_totalFinish_or_hasTotalForward hW hY hYfin
      hfirstOff hlastOff).resolve_left hcurrentNe
  obtain ⟨b, habTotal⟩ := htotalOut
  have habW := total.forwardEdges_subset_familyEdges habTotal
  have haW : a ∈ Gamma.vertexSet W :=
    (familyEdges_subset_vertexSet_prod W habW).1
  obtain ⟨owner, hownerW, haOwner⟩ := haW
  obtain ⟨p, rfl⟩ := hWfin hownerW
  let tail := p.suffixFrom a haOwner
  have htailStart : tail.start = a := p.suffixFrom_start a haOwner
  have htailFinish : tail.finish = p.finish := p.suffixFrom_finish a haOwner
  have htailEdges : tail.edgeSet ⊆ familyEdges W := by
    intro e he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨.inl p, hownerW, p.suffixFrom_edgeSet_subset a haOwner he⟩
  have htailTerminal : tail.finish ∈ Gamma.terminalFrontier W :=
    ⟨.inl p, hownerW, by simp only [DWeb.terminal?_finite, htailFinish]⟩
  have htailNe : tail.start ≠ tail.finish := by
    intro heq
    have hnoOut : ¬ HasOutgoing (familyEdges W) tail.finish := by
      rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin] at htailTerminal
      exact htailTerminal.2
    exact hnoOut ⟨b, by
      have hfinishA : tail.finish = a := heq.symm.trans htailStart
      simpa only [hfinishA] using habW⟩
  have htailJoin : a = tail.start := htailStart.symm
  have hstartNoPrefix : ¬ HasOutgoing S.word.forwardEdges tail.start := by
    rw [htailStart]
    rcases S.phase with hzero | hback
    · simp [hzero.1, HasOutgoing]
    · exact S.safe.no_forward_outgoing_at_backward_exit hW hY hYfin
        (by simpa only [S.first_eq] using hfirstOff) hback
  have hsourceTail : S.word.forwardEdges = ∅ ∨ s ∉ tail.support := by
    rcases S.phase with hzero | hback
    · exact Or.inl hzero.1
    · right
      apply ColouredSafeReverseReachability.forward_fragment_avoids_initial
        hW hWfin hfirst tail htailEdges
      intro heq
      obtain ⟨c, hac⟩ := hback
      have haY : a ∈ Gamma.vertexSet Y :=
        (familyEdges_subset_vertexSet_prod Y
          (S.word.backwardEdges_subset_familyEdges hac)).1
      exact hfirstOff (by simpa only [s, htailStart, heq] using haY)
  have hfreshOfFirst (q : FinitePath Gamma.graph)
      (hq : q.IsSubpathOf (.inl tail))
      (hqStart : q.start = tail.start)
      (hqFirst : q.support ∩
        (Gamma.vertexSet Y \ removedInterior S.word.backwardEdges) ⊆
          {q.start, q.finish}) : Disjoint q.edgeSet S.word.forwardEdges := by
    rcases hsourceTail with hzero | hsTail
    · simp [hzero]
    · apply firstReferenceContact_forward_edges_fresh hW
        S.word.forwardEdges_subset_familyEdges
        S.word.backwardEdges_subset_familyEdges q
        (hq.2.trans htailEdges) (by simpa only [hqStart] using hstartNoPrefix)
        (fun h ↦ hsTail (hq.1 h))
      · intro x
        have hb := S.word.edgeBalance_forward_sub_backward hW hY x
        simpa only [S.first_eq, hqStart, htailStart] using hb
      · exact hqFirst
  have hincomingUnused (q : FinitePath Gamma.graph)
      (hq : q.IsSubpathOf (.inl tail))
      (hqStart : q.start = tail.start) (hqNe : q.start ≠ q.finish)
      (hqFirst : q.support ∩
        (Gamma.vertexSet Y \ removedInterior S.word.backwardEdges) ⊆
          {q.start, q.finish}) : ¬ HasIncoming S.word.forwardEdges q.finish := by
    rcases hsourceTail with hzero | hsTail
    · simp [hzero, HasIncoming]
    · apply firstReferenceContact_has_no_old_forward_incoming_of_balance hW
        S.word.forwardEdges_subset_familyEdges
        S.word.backwardEdges_subset_familyEdges q hqNe
        (hq.2.trans htailEdges) (by simpa only [hqStart] using hstartNoPrefix)
        (fun h ↦ hsTail (hq.1 h))
      · intro x
        have hb := S.word.edgeBalance_forward_sub_backward hW hY x
        simpa only [S.first_eq, hqStart, htailStart] using hb
      · exact hqFirst
  let upper : Set V := {x | HasIncoming total.forwardEdges x ∧
    ¬ HasOutgoing total.forwardEdges x}
  let contact : Set V := (Gamma.vertexSet Y \
    removedInterior S.word.backwardEdges) \ {tail.start}
  let stop : Set V := contact ∪ upper
  have hmeet : tail.walk.Meets stop := by
    by_cases hall : tail.edgeSet ⊆ total.forwardEdges
    · have hin : HasIncoming total.forwardEdges tail.finish := by
        obtain ⟨z, hz⟩ :=
          FinitePath.exists_incoming_edge_of_mem_support_of_ne_start tail
            tail.finish_mem_support htailNe.symm
        exact ⟨z, hall hz⟩
      have hout : ¬ HasOutgoing total.forwardEdges tail.finish := by
        rintro ⟨z, hz⟩
        rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin] at htailTerminal
        exact htailTerminal.2
          ⟨z, total.forwardEdges_subset_familyEdges hz⟩
      exact ⟨tail.finish, tail.finish_mem_support, Or.inr ⟨hin, hout⟩⟩
    · obtain ⟨x, hx, _hxne, hxin, hxout, _⟩ :=
        finitePath_exists_upperBoundary_of_not_subset hW
          total.forwardEdges_subset_familyEdges tail htailEdges htailNe
          (by simpa only [htailStart] using (show HasOutgoing
            total.forwardEdges a from ⟨b, habTotal⟩)) hall
      exact ⟨x, hx, Or.inr ⟨hxin, hxout⟩⟩
  let q := tail.firstHit stop hmeet
  have hqSub : q.IsSubpathOf (.inl tail) := tail.firstHit_isSubpathOf stop hmeet
  have hqStart : q.start = tail.start := rfl
  have hqFinish : q.finish ∈ stop := tail.firstHit_finish_mem stop hmeet
  have hstartNotUpper : tail.start ∉ upper := by
    intro h
    exact h.2 (by simpa only [htailStart] using (show HasOutgoing
      total.forwardEdges a from ⟨b, habTotal⟩))
  have hstartNotStop : tail.start ∉ stop := by
    rintro (h | h)
    · exact h.2 (Set.mem_singleton_iff.mpr rfl)
    · exact hstartNotUpper h
  have hqNe : q.start ≠ q.finish := by
    intro heq
    apply hstartNotStop
    rw [← hqStart, heq]
    exact hqFinish
  have hqFirstStop : ∀ x ∈ q.support, x ≠ q.start → x ∈ stop →
      x = q.finish := by
    intro x hx hxStart hxStop
    by_contra hneFinish
    have hlastIndex : x ≠ q.walk.support.getLast q.walk.support_ne_nil := by
      simpa only [q.walk.getLast_support] using hneFinish
    exact tail.firstHit_no_mem_before stop hmeet
      (List.mem_dropLast_of_mem_of_ne_getLast hx hlastIndex) hxStop
  have hqFirst : q.support ∩
      (Gamma.vertexSet Y \ removedInterior S.word.backwardEdges) ⊆
        {q.start, q.finish} := by
    rintro x ⟨hxq, hxContact⟩
    by_cases hxs : x = q.start
    · exact Set.mem_insert_iff.mpr (Or.inl hxs)
    · have hxStop : x ∈ stop := by
        left
        exact ⟨hxContact, fun h ↦ hxs (by
          simpa only [Set.mem_singleton_iff, q, hqStart] using h)⟩
      exact Set.mem_insert_of_mem _
        (Set.mem_singleton_iff.mpr (hqFirstStop x hxq hxs hxStop))
  have hqEdges : q.edgeSet ⊆ total.forwardEdges := by
    by_contra hnot
    obtain ⟨x, hxq, hxStart, hxin, hxout, hxpath⟩ :=
      finitePath_exists_upperBoundary_of_not_subset hW
        total.forwardEdges_subset_familyEdges q
        (hqSub.2.trans htailEdges) hqNe
        (by simpa only [hqStart, htailStart] using (show HasOutgoing
          total.forwardEdges a from ⟨b, habTotal⟩)) hnot
    have hxFinish : x ≠ q.finish := by
      rintro rfl
      obtain ⟨z, hz⟩ := hxpath
      exact FinitePath.no_outgoing_edge_at_finish q z hz
    exact hxFinish (hqFirstStop x hxq hxStart (Or.inr ⟨hxin, hxout⟩))
  have houtcome : q.finish = t ∨
      (q.finish ∈ Gamma.vertexSet Y \
        removedInterior S.word.backwardEdges ∧ q.finish ≠ q.start) := by
    rcases hqFinish with hcontact | hupper
    · exact Or.inr ⟨hcontact.1, hqNe.symm⟩
    · by_cases hqt : q.finish = t
      · exact Or.inl hqt
      · right
        have hqs : q.finish ≠ s := by
          intro heq
          rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin] at hfirst
          obtain ⟨z, hz⟩ := hupper.1
          exact hfirst.2 ⟨z, by
            have hzW := total.forwardEdges_subset_familyEdges hz
            simpa only [s, heq] using hzW⟩
        have hFb : edgeBalance total.forwardEdges q.finish = -1 :=
          edgeBalance_eq_neg_one_iff.mpr hupper
        have hb := total.edgeBalance_forward_sub_backward hW hY q.finish
        have hdelta : edgeBalance total.forwardEdges q.finish -
            edgeBalance total.backwardEdges q.finish = 0 := by
          have hqs' : q.finish ≠ total.vertex 0 := by
            simpa only [s] using hqs
          have hqt' : q.finish ≠ total.vertex (Fin.last total.length) := by
            simpa only [t] using hqt
          simpa [propInt, hqs', hqt'] using hb
        have hRb : edgeBalance total.backwardEdges q.finish = -1 := by
          omega
        have hR := edgeBalance_eq_neg_one_iff.mp hRb
        have hYmem : q.finish ∈ Gamma.vertexSet Y := by
          obtain ⟨z, hz⟩ := hR.1
          exact (familyEdges_subset_vertexSet_prod Y
            (total.backwardEdges_subset_familyEdges hz)).2
        refine ⟨⟨hYmem, ?_⟩, hqNe.symm⟩
        rintro ⟨_hin, hout⟩
        obtain ⟨z, hz⟩ := hout
        exact hR.2 ⟨z, S.backward_subset hz⟩
  exact ⟨⟨q, htailJoin.trans hqStart.symm, hqNe, hqEdges,
    hfreshOfFirst q hqSub hqStart hqFirst,
    hincomingUnused q hqSub hqStart hqNe hqFirst, hqFirst, by
      simpa only [t] using houtcome⟩⟩

/-- The complete one-step normalizer with an internal prescribed endpoint. -/
theorem FixedSafePrefixState.exists_normalizationStep_of_last_mem
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (htotal : total.IsIntervalSafe)
    (S : FixedSafePrefixState total)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (hcurrentNe : S.word.vertex (Fin.last S.word.length) ≠
      total.vertex (Fin.last total.length)) :
    Nonempty (FixedNormalizationStep S) := by
  obtain ⟨F⟩ := S.exists_fixedNextForward_of_last_mem hW hY hWfin hYfin
    hfirst hfirstOff hlastMem hlastOff hcurrentNe
  rcases F.outcome with hterminal | hcontact
  · obtain ⟨T⟩ := S.exists_terminalExtension_of_forward hY hYfin
      hfirstOff hlastOff F hterminal
    exact ⟨.terminal T⟩
  · obtain ⟨N⟩ := S.exists_successor_of_contact hW hY hYfin htotal
      hfirstOff F hcontact.1
    exact ⟨.successor N⟩

/-- A fixed prefix endpoint stays on the original forward warp even when the
prescribed last occurrence is not a warp terminal. -/
theorem FixedSafePrefixState.current_mem_forwardWarp_of_last_mem
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    S.word.vertex (Fin.last S.word.length) ∈ Gamma.vertexSet W := by
  rcases S.current_eq_totalFinish_or_hasTotalForward hW hY hYfin
      hfirstOff hlastOff with hterminal | ⟨b, hab⟩
  · simpa only [hterminal] using hlastMem
  · exact (familyEdges_subset_vertexSet_prod W
      (total.forwardEdges_subset_familyEdges hab)).1

/-- Forget a fixed prefix as a node of the original `W`-tree. -/
def FixedSafePrefixState.toLocalSafeWordNodeOfLastMem
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    LocalSafeWordNode W Y (total.vertex 0) where
  word := S.word
  safe := S.safe
  first_eq := S.first_eq
  current_mem := S.current_mem_forwardWarp_of_last_mem hW hY hYfin
    hfirstOff hlastMem hlastOff

/-- A normalized word ending at the prescribed internal endpoint is a node
of the original `W`-tree. -/
def FixedNormalizedTerminal.toLocalSafeWordNodeOfLastMem
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total} (T : FixedNormalizedTerminal S)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W) :
    LocalSafeWordNode W Y (total.vertex 0) where
  word := T.word
  safe := T.safe
  first_eq := T.first_eq
  current_mem := by simpa only [T.last_eq] using hlastMem

/-- A constructed strict successor remains an edge in the original local
safe-word tree under the weaker endpoint hypothesis. -/
theorem FixedSafePrefixSuccessor.localSafeWordExtension_of_last_mem
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total} (N : FixedSafePrefixSuccessor S)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    LocalSafeWordExtension hW hY
      (S.toLocalSafeWordNodeOfLastMem hW hY hYfin
        hfirstOff hlastMem hlastOff)
      (N.next.toLocalSafeWordNodeOfLastMem hW hY hYfin
        hfirstOff hlastMem hlastOff) := by
  refine ⟨N.embedding, N.length_lt, ?_⟩
  change N.next.word.vertexSet ⊆ S.word.vertexSet ∪
    localOwnerCarrier hW hY (S.word.vertex (Fin.last S.word.length))
  rw [N.next_vertexSet]
  have hforwardCovered : N.forward.path.support ⊆
      coveredPathSupport hW
        (S.word.vertex (Fin.last S.word.length)) :=
    finiteForward_support_subset_coveredPathSupport hW hY N.forward.path
      N.forward.nontrivial
      (N.forward.edges_total.trans total.forwardEdges_subset_familyEdges)
      N.forward.join
  have hcontactOwner : N.forward.path.finish ∈ N.referenceOwner.support := by
    rw [← N.backward.extension_finish]
    exact N.backward.extension_isSubpath_owner.1
      N.backward.extension.finish_mem_support
  have hbackwardLocal : N.backward.extension.support ⊆
      localOwnerCarrier hW hY
        (S.word.vertex (Fin.last S.word.length)) := by
    apply (N.backward.extension_isSubpath_owner.1).trans
    exact referenceOwner_support_subset_localOwnerCarrier hW hY
      (hforwardCovered N.forward.path.finish_mem_support)
      N.referenceOwner N.referenceOwner_mem hcontactOwner
  intro x hx
  rcases hx with hxOld | hxBackward
  · rcases hxOld with hxWord | hxForward
    · exact Or.inl hxWord
    · exact Or.inr (Or.inl (hforwardCovered hxForward))
  · exact Or.inr (hbackwardLocal hxBackward)

/-- The final forward suffix is a local-tree edge under the weaker endpoint
hypothesis. -/
theorem FixedNormalizedTerminalExtension.localSafeWordExtension_of_last_mem
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total}
    (E : FixedNormalizedTerminalExtension S)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    LocalSafeWordExtension hW hY
      (S.toLocalSafeWordNodeOfLastMem hW hY hYfin
        hfirstOff hlastMem hlastOff)
      (E.terminal.toLocalSafeWordNodeOfLastMem hlastMem) := by
  refine ⟨E.terminal.embedding, ?_, ?_⟩
  · change S.word.length < E.terminal.word.length
    rw [E.word_eq,
      S.word.appendForwardPath_length E.path E.join E.edges_forward E.fresh]
    have hpositive : 0 < E.path.walk.length := by
      exact Nat.pos_of_ne_zero (fun h ↦ E.nontrivial
        (Walk.endpoints_eq_of_length_eq_zero E.path.walk h))
    omega
  · change E.terminal.word.vertexSet ⊆ S.word.vertexSet ∪
      localOwnerCarrier hW hY (S.word.vertex (Fin.last S.word.length))
    rw [E.word_eq,
      S.word.appendForwardPath_vertexSet E.path E.join E.edges_forward E.fresh]
    have hpathLocal := finiteForward_support_subset_localOwnerCarrier
      hW hY E.path E.nontrivial E.edges_forward E.join
    intro x hx
    exact hx.elim Or.inl (fun h ↦ Or.inr (hpathLocal h))

/-- From any fixed prefix, the weaker endpoint normalizer reaches a local
tree node ending at the prescribed endpoint. -/
theorem FixedSafePrefixState.exists_reachable_of_last_mem
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (htotal : total.IsIntervalSafe)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (S : FixedSafePrefixState total) :
    ∃ Q : LocalSafeWordNode W Y (total.vertex 0),
      Relation.ReflTransGen (LocalSafeWordExtension hW hY)
        (S.toLocalSafeWordNodeOfLastMem hW hY hYfin
          hfirstOff hlastMem hlastOff) Q ∧
      Q.word.vertex (Fin.last Q.word.length) =
        total.vertex (Fin.last total.length) := by
  classical
  let P : ℕ → Prop := fun n ↦ ∀ S : FixedSafePrefixState total,
    total.length - S.word.length = n →
      ∃ Q : LocalSafeWordNode W Y (total.vertex 0),
        Relation.ReflTransGen (LocalSafeWordExtension hW hY)
          (S.toLocalSafeWordNodeOfLastMem hW hY hYfin
            hfirstOff hlastMem hlastOff) Q ∧
        Q.word.vertex (Fin.last Q.word.length) =
          total.vertex (Fin.last total.length)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hremaining
        by_cases hdone : S.word.vertex (Fin.last S.word.length) =
            total.vertex (Fin.last total.length)
        · exact ⟨S.toLocalSafeWordNodeOfLastMem hW hY hYfin
              hfirstOff hlastMem hlastOff, .refl, hdone⟩
        · obtain ⟨step⟩ := S.exists_normalizationStep_of_last_mem
            hW hY hWfin hYfin htotal hfirst hfirstOff hlastMem hlastOff hdone
          rcases step with terminal | successor
          · let Q := terminal.terminal.toLocalSafeWordNodeOfLastMem hlastMem
            refine ⟨Q, Relation.ReflTransGen.single ?_,
              terminal.terminal.last_eq⟩
            exact terminal.localSafeWordExtension_of_last_mem hW hY hYfin
              hfirstOff hlastMem hlastOff
          · have hnextBound := successor.next.length_le_total
            have hless : total.length - successor.next.word.length < n := by
              have hstateTotal : S.word.length < total.length :=
                successor.length_lt.trans_le hnextBound
              have hsub := Nat.sub_lt_sub_left hstateTotal successor.length_lt
              simpa only [hremaining] using hsub
            obtain ⟨Q, hreach, hlastQ⟩ :=
              ih _ hless successor.next rfl
            refine ⟨Q, (Relation.ReflTransGen.single ?_).trans hreach, hlastQ⟩
            exact successor.localSafeWordExtension_of_last_mem hW hY hYfin
              hfirstOff hlastMem hlastOff
  exact hP (total.length - S.word.length) S rfl

/-- Every finite interval-safe word whose first occurrence is an initial
forward-warp vertex and whose last occurrence is merely covered by that warp
normalizes to a node reachable in the original local tree, with exactly the
same last occurrence. -/
theorem exists_reachable_normalizedEndpointNode
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (total : FiniteColouredOccurrenceWord W Y)
    (htotal : total.IsIntervalSafe)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    ∃ Q : LocalSafeWordNode W Y (total.vertex 0),
      Relation.ReflTransGen (LocalSafeWordExtension hW hY)
        (LocalSafeWordNode.root (W := W) (Y := Y) (total.vertex 0)
          (initialSet_subset_vertexSet W hfirst)) Q ∧
      Q.word.vertex (Fin.last Q.word.length) =
        total.vertex (Fin.last total.length) := by
  let S := FixedSafePrefixState.initial total
  obtain ⟨Q, hreach, hlastQ⟩ := S.exists_reachable_of_last_mem
    hW hY hWfin hYfin htotal hfirst hfirstOff hlastMem hlastOff
  have hroot : S.toLocalSafeWordNodeOfLastMem hW hY hYfin
      hfirstOff hlastMem hlastOff =
      LocalSafeWordNode.root (W := W) (Y := Y) (total.vertex 0)
        (initialSet_subset_vertexSet W hfirst) := by
    exact LocalSafeWordNode.eq_of_word_eq rfl
  rw [hroot] at hreach
  exact ⟨Q, hreach, hlastQ⟩

#print axioms FixedSafePrefixState.exists_fixedNextForward_of_last_mem
#print axioms FixedSafePrefixState.exists_normalizationStep_of_last_mem
#print axioms FixedSafePrefixState.exists_reachable_of_last_mem
#print axioms exists_reachable_normalizedEndpointNode

end Erdos599.Alternating.FiniteColouredOccurrenceWord
