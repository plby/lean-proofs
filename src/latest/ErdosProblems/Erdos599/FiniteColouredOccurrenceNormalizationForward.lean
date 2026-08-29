/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceNormalizationState
import ErdosProblems.Erdos599.ColouredSafeForwardContact

/-!
# The next fixed-word forward fragment

Starting at a root-tight normalization state, this file follows the unique
finite `W` owner to its first reference contact outside the already removed
interiors.  Balance proves that no edge of the fixed total forward relation
can be skipped before that contact.  If there is no such contact, the suffix
ends at the fixed total word's terminal.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

private theorem walk_exists_used_incoming_unused_outgoing
    (hW : Gamma.IsWarp W) {F : Set (V × V)}
    (hF : F ⊆ familyEdges W) {a b : V} (q : Walk Gamma.graph a b)
    (hq : q.edgeSet ⊆ familyEdges W) (hFin : HasIncoming F a)
    (hnot : ¬q.edgeSet ⊆ F) :
    ∃ x ∈ q.support, HasIncoming F x ∧ ¬HasOutgoing F x ∧
      HasOutgoing q.edgeSet x := by
  induction q with
  | nil => exact False.elim (hnot (by simp [Walk.edgeSet]))
  | @cons a c b hac q ih =>
      have hacW : (a, c) ∈ familyEdges W := hq (by simp [Walk.edgeSet])
      by_cases hacF : (a, c) ∈ F
      · have hqW : q.edgeSet ⊆ familyEdges W := by
          intro e he
          exact hq (by simp [Walk.edgeSet, he])
        have hqNot : ¬q.edgeSet ⊆ F := by
          intro hsub
          apply hnot
          intro e he
          simp only [Walk.edgeSet_cons, Set.mem_union,
            Set.mem_singleton_iff] at he
          exact he.elim (fun h ↦ h ▸ hacF) (fun h ↦ hsub h)
        obtain ⟨x, hx, hxin, hxout, hqx⟩ :=
          ih hqW ⟨a, hacF⟩ hqNot
        exact ⟨x, by simp [Walk.support, hx], hxin, hxout, by
          obtain ⟨y, hxy⟩ := hqx
          exact ⟨y, by simp [Walk.edgeSet, hxy]⟩⟩
      · have hnoOut : ¬HasOutgoing F a := by
          rintro ⟨z, haz⟩
          have hzc : z = c := (IsWarp.familyEdges_biUnique hW).2 (hF haz) hacW
          exact hacF (hzc ▸ haz)
        exact ⟨a, by simp [Walk.support], hFin, hnoOut,
          ⟨c, by simp [Walk.edgeSet]⟩⟩

/-- If a nontrivial `W` fragment starts with a total-forward incidence but
contains a missing total-forward edge, it has an internal upper boundary of
the total forward relation. -/
private theorem finitePath_exists_totalForward_upperBoundary_of_not_subset
    (hW : Gamma.IsWarp W) {F : Set (V × V)}
    (hF : F ⊆ familyEdges W) (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) (hne : p.start ≠ p.finish)
    (hstart : HasOutgoing F p.start) (hnot : ¬p.edgeSet ⊆ F) :
    ∃ x ∈ p.support, x ≠ p.start ∧ HasIncoming F x ∧
      ¬HasOutgoing F x ∧ HasOutgoing p.edgeSet x := by
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
  have hqNot : ¬q.edgeSet ⊆ F := by
    intro hsub
    apply hnot
    intro e he
    change e ∈ p.walk.edgeSet at he
    rw [hw] at he
    simp only [Walk.edgeSet_cons, Set.mem_union,
      Set.mem_singleton_iff] at he
    exact he.elim (fun h ↦ h ▸ hacF) (fun h ↦ hsub h)
  obtain ⟨x, hxq, hxin, hxout, hqx⟩ :=
    walk_exists_used_incoming_unused_outgoing hW hF q hqW ⟨p.start, hacF⟩ hqNot
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

/-- A path selected up to its first new reference contact cannot skip a
fixed total-forward edge. -/
theorem FixedSafePrefixState.firstContact_edges_subset_totalForward
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) (hne : p.start ≠ p.finish)
    (hstart : HasOutgoing total.forwardEdges p.start)
    (hsource : ∀ x ∈ p.support, x ≠ p.start → x ≠ total.vertex 0)
    (htarget : ∀ x, HasOutgoing p.edgeSet x →
      x ≠ total.vertex (Fin.last total.length))
    (hfirst : p.support ∩
      (Gamma.vertexSet Y \ removedInterior S.word.backwardEdges) ⊆
        {p.start, p.finish}) :
    p.edgeSet ⊆ total.forwardEdges := by
  by_contra hnot
  obtain ⟨x, hxp, hxStart, hxFin, hxNoOut, hxPathOut⟩ :=
    finitePath_exists_totalForward_upperBoundary_of_not_subset
      hW total.forwardEdges_subset_familyEdges p hp hne hstart hnot
  have hxs : x ≠ total.vertex 0 := hsource x hxp hxStart
  have hxt : x ≠ total.vertex (Fin.last total.length) := htarget x hxPathOut
  have hbalance := total.edgeBalance_forward_sub_backward hW hY x
  have hFb : edgeBalance total.forwardEdges x = -1 := by
    simp [edgeBalance, propInt, hxFin, hxNoOut]
  have hxContact : x ∈ Gamma.vertexSet Y \
      removedInterior S.word.backwardEdges := by
    by_contra hnotContact
    by_cases hxY : x ∈ Gamma.vertexSet Y
    · have hxInterior : x ∈ removedInterior S.word.backwardEdges := by
        exact Classical.byContradiction fun h ↦ hnotContact ⟨hxY, h⟩
      have hRin : HasIncoming total.backwardEdges x := by
        obtain ⟨z, hzx⟩ := hxInterior.1
        exact ⟨z, S.backward_subset hzx⟩
      have hRout : HasOutgoing total.backwardEdges x := by
        obtain ⟨z, hxz⟩ := hxInterior.2
        exact ⟨z, S.backward_subset hxz⟩
      have hRb : edgeBalance total.backwardEdges x = 0 := by
        simp [edgeBalance, hRin, hRout]
      rw [hFb, hRb] at hbalance
      simp [propInt, hxs, hxt] at hbalance
    · have hRin : ¬HasIncoming total.backwardEdges x := by
        rintro ⟨z, hzx⟩
        exact hxY (familyEdges_subset_vertexSet_prod Y
          (total.backwardEdges_subset_familyEdges hzx)).2
      have hRout : ¬HasOutgoing total.backwardEdges x := by
        rintro ⟨z, hxz⟩
        exact hxY (familyEdges_subset_vertexSet_prod Y
          (total.backwardEdges_subset_familyEdges hxz)).1
      have hRb : edgeBalance total.backwardEdges x = 0 := by
        simp [edgeBalance, hRin, hRout]
      rw [hFb, hRb] at hbalance
      simp [propInt, hxs, hxt] at hbalance
  have hxEnds := hfirst ⟨hxp, hxContact⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxEnds
  rcases hxEnds with hx | hx
  · exact hxStart hx
  · obtain ⟨z, hxz⟩ := hxPathOut
    exact FinitePath.no_outgoing_edge_at_finish p z (hx ▸ hxz)

/-- The concrete next forward fragment inside a fixed total word. -/
structure FixedNextForward
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total) where
  path : FinitePath Gamma.graph
  join : S.word.vertex (Fin.last S.word.length) = path.start
  nontrivial : path.start ≠ path.finish
  edges_total : path.edgeSet ⊆ total.forwardEdges
  fresh : Disjoint path.edgeSet S.word.forwardEdges
  incoming_unused : ¬HasIncoming S.word.forwardEdges path.finish
  first_contact : path.support ∩
      (Gamma.vertexSet Y \ removedInterior S.word.backwardEdges) ⊆
    {path.start, path.finish}
  outcome : path.finish = total.vertex (Fin.last total.length) ∨
    (path.finish ∈ Gamma.vertexSet Y \
      removedInterior S.word.backwardEdges ∧ path.finish ≠ path.start)

theorem FixedNextForward.contact_geometry
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total} (F : FixedNextForward S) :
    F.path.support ∩ Gamma.vertexSet Y ⊆
      {F.path.start, F.path.finish} ∪ removedInterior S.word.backwardEdges := by
  rintro x ⟨hxp, hxY⟩
  by_cases hxR : x ∈ removedInterior S.word.backwardEdges
  · exact Or.inr hxR
  · exact Or.inl (F.first_contact ⟨hxp, hxY, hxR⟩)

/-- Follow the fixed total word's current `W` owner.  Either its first new
reference contact is reached, or the fixed total terminal is reached.  In
both cases every selected edge belongs to the fixed total forward relation;
this is a theorem from balance, not a stored continuation choice. -/
theorem FixedSafePrefixState.exists_fixedNextForward
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
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
    have hnoOut : ¬HasOutgoing (familyEdges W) tail.finish := by
      rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin] at htailTerminal
      exact htailTerminal.2
    exact hnoOut ⟨b, by
      have hfinishA : tail.finish = a := heq.symm.trans htailStart
      simpa only [hfinishA] using habW⟩
  have htailJoin : a = tail.start := htailStart.symm
  have hstartNoPrefix : ¬HasOutgoing S.word.forwardEdges tail.start := by
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
  have hsourcePath (q : FinitePath Gamma.graph)
      (hq : q.IsSubpathOf (.inl tail)) :
      ∀ x ∈ q.support, x ≠ q.start → x ≠ s := by
    intro x hx hxStart hxs
    subst x
    rcases hsourceTail with hzero | hsTail
    · by_cases hsa : s = q.start
      · exact hxStart hsa
      · exact (ColouredSafeReverseReachability.forward_fragment_avoids_initial
          hW hWfin hfirst q (hq.2.trans htailEdges) hsa) hx
    · exact hsTail (hq.1 hx)
  have htargetPath (q : FinitePath Gamma.graph)
      (hqEdges : q.edgeSet ⊆ familyEdges W) :
      ∀ x, HasOutgoing q.edgeSet x → x ≠ t := by
    intro x hxOut hxt
    rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin] at hlast
    obtain ⟨z, hxz⟩ := hxOut
    exact hlast.2 ⟨z, by simpa only [t, hxt] using hqEdges hxz⟩
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
          {q.start, q.finish}) : ¬HasIncoming S.word.forwardEdges q.finish := by
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
  let contact := (Gamma.vertexSet Y \
    removedInterior S.word.backwardEdges) \ {tail.start}
  by_cases hmeet : tail.walk.Meets contact
  · let q := tail.firstHit contact hmeet
    have hqSub : q.IsSubpathOf (.inl tail) :=
      tail.firstHit_isSubpathOf contact hmeet
    have hqStart : q.start = tail.start := rfl
    have hqFinish : q.finish ∈ contact := tail.firstHit_finish_mem contact hmeet
    have hqNe : q.start ≠ q.finish := by
      intro heq
      exact hqFinish.2 (Set.mem_singleton_iff.mpr (heq.symm.trans hqStart))
    have hqFirst : q.support ∩
        (Gamma.vertexSet Y \ removedInterior S.word.backwardEdges) ⊆
          {q.start, q.finish} := by
      rintro x ⟨hxq, hxContact⟩
      by_cases hxs : x = q.start
      · exact Set.mem_insert_iff.mpr (Or.inl hxs)
      · have hxf : x = q.finish := by
          by_contra hneFinish
          have hlastIndex : x ≠ q.walk.support.getLast q.walk.support_ne_nil := by
            simpa only [q.walk.getLast_support] using hneFinish
          exact tail.firstHit_no_mem_before contact hmeet
            (List.mem_dropLast_of_mem_of_ne_getLast hxq hlastIndex)
            ⟨hxContact, fun h ↦ hxs (by
              simpa only [Set.mem_singleton_iff, q, hqStart] using h)⟩
        exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr hxf)
    have hqEdges : q.edgeSet ⊆ total.forwardEdges :=
      S.firstContact_edges_subset_totalForward hW hY q
        (hqSub.2.trans htailEdges) hqNe
        (by simpa only [hqStart, htailStart] using (show HasOutgoing
          total.forwardEdges a from ⟨b, habTotal⟩))
        (hsourcePath q hqSub) (htargetPath q (hqSub.2.trans htailEdges)) hqFirst
    exact ⟨⟨q, htailJoin.trans hqStart.symm, hqNe, hqEdges,
      hfreshOfFirst q hqSub hqStart hqFirst,
      hincomingUnused q hqSub hqStart hqNe hqFirst, hqFirst,
      Or.inr ⟨hqFinish.1, hqNe.symm⟩⟩⟩
  · have htailFirst : tail.support ∩
        (Gamma.vertexSet Y \ removedInterior S.word.backwardEdges) ⊆
          {tail.start, tail.finish} := by
      rintro x ⟨hxtail, hxContact⟩
      by_cases hxs : x = tail.start
      · exact Set.mem_insert_iff.mpr (Or.inl hxs)
      · exact False.elim (hmeet ⟨x, hxtail, hxContact, hxs⟩)
    have htailTotal : tail.edgeSet ⊆ total.forwardEdges :=
      S.firstContact_edges_subset_totalForward hW hY tail htailEdges htailNe
        (by simpa only [htailStart] using (show HasOutgoing
          total.forwardEdges a from ⟨b, habTotal⟩))
        (hsourcePath tail tail.isSubpathOf_self)
        (htargetPath tail htailEdges) htailFirst
    have htailFinishTotal : tail.finish = t := by
      by_contra hneT
      have hinF : HasIncoming total.forwardEdges tail.finish := by
        obtain ⟨z, hzt⟩ :=
          FinitePath.exists_incoming_edge_of_mem_support_of_ne_start tail
            tail.finish_mem_support htailNe.symm
        exact ⟨z, htailTotal hzt⟩
      have houtF : ¬HasOutgoing total.forwardEdges tail.finish := by
        intro hout
        obtain ⟨z, htz⟩ := hout
        rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin] at htailTerminal
        exact htailTerminal.2 ⟨z, total.forwardEdges_subset_familyEdges htz⟩
      have hneS : tail.finish ≠ s := by
        intro heq
        rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin] at hfirst
        obtain ⟨z, hzt⟩ := hinF
        apply hfirst.2
        exact ⟨z, by
          have hzW := total.forwardEdges_subset_familyEdges hzt
          simpa only [s, heq] using hzW⟩
      have hFb : edgeBalance total.forwardEdges tail.finish = -1 := by
        simp [edgeBalance, propInt, hinF, houtF]
      have hRb : edgeBalance total.backwardEdges tail.finish = 0 := by
        by_cases hy : tail.finish ∈ Gamma.vertexSet Y
        · have hInterior : tail.finish ∈ removedInterior S.word.backwardEdges := by
            by_contra hnotInterior
            exact hmeet ⟨tail.finish, tail.finish_mem_support,
              ⟨hy, hnotInterior⟩, fun h ↦ htailNe h.symm⟩
          have hinR : HasIncoming total.backwardEdges tail.finish := by
            obtain ⟨z, hzt⟩ := hInterior.1
            exact ⟨z, S.backward_subset hzt⟩
          have houtR : HasOutgoing total.backwardEdges tail.finish := by
            obtain ⟨z, htz⟩ := hInterior.2
            exact ⟨z, S.backward_subset htz⟩
          simp [edgeBalance, hinR, houtR]
        · have hinR : ¬HasIncoming total.backwardEdges tail.finish := by
            rintro ⟨z, hzt⟩
            exact hy (familyEdges_subset_vertexSet_prod Y
              (total.backwardEdges_subset_familyEdges hzt)).2
          have houtR : ¬HasOutgoing total.backwardEdges tail.finish := by
            rintro ⟨z, htz⟩
            exact hy (familyEdges_subset_vertexSet_prod Y
              (total.backwardEdges_subset_familyEdges htz)).1
          simp [edgeBalance, hinR, houtR]
      have hb := total.edgeBalance_forward_sub_backward hW hY tail.finish
      rw [hFb, hRb] at hb
      have hneS' : tail.finish ≠ total.vertex 0 := by
        simpa only [s] using hneS
      have hneT' : tail.finish ≠ total.vertex (Fin.last total.length) := by
        simpa only [t] using hneT
      simp only [propInt, if_neg hneS', if_neg hneT'] at hb
      omega
    exact ⟨⟨tail, htailJoin, htailNe, htailTotal,
      hfreshOfFirst tail tail.isSubpathOf_self rfl htailFirst,
      hincomingUnused tail tail.isSubpathOf_self rfl htailNe htailFirst,
      htailFirst, Or.inl htailFinishTotal⟩⟩

#print axioms FixedSafePrefixState.firstContact_edges_subset_totalForward
#print axioms FixedSafePrefixState.exists_fixedNextForward

end Erdos599.Alternating.FiniteColouredOccurrenceWord
