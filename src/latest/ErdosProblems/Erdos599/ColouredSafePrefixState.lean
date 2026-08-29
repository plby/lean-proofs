/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNextForward
import ErdosProblems.Erdos599.ColouredSafeReferenceIntervalChoice

/-!
# The actual finite state of the safe occurrence recursion

The state stores chronological data and the precise first/later-contact
interval records. Its successor is constructed from the proved forward
contact and reference interval choices; there is no successor oracle or
output warp in the state.
-/

namespace Erdos599.ColouredSafeReverseReachability

open Set DirectedPath Alternating
open Alternating.SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

structure SafePrefixState (W Y : Set Gamma.DPath) (s : V) where
  word : FiniteColouredOccurrenceWord W Y
  safe : word.IsIntervalSafe
  first_eq : word.vertex 0 = s
  current_mem : word.vertex (Fin.last word.length) ∈ Gamma.vertexSet W
  current_outside : word.vertex (Fin.last word.length) ∉ reverseReachable W Y s
  phase : (word.forwardEdges = ∅ ∧ word.vertex (Fin.last word.length) = s) ∨
    HasOutgoing word.backwardEdges (word.vertex (Fin.last word.length))
  intervals : ∀ p : FinitePath Gamma.graph, (Sum.inl p : Gamma.DPath) ∈ Y →
    word.backwardEdges ∩ p.edgeSet = ∅ ∨
      Nonempty (PriorRemovedInterval p (reverseReachable W Y s)
        word.backwardEdges word.forwardEdges)

def SafePrefixState.initial {s : V} (hsW : s ∈ Gamma.vertexSet W)
    (hsC : s ∉ reverseReachable W Y s) : SafePrefixState W Y s where
  word := FiniteColouredOccurrenceWord.emptyAt s
  safe := FiniteColouredOccurrenceWord.emptyAt_isIntervalSafe s
  first_eq := rfl
  current_mem := hsW
  current_outside := hsC
  phase := Or.inl ⟨FiniteColouredOccurrenceWord.emptyAt_forwardEdges s, rfl⟩
  intervals := by intro p hp; left; simp

private theorem finish_eq_of_same_edges_of_nontrivial
    (p q : FinitePath Gamma.graph) (hne : p.start ≠ p.finish)
    (hE : p.edgeSet = q.edgeSet) : p.finish = q.finish := by
  obtain ⟨x, hx⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start p
    p.finish_mem_support hne.symm
  have hxq : (x, p.finish) ∈ q.edgeSet := hE ▸ hx
  have hpq : p.finish ∈ q.support := (q.edgeSet_subset_support_prod hxq).2
  by_contra hnot
  obtain ⟨y, hy⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish q hpq hnot
  exact FinitePath.no_outgoing_edge_at_finish p y (hE.symm ▸ hy)

private theorem choice_old_finish_mem_forward
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    {s : V} (S : SafePrefixState W Y s) (owner : FinitePath Gamma.graph)
    (howner : (Sum.inl owner : Gamma.DPath) ∈ Y) {w : V}
    (K : BackwardIntervalChoice owner (reverseReachable W Y s) S.word.backwardEdges w) :
    K.old.finish ∈ Gamma.vertexSet W := by
  by_cases htriv : K.old.start = K.old.finish
  · have hstart : K.old.start ∈ Gamma.vertexSet W := by
      apply earliest_reference_exit_mem_forward hsource owner howner
        K.old_start_earliest.mem_support K.old_start_earliest.outside
      intro b _hb hba
      obtain ⟨hba⟩ := hba
      exact K.old_start_earliest.earlier_mem (PathOrder.before_of_orderedOccurrence hba)
    exact htriv ▸ hstart
  · rcases S.intervals owner howner with hempty | hprior
    · obtain ⟨x, hx⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start K.old
        K.old.finish_mem_support (Ne.symm htriv)
      have he : K.old.edgeSet = ∅ := K.removed_eq.symm.trans hempty
      exact False.elim (Set.notMem_empty _ (he ▸ hx))
    · let prior := Classical.choice hprior
      have he : K.old.edgeSet = prior.path.edgeSet :=
        K.removed_eq.symm.trans prior.removed_eq
      have hfinish := finish_eq_of_same_edges_of_nontrivial K.old prior.path htriv he
      obtain ⟨x, hx⟩ := prior.finish_incoming
      have hmem := (familyEdges_subset_vertexSet_prod W
        (S.word.forwardEdges_subset_familyEdges hx)).2
      simpa only [hfinish] using hmem

/-- Construct a strictly longer state, retaining the actual forward
fragment and the reference owner containing the backward extension.
All interval records, including earliest lower endpoints, survive. -/
theorem SafePrefixState.exists_successor_with_fragments
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {s : V} (hs : s ∈ Gamma.initialSet W) (hsOff : s ∉ Gamma.vertexSet Y)
    (S : SafePrefixState W Y s) :
    ∃ T : SafePrefixState W Y s,
      S.word.Prefix T.word ∧ S.word.length < T.word.length ∧
      ∃ F : NextForwardContact S.word, F.path.edgeSet ⊆ T.word.forwardEdges ∧
        T.word.vertexSet ⊆ S.word.vertexSet ∪ F.path.support ∪ F.owner.support := by
  classical
  have hfirst : S.word.vertex 0 ∈ Gamma.initialSet W := by
    rw [S.first_eq]
    exact hs
  have hfirstOff : S.word.vertex 0 ∉ Gamma.vertexSet Y := by
    rw [S.first_eq]
    exact hsOff
  have hphase : (S.word.forwardEdges = ∅ ∧
      S.word.vertex (Fin.last S.word.length) = S.word.vertex 0) ∨
      HasOutgoing S.word.backwardEdges (S.word.vertex (Fin.last S.word.length)) := by
    simpa only [S.first_eq] using S.phase
  have hnotC : S.word.vertex (Fin.last S.word.length) ∉
      reverseReachable W Y (S.word.vertex 0) := by
    simpa only [S.first_eq] using S.current_outside
  obtain ⟨F⟩ := exists_nextForwardContact hW hY hWfin hYfin hsource hterminal
    S.word S.safe hfirst hfirstOff S.current_mem hphase hnotC
  have hfinishC : F.path.finish ∉ reverseReachable W Y s := by
    simpa only [S.first_eq] using F.finish_outside
  have hpredC : F.predecessor ∉ reverseReachable W Y s := by
    simpa only [S.first_eq] using F.predecessor_outside
  obtain ⟨K⟩ := exists_backwardIntervalChoice (S.intervals F.owner F.owner_mem)
    F.predecessor_edge hpredC hfinishC F.finish_not_interior F.incoming_unused
  have hstart : F.path.start ∈ Gamma.vertexSet Y →
      HasOutgoing S.word.backwardEdges F.path.start := by
    intro haY
    rcases S.phase with ⟨_hzero, haFirst⟩ | hback
    · apply False.elim
      apply hsOff
      simpa only [← F.join, haFirst] using haY
    · simpa only [F.join] using hback
  obtain ⟨Q, hQ, hQfirst, hQlast, hQlen, hQvertices, hQF, hQR, hprefix⟩ :=
    S.safe.exists_forward_backward_extension hY hYfin F.path F.join
      F.edges F.fresh hstart F.contact_geometry (.inl F.owner) F.owner_mem
      K.old K.extension K.old_isSubpath K.extension_isSubpath K.join
      K.removed_eq K.extension_finish K.extension_nontrivial
  have hnewIncoming : HasIncoming Q.forwardEdges F.path.finish := by
    obtain ⟨x, hx⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start F.path
      F.path.finish_mem_support F.nontrivial.symm
    exact ⟨x, by rw [hQF]; exact Or.inr hx⟩
  have hnewOutgoing : HasOutgoing Q.backwardEdges K.extension.start := by
    obtain ⟨x, hx⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      K.extension K.extension.start_mem_support K.extension_nontrivial
    exact ⟨x, by rw [hQR]; exact Or.inr hx⟩
  have hnextW : K.extension.start ∈ Gamma.vertexSet W := by
    rw [← K.join]
    exact choice_old_finish_mem_forward hsource S F.owner F.owner_mem K
  have hrecords : ∀ p : FinitePath Gamma.graph, (Sum.inl p : Gamma.DPath) ∈ Y →
      Q.backwardEdges ∩ p.edgeSet = ∅ ∨
        Nonempty (PriorRemovedInterval p (reverseReachable W Y s)
          Q.backwardEdges Q.forwardEdges) := by
    intro p hpY
    by_cases hp : p = F.owner
    · subst p
      right
      rw [hQR]
      exact K.exists_updatedPrior hfinishC hnewIncoming
    · have hdisj : Disjoint K.extension.edgeSet p.edgeSet := by
        apply Set.disjoint_left.2
        intro e heK hep
        have hne : (Sum.inl p : Gamma.DPath) ≠ .inl F.owner :=
          fun h ↦ hp (Sum.inl.inj h)
        exact Set.disjoint_left.1 (hY hpY F.owner_mem hne)
          (p.edgeSet_subset_support_prod hep).1
          (K.extension_isSubpath.1 (K.extension.edgeSet_subset_support_prod heK).1)
      have hReq : Q.backwardEdges ∩ p.edgeSet = S.word.backwardEdges ∩ p.edgeSet := by
        rw [hQR, Set.union_inter_distrib_right,
          Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.union_empty]
      rcases S.intervals p hpY with hempty | hprior
      · exact Or.inl (hReq.trans hempty)
      · let prior := Classical.choice hprior
        right
        refine ⟨PriorRemovedInterval.of_subpath prior.isSubpath
          (hReq.trans prior.removed_eq) prior.start_earliest prior.finish_outside ?_⟩
        obtain ⟨x, hx⟩ := prior.finish_incoming
        exact ⟨x, by rw [hQF]; exact Or.inl hx⟩
  let T : SafePrefixState W Y s := {
    word := Q
    safe := hQ
    first_eq := hQfirst.trans S.first_eq
    current_mem := by simpa only [hQlast] using hnextW
    current_outside := by simpa only [hQlast] using K.extension_start_outside
    phase := Or.inr (by simpa only [hQlast] using hnewOutgoing)
    intervals := hrecords }
  refine ⟨T, hprefix, ?_, F, ?_, ?_⟩
  · change S.word.length < Q.length
    rw [hQlen]
    have hlen : 0 < K.extension.walk.length := by
      have hzero : ∀ {a b : V} (p : Walk Gamma.graph a b), p.length = 0 → a = b := by
        intro a b p hp
        cases p with
        | nil => rfl
        | cons h p => simp at hp
      by_contra hnot
      exact K.extension_nontrivial (hzero K.extension.walk (Nat.eq_zero_of_not_pos hnot))
    omega
  · change F.path.edgeSet ⊆ Q.forwardEdges
    rw [hQF]
    exact Set.subset_union_right
  · change Q.vertexSet ⊆ S.word.vertexSet ∪ F.path.support ∪ F.owner.support
    rw [hQvertices]
    exact Set.union_subset_union_right _ K.extension_isSubpath.1

/-- Forget only the fragment witnesses from the constructed successor,
preserving the original single-source recursion interface. -/
theorem SafePrefixState.exists_successor
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {s : V} (hs : s ∈ Gamma.initialSet W) (hsOff : s ∉ Gamma.vertexSet Y)
    (S : SafePrefixState W Y s) :
    ∃ T : SafePrefixState W Y s,
      S.word.Prefix T.word ∧ S.word.length < T.word.length := by
  obtain ⟨T, hp, hl, _hfragments⟩ := S.exists_successor_with_fragments
    hW hY hWfin hYfin hsource hterminal hs hsOff
  exact ⟨T, hp, hl⟩

#print axioms SafePrefixState.exists_successor_with_fragments
#print axioms SafePrefixState.exists_successor

end Erdos599.ColouredSafeReverseReachability
