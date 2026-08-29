/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Backward-owner uniqueness in an infinite safe trace

The interval clause in `IsSafe` has a useful consequence which is easy to
lose when an alternating trace is represented only by its links: two
different backward links cannot be subpaths of the same finite reference
member.  This file records that consequence in the index-friendly form used
by fractured-warp projection.
-/

noncomputable section

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

local instance infiniteOwnerDecidableEq : DecidableEq V := Classical.decEq V

private theorem Link.not_mem_interior_entry' {D : Digraph V}
    (l : Link D) : l.entry ∉ l.interior := by
  intro h
  exact h.2 (by rw [l.endpoints_eq]; simp)

/-- Different backward links of an infinite trace have disjoint supports.
The two crossed-endpoint intersections allowed by `CompatibleInOrder` are
ruled out using the next forward link (which always exists in an infinite
trace) or the intervening forward link. -/
theorem InfiniteTrace.backward_support_disjoint_of_lt
    {D : Digraph V} (R : InfiniteTrace D) {i j : ℕ}
    (hij : i < j)
    (hi : (R.link i).direction = .backward)
    (hj : (R.link j).direction = .backward) :
    Disjoint (R.link i).path.support (R.link j).path.support := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hcompat := R.compatible i j hij
  simp only [CompatibleInOrder, hi, hj] at hcompat
  rcases hcompat hxi hxj with hcross | hcross
  · have hnext : (R.link (j + 1)).direction = .forward := by
      have halt := R.alternates j
      rw [hj] at halt
      cases h : (R.link (j + 1)).direction with
      | forward => rfl
      | backward => exact (halt h.symm).elim
    have hxnext : x ∈ (R.link (j + 1)).path.support := by
      have hjoin := R.joins j
      have hx : x = (R.link (j + 1)).entry := hcross.2.trans hjoin
      rw [hx]
      exact (R.link (j + 1)).entry_mem_support
    have hicomp := R.compatible i (j + 1) (by omega)
    simp only [CompatibleInOrder, hi, hnext] at hicomp
    have hxint := hicomp.2 (by omega) ⟨hxi, hxnext⟩
    exact (R.link i).not_mem_interior_entry'
      (hcross.1.symm ▸ hxint.1)
  · have hmid : (R.link (i + 1)).direction = .forward := by
      have halt := R.alternates i
      rw [hi] at halt
      cases h : (R.link (i + 1)).direction with
      | forward => rfl
      | backward => exact (halt h.symm).elim
    have hxmid : x ∈ (R.link (i + 1)).path.support := by
      have hjoin := R.joins i
      have hx : x = (R.link (i + 1)).entry := hcross.1.trans hjoin
      rw [hx]
      exact (R.link (i + 1)).entry_mem_support
    have hmidj : i + 1 < j := by
      have halt := R.alternates i
      by_contra hnot
      have heq : j = i + 1 := by omega
      subst j
      exact halt (hi.trans hj.symm)
    by_cases hadj : j = i + 2
    · have hjoin := R.joins (i + 1)
      have heq : (R.link (i + 1)).entry =
          (R.link (i + 1)).exit := by
        calc
          (R.link (i + 1)).entry = x :=
            (hcross.1.trans (R.joins i)).symm
          _ = (R.link j).entry := hcross.2
          _ = (R.link (i + 1)).exit := by
            rw [show i + 1 + 1 = j by omega] at hjoin
            exact hjoin.symm
      exact (R.link (i + 1)).entry_ne_exit heq
    · have hcomp := R.compatible (i + 1) j hmidj
      simp only [CompatibleInOrder, hmid, hj] at hcomp
      exact Set.disjoint_left.1 (hcomp.2 (by omega)) hxmid hxj

theorem InfiniteTrace.backward_support_disjoint
    {D : Digraph V} (R : InfiniteTrace D) {i j : ℕ}
    (hne : i ≠ j)
    (hi : (R.link i).direction = .backward)
    (hj : (R.link j).direction = .backward) :
    Disjoint (R.link i).path.support (R.link j).path.support := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact R.backward_support_disjoint_of_lt hij hi hj
  · exact (R.backward_support_disjoint_of_lt hji hj hi).symm

/-- Two backward links of a safe infinite trace cannot lie on the same
finite reference member.  If they did, order their starts on that member.
The safety interval forces the reference edge immediately after the first
link to be another backward edge, whose link then meets the first link at
its terminal vertex, contradicting disjointness of backward-link supports. -/
private theorem InfiniteTrace.not_backward_common_finite_owner_of_start_lt
    (R : InfiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hsafe : IsSafe Y (.infinite R))
    {i j : ℕ}
    (hi : (R.link i).direction = .backward)
    (hj : (R.link j).direction = .backward)
    {p : FinitePath Gamma.graph}
    (hpY : (Sum.inl p : Gamma.DPath) ∈ Y)
    (hpi : (R.link i).path.IsSubpathOf (.inl p))
    (hpj : (R.link j).path.IsSubpathOf (.inl p))
    (hne : i ≠ j)
    (hstartlt : p.walk.support.idxOf (R.link i).path.start <
      p.walk.support.idxOf (R.link j).path.start) : False := by
  classical
  have hdij := R.backward_support_disjoint hne hi hj
  let a := (R.link i).path.start
  let b := (R.link j).path.start
  have haP : a ∈ p.support := hpi.1 (R.link i).path.start_mem_support
  have hbP : b ∈ p.support := hpj.1 (R.link j).path.start_mem_support
  have hab : a ≠ b := by
    intro hab
    exact Set.disjoint_left.1 hdij
      (R.link i).path.start_mem_support
      (by simpa [a, b, hab] using (R.link j).path.start_mem_support)
  have habpos : p.walk.support.idxOf a < p.walk.support.idxOf b := by
    simpa [a, b] using hstartlt
  have hstartFinish : p.walk.support.idxOf a <
        p.walk.support.idxOf (R.link i).path.finish := by
      obtain ⟨t, hit⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish
        (R.link i).path (R.link i).path.start_mem_support
          (R.link i).nontrivial
      have hpos := FinitePath.edgeSet_eq_position_interval
        p (R.link i).path hpi
      have := (hpos ▸ hit).2.2
      simpa [a] using this
  have hfinishLe : p.walk.support.idxOf (R.link i).path.finish ≤
      p.walk.support.idxOf b := by
    by_contra hnot
    have hbetween : p.walk.support.idxOf a ≤
        p.walk.support.idxOf b ∧
        p.walk.support.idxOf b <
          p.walk.support.idxOf (R.link i).path.finish := ⟨habpos.le, by omega⟩
    obtain ⟨t, hjt⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish
      (R.link j).path (R.link j).path.start_mem_support
        (R.link j).nontrivial
    have hpos := FinitePath.edgeSet_eq_position_interval
      p (R.link i).path hpi
    have hjtP := hpj.2 hjt
    have hjtI : (b, t) ∈ (R.link i).path.edgeSet := by
      rw [hpos]
      exact ⟨hjtP, hbetween⟩
    exact Set.disjoint_left.1 hdij
      ((R.link i).path.edgeSet_subset_support_prod hjtI).1
      (R.link j).path.start_mem_support
  have hfinishP : (R.link i).path.finish ∈ p.walk.support :=
    hpi.1 (R.link i).path.finish_mem_support
  have hbIdx : p.walk.support.idxOf b < p.walk.support.length :=
    List.idxOf_lt_length_iff.mpr hbP
  have hfinishLt : p.walk.support.idxOf (R.link i).path.finish <
      p.walk.support.idxOf b := by
    apply lt_of_le_of_ne hfinishLe
    intro heq
    have hvertex : (R.link i).path.finish = b :=
      (List.idxOf_inj (l := p.walk.support) hfinishP).mp heq
    exact Set.disjoint_left.1 hdij
      (R.link i).path.finish_mem_support
      (by simpa [b, hvertex] using (R.link j).path.start_mem_support)
  let k := p.walk.support.idxOf (R.link i).path.finish
  have hk : k < p.walk.length := by
    have hlen := Walk.support_length_eq p.walk
    dsimp [k]
    omega
  let t := p.walk.support[k + 1]'(by
    rw [Walk.support_length_eq p.walk]
    omega)
  have hitP : ((R.link i).path.finish, t) ∈ p.edgeSet := by
    change _ ∈ p.walk.edgeSet
    rw [Walk.mem_edgeSet_iff_exists_getVert p.walk]
    refine ⟨k, hk, ?_⟩
    refine ⟨by rw [Walk.support_length_eq p.walk]; omega, ?_⟩
    apply Prod.ext
    · exact (List.getElem_idxOf
        (List.idxOf_lt_length_iff.mpr hfinishP)).symm
    · rfl
  obtain ⟨si, hisi⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish
    (R.link i).path (R.link i).path.start_mem_support
      (R.link i).nontrivial
  obtain ⟨sj, hjsj⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish
    (R.link j).path (R.link j).path.start_mem_support
      (R.link j).nontrivial
  have hisafe : (a, si) ∈
      (AltPath.infinite R).directionEdges .backward ∩ p.edgeSet := by
    constructor
    · simp only [AltPath.directionEdges, AltPath.links,
        InfiniteTrace.links, Set.mem_iUnion, Set.mem_range]
      exact ⟨R.link i, ⟨i, rfl⟩, hi, hisi⟩
    · exact hpi.2 hisi
  have hjsafe : (b, sj) ∈
      (AltPath.infinite R).directionEdges .backward ∩ p.edgeSet := by
    constructor
    · simp only [AltPath.directionEdges, AltPath.links,
        InfiniteTrace.links, Set.mem_iUnion, Set.mem_range]
      exact ⟨R.link j, ⟨j, rfl⟩, hj, hjsj⟩
    · exact hpj.2 hjsj
  have hitSafe : ((R.link i).path.finish, t) ∈
      (AltPath.infinite R).directionEdges .backward ∩ p.edgeSet := by
    apply IsEdgeInterval.mem_of_between_positions
      (hsafe.2.1 (.inl p) hpY) hisafe hjsafe hitP
    · exact hstartFinish.le
    · exact hfinishLe
  simp only [AltPath.directionEdges, Set.mem_inter_iff,
    Set.mem_iUnion] at hitSafe
  rcases hitSafe with ⟨⟨l, hklink, hkdir, hkit⟩, _⟩
  simp only [AltPath.links, InfiniteTrace.links, Set.mem_range] at hklink
  rcases hklink with ⟨k, rfl⟩
  by_cases hki : k = i
  · subst k
    exact FinitePath.no_outgoing_edge_at_finish (R.link i).path t hkit
  · have hdisj := R.backward_support_disjoint hki hkdir hi
    exact Set.disjoint_left.1 hdisj
      ((R.link k).path.edgeSet_subset_support_prod hkit).1
      (R.link i).path.finish_mem_support

/-- Two backward links of a safe infinite trace cannot lie on the same
finite reference member. -/
theorem InfiniteTrace.backward_indices_eq_of_common_finite_owner
    (R : InfiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hsafe : IsSafe Y (.infinite R))
    {i j : ℕ}
    (hi : (R.link i).direction = .backward)
    (hj : (R.link j).direction = .backward)
    {p : FinitePath Gamma.graph}
    (hpY : (Sum.inl p : Gamma.DPath) ∈ Y)
    (hpi : (R.link i).path.IsSubpathOf (.inl p))
    (hpj : (R.link j).path.IsSubpathOf (.inl p)) :
    i = j := by
  classical
  by_contra hne
  have hdij := R.backward_support_disjoint hne hi hj
  have hiP : (R.link i).path.start ∈ p.support :=
    hpi.1 (R.link i).path.start_mem_support
  have hjP : (R.link j).path.start ∈ p.support :=
    hpj.1 (R.link j).path.start_mem_support
  have hstartNe : (R.link i).path.start ≠ (R.link j).path.start := by
    intro h
    exact Set.disjoint_left.1 hdij
      (R.link i).path.start_mem_support
      (h ▸ (R.link j).path.start_mem_support)
  have hidxNe : p.walk.support.idxOf (R.link i).path.start ≠
      p.walk.support.idxOf (R.link j).path.start := by
    intro h
    exact hstartNe ((List.idxOf_inj (l := p.walk.support) hiP).mp h)
  rcases lt_or_gt_of_ne hidxNe with hlt | hgt
  · exact R.not_backward_common_finite_owner_of_start_lt
      hsafe hi hj hpY hpi hpj hne hlt
  · exact R.not_backward_common_finite_owner_of_start_lt
      hsafe hj hi hpY hpj hpi (Ne.symm hne) hgt

/-- Finite character supplies the finite owner required by the preceding
index-injectivity theorem. -/
theorem InfiniteTrace.backward_indices_eq_of_common_owner
    (R : InfiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hsafe : IsSafe Y (.infinite R))
    (hYfinite : Gamma.HasFiniteCharacter Y)
    {i j : ℕ}
    (hi : (R.link i).direction = .backward)
    (hj : (R.link j).direction = .backward)
    {p : Gamma.DPath} (hpY : p ∈ Y)
    (hpi : (R.link i).path.IsSubpathOf p)
    (hpj : (R.link j).path.IsSubpathOf p) :
    i = j := by
  obtain ⟨q, rfl⟩ := hYfinite hpY
  exact R.backward_indices_eq_of_common_finite_owner
    hsafe hi hj hpY hpi hpj

end Alternating
end Erdos599
