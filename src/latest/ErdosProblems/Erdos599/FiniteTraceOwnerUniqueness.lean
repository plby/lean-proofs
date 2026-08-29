/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Backward-owner uniqueness in a finite safe trace

This is the finite companion to `InfiniteTraceOwnerUniqueness`.  The sole
extra boundary hypothesis is that the last link is forward.  For the
application-facing theorem this is derived from the more natural condition
that the terminal vertex lies outside the reference warp.
-/

noncomputable section

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

local instance finiteOwnerDecidableEq : DecidableEq V := Classical.decEq V

private theorem Link.not_mem_interior_entry_finite {D : Digraph V}
    (l : Link D) : l.entry ∉ l.interior := by
  intro h
  exact h.2 (by rw [l.endpoints_eq]; simp)

/-- A finite safe trace ending outside its reference warp has a forward last
link.  Indeed, the exit of a backward last link belongs to its reference
owner. -/
theorem FiniteTrace.last_direction_eq_forward_of_terminal_not_mem
    (R : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hsafe : IsSafe Y (.finite R))
    (hterminal : R.terminal ∉ Gamma.vertexSet Y) :
    R.lastLink.direction = .forward := by
  cases hdir : R.lastLink.direction with
  | forward => rfl
  | backward =>
      have hmem : R.lastLink ∈ (AltPath.finite R).links := by
        simpa [AltPath.links] using R.lastLink_mem_links
      obtain ⟨p, hpY, hsub⟩ := hsafe.1.2.1 R.lastLink hmem hdir
      exfalso
      apply hterminal
      change R.lastLink.exit ∈ Gamma.vertexSet Y
      refine ⟨p, hpY, hsub.1 ?_⟩
      change R.lastLink.exit ∈ R.lastLink.path.support
      exact R.lastLink.exit_mem_support

/-- Different backward links of a finite trace with a forward last link have
disjoint supports.  The forward terminal condition supplies the successor
of the later backward link needed to eliminate a crossed endpoint. -/
theorem FiniteTrace.backward_support_disjoint_of_lt
    {D : Digraph V} (R : FiniteTrace D)
    (hlast : R.lastLink.direction = .forward)
    {i j : Fin (R.lastIndex + 1)} (hij : i < j)
    (hi : (R.link i).direction = .backward)
    (hj : (R.link j).direction = .backward) :
    Disjoint (R.link i).path.support (R.link j).path.support := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hcompat := R.compatible i j hij
  simp only [CompatibleInOrder, hi, hj] at hcompat
  rcases hcompat hxi hxj with hcross | hcross
  · have hjlt : j.1 < R.lastIndex := by
      have hjle : j.1 ≤ R.lastIndex := by omega
      apply lt_of_le_of_ne hjle
      intro hjeq
      have hjlast : j = ⟨R.lastIndex, Nat.lt_succ_self _⟩ := Fin.ext hjeq
      have hbad : Direction.backward = Direction.forward := by
        calc
          .backward = (R.link j).direction := hj.symm
          _ = R.lastLink.direction := by rw [hjlast]; rfl
          _ = .forward := hlast
      cases hbad
    let j0 : Fin R.lastIndex := ⟨j.1, hjlt⟩
    let jnext : Fin (R.lastIndex + 1) := ⟨j.1 + 1, by omega⟩
    have hjoinNext : (R.link j).exit = (R.link jnext).entry := by
      simpa [j0, jnext] using R.joins j0
    have hnext : (R.link jnext).direction = .forward := by
      have halt := R.alternates j0
      have halt' : (R.link j).direction ≠ (R.link jnext).direction := by
        simpa [j0, jnext] using halt
      rw [hj] at halt'
      cases h : (R.link jnext).direction with
      | forward => rfl
      | backward => exact (halt' h.symm).elim
    have hxnext : x ∈ (R.link jnext).path.support := by
      have hx : x = (R.link jnext).entry := hcross.2.trans hjoinNext
      rw [hx]
      exact (R.link jnext).entry_mem_support
    have hinext : i < jnext := by
      change i.1 < jnext.1
      dsimp [jnext]
      omega
    have hicomp := R.compatible i jnext hinext
    simp only [CompatibleInOrder, hi, hnext] at hicomp
    have hxint := hicomp.2 (by
      intro hadj
      change jnext.1 = i.1 + 1 at hadj
      dsimp [jnext] at hadj
      omega) ⟨hxi, hxnext⟩
    exact (R.link i).not_mem_interior_entry_finite
      (hcross.1.symm ▸ hxint.1)
  · have hilt : i.1 < R.lastIndex := by omega
    let i0 : Fin R.lastIndex := ⟨i.1, hilt⟩
    let imid : Fin (R.lastIndex + 1) := ⟨i.1 + 1, by omega⟩
    have hjoinMid : (R.link i).exit = (R.link imid).entry := by
      simpa [i0, imid] using R.joins i0
    have hmid : (R.link imid).direction = .forward := by
      have halt := R.alternates i0
      have halt' : (R.link i).direction ≠ (R.link imid).direction := by
        simpa [i0, imid] using halt
      rw [hi] at halt'
      cases h : (R.link imid).direction with
      | forward => rfl
      | backward => exact (halt' h.symm).elim
    have hxmid : x ∈ (R.link imid).path.support := by
      have hx : x = (R.link imid).entry := hcross.1.trans hjoinMid
      rw [hx]
      exact (R.link imid).entry_mem_support
    have hmidj : imid < j := by
      have halt := R.alternates i0
      have halt' : (R.link i).direction ≠ (R.link imid).direction := by
        simpa [i0, imid] using halt
      by_contra hnot
      have heq : j = imid := by
        apply Fin.ext
        change j.1 = imid.1
        change ¬ imid.1 < j.1 at hnot
        dsimp [imid] at hnot ⊢
        omega
      have hjdir : (R.link imid).direction = .backward := by
        rw [← heq]
        exact hj
      exact halt' (hi.trans hjdir.symm)
    by_cases hadj : j.1 = imid.1 + 1
    · have hmidlt : imid.1 < R.lastIndex := by omega
      let mid0 : Fin R.lastIndex := ⟨imid.1, hmidlt⟩
      have hjoin := R.joins mid0
      have heq : (R.link imid).entry = (R.link imid).exit := by
        calc
          (R.link imid).entry = x :=
            (hcross.1.trans hjoinMid).symm
          _ = (R.link j).entry := hcross.2
          _ = (R.link imid).exit := by
            have hjoin' : (R.link imid).exit = (R.link j).entry := by
              have hcast : Fin.castSucc mid0 = imid := by
                apply Fin.ext
                rfl
              have hsucc : mid0.succ = j := by
                apply Fin.ext
                change imid.1 + 1 = j.1
                omega
              rw [← hcast, ← hsucc]
              exact hjoin
            exact hjoin'.symm
      exact (R.link imid).entry_ne_exit heq
    · have hcomp := R.compatible imid j hmidj
      simp only [CompatibleInOrder, hmid, hj] at hcomp
      exact Set.disjoint_left.1 (hcomp.2 hadj) hxmid hxj

theorem FiniteTrace.backward_support_disjoint
    {D : Digraph V} (R : FiniteTrace D)
    (hlast : R.lastLink.direction = .forward)
    {i j : Fin (R.lastIndex + 1)} (hne : i ≠ j)
    (hi : (R.link i).direction = .backward)
    (hj : (R.link j).direction = .backward) :
    Disjoint (R.link i).path.support (R.link j).path.support := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact R.backward_support_disjoint_of_lt hlast hij hi hj
  · exact (R.backward_support_disjoint_of_lt hlast hji hj hi).symm

private theorem FiniteTrace.not_backward_common_finite_owner_of_start_lt
    (R : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hsafe : IsSafe Y (.finite R))
    (hlast : R.lastLink.direction = .forward)
    {i j : Fin (R.lastIndex + 1)}
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
  have hdij := R.backward_support_disjoint hlast hne hi hj
  let a := (R.link i).path.start
  let b := (R.link j).path.start
  have haP : a ∈ p.support := hpi.1 (R.link i).path.start_mem_support
  have hbP : b ∈ p.support := hpj.1 (R.link j).path.start_mem_support
  have habpos : p.walk.support.idxOf a < p.walk.support.idxOf b := by
    simpa [a, b] using hstartlt
  have hstartFinish : p.walk.support.idxOf a <
      p.walk.support.idxOf (R.link i).path.finish := by
    obtain ⟨t, hit⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish
      (R.link i).path (R.link i).path.start_mem_support
        (R.link i).nontrivial
    have hpos := FinitePath.edgeSet_eq_position_interval
      p (R.link i).path hpi
    have h := (hpos ▸ hit).2.2
    simpa [a] using h
  have hfinishLe : p.walk.support.idxOf (R.link i).path.finish ≤
      p.walk.support.idxOf b := by
    by_contra hnot
    have hbetween : p.walk.support.idxOf a ≤ p.walk.support.idxOf b ∧
        p.walk.support.idxOf b <
          p.walk.support.idxOf (R.link i).path.finish :=
      ⟨habpos.le, by omega⟩
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
      (AltPath.finite R).directionEdges .backward ∩ p.edgeSet := by
    constructor
    · simp only [AltPath.directionEdges, AltPath.links,
        FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
      exact ⟨R.link i, ⟨i, rfl⟩, hi, hisi⟩
    · exact hpi.2 hisi
  have hjsafe : (b, sj) ∈
      (AltPath.finite R).directionEdges .backward ∩ p.edgeSet := by
    constructor
    · simp only [AltPath.directionEdges, AltPath.links,
        FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
      exact ⟨R.link j, ⟨j, rfl⟩, hj, hjsj⟩
    · exact hpj.2 hjsj
  have hitSafe : ((R.link i).path.finish, t) ∈
      (AltPath.finite R).directionEdges .backward ∩ p.edgeSet := by
    apply IsEdgeInterval.mem_of_between_positions
      (hsafe.2.1 (.inl p) hpY) hisafe hjsafe hitP
    · exact hstartFinish.le
    · exact hfinishLe
  simp only [AltPath.directionEdges, Set.mem_inter_iff,
    Set.mem_iUnion] at hitSafe
  rcases hitSafe with ⟨⟨l, hklink, hkdir, hkit⟩, _⟩
  simp only [AltPath.links, FiniteTrace.links, Set.mem_range] at hklink
  rcases hklink with ⟨q, rfl⟩
  by_cases hqi : q = i
  · subst q
    exact FinitePath.no_outgoing_edge_at_finish (R.link i).path t hkit
  · have hdisj := R.backward_support_disjoint hlast hqi hkdir hi
    exact Set.disjoint_left.1 hdisj
      ((R.link q).path.edgeSet_subset_support_prod hkit).1
      (R.link i).path.finish_mem_support

/-- Two backward links of a finite safe trace with forward final direction
cannot lie on the same finite reference member. -/
theorem FiniteTrace.backward_indices_eq_of_common_finite_owner_of_last_forward
    (R : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hsafe : IsSafe Y (.finite R))
    (hlast : R.lastLink.direction = .forward)
    {i j : Fin (R.lastIndex + 1)}
    (hi : (R.link i).direction = .backward)
    (hj : (R.link j).direction = .backward)
    {p : FinitePath Gamma.graph}
    (hpY : (Sum.inl p : Gamma.DPath) ∈ Y)
    (hpi : (R.link i).path.IsSubpathOf (.inl p))
    (hpj : (R.link j).path.IsSubpathOf (.inl p)) :
    i = j := by
  classical
  by_contra hne
  have hdij := R.backward_support_disjoint hlast hne hi hj
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
      hsafe hlast hi hj hpY hpi hpj hne hlt
  · exact R.not_backward_common_finite_owner_of_start_lt
      hsafe hlast hj hi hpY hpj hpi (Ne.symm hne) hgt

/-- Application-facing finite owner injectivity: terminal outside the
reference warp supplies the necessary forward final direction, and finite
character supplies a finite common owner. -/
theorem FiniteTrace.backward_indices_eq_of_common_owner
    (R : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hsafe : IsSafe Y (.finite R))
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hterminal : R.terminal ∉ Gamma.vertexSet Y)
    {i j : Fin (R.lastIndex + 1)}
    (hi : (R.link i).direction = .backward)
    (hj : (R.link j).direction = .backward)
    {p : Gamma.DPath} (hpY : p ∈ Y)
    (hpi : (R.link i).path.IsSubpathOf p)
    (hpj : (R.link j).path.IsSubpathOf p) :
    i = j := by
  obtain ⟨q, rfl⟩ := hYfinite hpY
  exact R.backward_indices_eq_of_common_finite_owner_of_last_forward
    hsafe (R.last_direction_eq_forward_of_terminal_not_mem hsafe hterminal)
      hi hj hpY hpi hpj

end Alternating
end Erdos599
