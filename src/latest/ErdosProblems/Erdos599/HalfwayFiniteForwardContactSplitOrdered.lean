/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteForwardContactSplitEndpoints
import ErdosProblems.Erdos599.SafeSwitching

/-!
# Consecutive contacts determine one finite forward piece

The all-contact split gives a list of directed subpaths.  This file records
the order-theoretic fact needed by the alternating-trace assembler: two
successive displayed contacts of the parent path are the endpoints of one
literal member of that list.  The statement is phrased using ambient support
positions, so a run-coordinate enumeration can apply it without rebuilding
the inductive construction of the split.
-/

noncomputable section

open Set

namespace Erdos599
namespace DirectedPath
namespace FinitePath

universe u

variable {V : Type u} {D : Digraph V}
variable {p : FinitePath D} {X : Set V}
variable [DecidableEq V]

namespace OrderedOccurrence

theorem left_mem_support {x y : V} (hxy : OrderedOccurrence p x y) :
    x ∈ p.support := by
  apply p.between_support_subset hxy
  simpa only [between_start] using (p.between hxy).start_mem_support

theorem right_mem_support {x y : V} (hxy : OrderedOccurrence p x y) :
    y ∈ p.support := by
  apply p.between_support_subset hxy
  simpa only [between_finish] using (p.between hxy).finish_mem_support

/-- An ordered occurrence is also strict in the numerical position order of
the parent support. -/
theorem idxOf_lt {x y : V} (hxy : OrderedOccurrence p x y) :
    p.walk.support.idxOf x < p.walk.support.idxOf y := by
  classical
  let q := p.between hxy
  have hqne : q.start ≠ q.finish := by
    simpa only [q, between_start, between_finish] using hxy.ne
  obtain ⟨z, hz⟩ :=
    Alternating.FinitePath.exists_edge_from_of_mem_of_ne_finish
      q q.start_mem_support hqne
  have hpos := Alternating.FinitePath.edgeSet_eq_position_interval
    p q (p.between_isSubpathOf hxy)
  rw [hpos] at hz
  simpa only [q, between_start, between_finish] using hz.2.2

private theorem idxOf_finish_eq_length (p : FinitePath D) :
    p.walk.support.idxOf p.finish = p.walk.length := by
  classical
  have hlast : p.walk.support[p.walk.length]'(by
      rw [Alternating.Walk.support_length_eq p.walk]
      omega) = p.finish :=
    Alternating.Walk.getElem_length_eq_end p.walk
  calc
    p.walk.support.idxOf p.finish =
        p.walk.support.idxOf
          (p.walk.support[p.walk.length]'(by
            rw [Alternating.Walk.support_length_eq p.walk]
            omega)) := by rw [hlast]
    _ = p.walk.length := by rw [p.isPath.idxOf_getElem]

theorem left_ne_finish {x y : V} (hxy : OrderedOccurrence p x y) :
    x ≠ p.finish := by
  classical
  intro hx
  have hlt := hxy.idxOf_lt
  have hylt : p.walk.support.idxOf y < p.walk.support.length :=
    List.idxOf_lt_length_iff.mpr hxy.right_mem_support
  rw [hx, idxOf_finish_eq_length p] at hlt
  rw [Alternating.Walk.support_length_eq p.walk] at hylt
  omega

end OrderedOccurrence

namespace ContactSplit

/-- A vertex whose parent position lies between the endpoints of a directed
child subpath belongs to that child. -/
private theorem mem_support_of_position_interval
    (q : FinitePath D) (hsub : q.IsSubpathOf (.inl p))
    {z : V} (hz : z ∈ p.support)
    (hlo : p.walk.support.idxOf q.start ≤ p.walk.support.idxOf z)
    (hhi : p.walk.support.idxOf z ≤ p.walk.support.idxOf q.finish) :
    z ∈ q.support := by
  classical
  by_cases hzf : z = q.finish
  · simpa only [hzf] using q.finish_mem_support
  have hlt : p.walk.support.idxOf z <
      p.walk.support.idxOf q.finish := by
    apply lt_of_le_of_ne hhi
    intro heq
    apply hzf
    exact (List.idxOf_inj (l := p.walk.support) hz).mp heq
  have hzNotFinish : z ≠ p.finish := by
    intro hzfinish
    have hqmem : q.finish ∈ p.support := hsub.1 q.finish_mem_support
    have hqbound : p.walk.support.idxOf q.finish <
        p.walk.support.length := List.idxOf_lt_length_iff.mpr hqmem
    have hpfinish : p.walk.support.idxOf p.finish = p.walk.length := by
      exact OrderedOccurrence.idxOf_finish_eq_length p
    rw [hzfinish, hpfinish] at hlt
    rw [Alternating.Walk.support_length_eq p.walk] at hqbound
    omega
  obtain ⟨t, hzt⟩ :=
    Alternating.FinitePath.exists_edge_from_of_mem_of_ne_finish
      p hz hzNotFinish
  have hpos := Alternating.FinitePath.edgeSet_eq_position_interval p q hsub
  have hztq : (z, t) ∈ q.edgeSet := by
    rw [hpos]
    exact ⟨hzt, hlo, hlt⟩
  exact (q.edgeSet_subset_support_prod hztq).1

private theorem piece_start_position_lt_finish
    (A : ContactSplit p X) {q : FinitePath D} (hq : q ∈ A.pieces) :
    p.walk.support.idxOf q.start < p.walk.support.idxOf q.finish := by
  classical
  obtain ⟨z, hz⟩ :=
    Alternating.FinitePath.exists_edge_from_of_mem_of_ne_finish
      q q.start_mem_support (A.nontrivial q hq)
  have hpos := Alternating.FinitePath.edgeSet_eq_position_interval
    p q (A.subpath q hq)
  rw [hpos] at hz
  exact hz.2.2

/-- Consecutive displayed break vertices of the parent path are the endpoints
of one literal split piece.  `hno` says precisely that there is no cutting
vertex at a parent-support position strictly between them. -/
theorem exists_piece_between (A : ContactSplit p X) {x y : V}
    (hxy : OrderedOccurrence p x y)
    (hxBreak : x = p.start ∨ x ∈ X)
    (hyBreak : y = p.finish ∨ y ∈ X)
    (hno : ∀ z ∈ p.support,
      p.walk.support.idxOf x < p.walk.support.idxOf z →
      p.walk.support.idxOf z < p.walk.support.idxOf y → z ∉ X) :
    ∃ q : {q : FinitePath D // q ∈ A.pieces},
      q.1.start = x ∧ q.1.finish = y := by
  classical
  have hxForStart : x ∈ p.support ∩ X ∨ x = p.start := by
    rcases hxBreak with hxStart | hxX
    · exact Or.inr hxStart
    · exact Or.inl ⟨hxy.left_mem_support, hxX⟩
  obtain ⟨q, hqx⟩ := A.exists_piece_start hxForStart hxy.left_ne_finish
  have hsub := A.subpath q.1 q.2
  have hqfinishP : q.1.finish ∈ p.support :=
    hsub.1 q.1.finish_mem_support
  have hqpos : p.walk.support.idxOf x <
      p.walk.support.idxOf q.1.finish := by
    simpa only [hqx] using A.piece_start_position_lt_finish q.2
  have hyP := hxy.right_mem_support
  have hxypos := hxy.idxOf_lt
  refine ⟨q, hqx, ?_⟩
  rcases lt_trichotomy
      (p.walk.support.idxOf q.1.finish)
      (p.walk.support.idxOf y) with hbefore | heq | hafter
  · rcases A.finish_contact q.1 q.2 with hparentFinish | hfinishX
    · have hybound : p.walk.support.idxOf y < p.walk.support.length :=
        List.idxOf_lt_length_iff.mpr hyP
      have hpfinish : p.walk.support.idxOf p.finish = p.walk.length :=
        OrderedOccurrence.idxOf_finish_eq_length p
      rw [hparentFinish, hpfinish] at hbefore
      rw [Alternating.Walk.support_length_eq p.walk] at hybound
      omega
    · exact (hno q.1.finish hqfinishP hqpos hbefore hfinishX).elim
  · exact (List.idxOf_inj (l := p.walk.support) hqfinishP).mp heq
  · have hyq : y ∈ q.1.support :=
      mem_support_of_position_interval q.1 hsub hyP
        (by simpa only [hqx] using hxypos.le) hafter.le
    rcases hyBreak with hyFinish | hyX
    · exact (finish_eq_of_parent_finish_mem hsub
          (hyFinish ▸ hyq)).trans hyFinish.symm
    · have hyEnds := A.endpoint_only q.1 q.2 ⟨hyq, hyX⟩
      have hyEnds' : y = q.1.start ∨ y = q.1.finish := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hyEnds
      rcases hyEnds' with hyStart | hyFinish
      · exact (hxy.ne (hqx.symm.trans hyStart.symm)).elim
      · exact hyFinish.symm

/-- A split piece ending at the parent finish is necessarily the last piece. -/
theorem eq_getLast_of_finish_eq (A : ContactSplit p X)
    {q : FinitePath D} (hq : q ∈ A.pieces) (hfinish : q.finish = p.finish) :
    q = A.pieces.getLast A.pieces_ne := by
  classical
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hq
  have hilast : i = A.pieces.length - 1 := by
    by_contra hine
    have hnext : i + 1 < A.pieces.length := by omega
    let r : FinitePath D := A.pieces[i + 1]
    have hr : r ∈ A.pieces := List.getElem_mem _
    have hchain := (List.isChain_iff_getElem.mp A.chain) i hnext
    have hrstart : r.start = p.finish := by
      calc
        r.start = A.pieces[i].finish := hchain.symm
        _ = q.finish := congrArg FinitePath.finish hget
        _ = p.finish := hfinish
    have hrfinish : r.finish = p.finish := by
      apply finish_eq_of_parent_finish_mem (A.subpath r hr)
      rw [← hrstart]
      exact r.start_mem_support
    exact A.nontrivial r hr (hrstart.trans hrfinish.symm)
  subst i
  calc
    q = A.pieces[A.pieces.length - 1] := hget.symm
    _ = A.pieces.getLast A.pieces_ne :=
      (List.getLast_eq_getElem A.pieces_ne).symm

/-- A split piece starting at the parent start is necessarily the first piece. -/
theorem eq_head_of_start_eq (A : ContactSplit p X)
    {q : FinitePath D} (hq : q ∈ A.pieces) (hstart : q.start = p.start) :
    q = A.pieces.head A.pieces_ne := by
  classical
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hq
  have hizero : i = 0 := by
    by_contra hine
    have hipos : 0 < i := by omega
    let r : FinitePath D := A.pieces[i - 1]
    have hr : r ∈ A.pieces := List.getElem_mem _
    have hadj : (i - 1) + 1 < A.pieces.length := by omega
    have hchain := (List.isChain_iff_getElem.mp A.chain) (i - 1) hadj
    have hrfinish : r.finish = p.start := by
      calc
        r.finish = A.pieces[(i - 1) + 1].start := hchain
        _ = A.pieces[i].start := by
          have hind : (i - 1) + 1 = i := by omega
          have hfin :
              (⟨(i - 1) + 1, hadj⟩ : Fin A.pieces.length) = ⟨i, hi⟩ :=
            Fin.ext hind
          exact congrArg FinitePath.start (congrArg A.pieces.get hfin)
        _ = q.start := congrArg FinitePath.start hget
        _ = p.start := hstart
    have hrstart : r.start = p.start := by
      apply start_eq_of_parent_start_mem (A.subpath r hr)
      rw [← hrfinish]
      exact r.finish_mem_support
    exact A.nontrivial r hr (hrstart.trans hrfinish.symm)
  subst i
  calc
    q = A.pieces[0] := hget.symm
    _ = A.pieces.head A.pieces_ne :=
      (List.head_eq_getElem A.pieces_ne).symm

/-- The final piece starts at the last displayed contact before the parent
finish. -/
theorem getLast_start_eq_of_consecutive_to_finish
    (A : ContactSplit p X) {x : V}
    (hx : OrderedOccurrence p x p.finish)
    (hxBreak : x = p.start ∨ x ∈ X)
    (hno : ∀ z ∈ p.support,
      p.walk.support.idxOf x < p.walk.support.idxOf z →
      p.walk.support.idxOf z < p.walk.support.idxOf p.finish → z ∉ X) :
    (A.pieces.getLast A.pieces_ne).start = x := by
  obtain ⟨q, hqstart, hqfinish⟩ :=
    A.exists_piece_between hx hxBreak (Or.inl rfl) hno
  have hqlast := A.eq_getLast_of_finish_eq q.2 hqfinish
  rw [← hqlast]
  exact hqstart

/-- The first piece finishes at the first displayed contact after the parent
start. -/
theorem head_finish_eq_of_consecutive_from_start
    (A : ContactSplit p X) {y : V}
    (hy : OrderedOccurrence p p.start y)
    (hyBreak : y = p.finish ∨ y ∈ X)
    (hno : ∀ z ∈ p.support,
      p.walk.support.idxOf p.start < p.walk.support.idxOf z →
      p.walk.support.idxOf z < p.walk.support.idxOf y → z ∉ X) :
    (A.pieces.head A.pieces_ne).finish = y := by
  obtain ⟨q, hqstart, hqfinish⟩ :=
    A.exists_piece_between hy (Or.inl rfl) hyBreak hno
  have hqhead := A.eq_head_of_start_eq q.2 hqstart
  rw [← hqhead]
  exact hqfinish

#print axioms exists_piece_between
#print axioms getLast_start_eq_of_consecutive_to_finish
#print axioms head_finish_eq_of_consecutive_from_start

end ContactSplit
end FinitePath
end DirectedPath
end Erdos599
