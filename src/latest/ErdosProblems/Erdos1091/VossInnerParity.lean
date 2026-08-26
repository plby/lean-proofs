/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossReturnParity

/-! # Ordering attachments by odd-cycle exclusion -/

open SimpleGraph

namespace Erdos1091.Voss.Ear

/-- An additional spoke cannot land on the rim arc of an odd cycle
already containing an internal ear chord. -/
theorem external_spoke_not_mem_odd_closure
    {V : Type*} {G : SimpleGraph V} {S : Set V}
    (E : Ear G S) (hlen : 2 ≤ E.walk.length) (hno : ¬ HasOddCycleWithTwoChords G)
    (q : G.Walk E.finish E.start) (hq : q.IsPath) (hqS : ∀ v ∈ q.support, v ∈ S)
    (hodd : Odd (E.walk.length + q.length)) {e : Sym2 V}
    (he : E.walk.IsChord e) (heEnds : e ≠ s(E.start, E.finish))
    {x d : V} (hx : x ∈ E.walk.support) (hxS : x ∉ S)
    (hdE : d ∉ E.walk.support) (hxd : G.Adj x d) : d ∉ q.support := by
  intro hdq
  have hds : d ≠ E.start := fun heq => hdE (by rw [heq]; exact E.walk.start_mem_support)
  have hdf : d ≠ E.finish := fun heq => hdE (by rw [heq]; exact E.walk.end_mem_support)
  have heven := E.even_append_of_chord_and_cross hlen q hq hqS hno he heEnds
    hx hxS hdq hds hdf hxd
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- If the complementary rim arc contains a spare spoke, its cycle is
even; hence the prefix arc closes the same ear to an odd cycle. -/
theorem odd_prefix_of_complement_spoke
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : C.IsCycle) (hodd : Odd C.length) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 2 ≤ E.walk.length)
    (hstart : E.start = z) {k j : ℕ} (hk : 0 < k) (hkN : k < C.length)
    (hfinish : C.getVert k = E.finish) (hkj : k ≤ j)
    {e : Sym2 V} (he : E.walk.IsChord e) (heEnds : e ≠ s(E.start, E.finish))
    {x : V} (hx : x ∈ E.walk.support) (hxC : x ∉ C.support)
    (hjE : C.getVert j ∉ E.walk.support) (hxd : G.Adj x (C.getVert j)) :
    Odd (E.walk.length + k) := by
  have hbase : C.getVert 0 = E.start := C.getVert_zero.trans hstart.symm
  let q := (CycleArc.wrap C k 0).copy hfinish hbase
  have hq : q.IsPath := (Walk.isPath_copy _ _ _).mpr (CycleArc.wrap_isPath C hC hk hkN)
  have hqsup : q.support = (CycleArc.wrap C k 0).support := Walk.support_copy _ _ _
  have hqC : ∀ v ∈ q.support, v ∈ C.support := by
    intro v hv
    exact CycleArc.wrap_support_subset C k 0 v (hqsup ▸ hv)
  have hdq : C.getVert j ∈ q.support := by
    rw [hqsup]
    exact CycleArc.getVert_mem_wrap_of_le C k 0 j hkj
  have hds : C.getVert j ≠ E.start := fun heq => hjE (by rw [heq]; exact E.walk.start_mem_support)
  have hdf : C.getVert j ≠ E.finish := fun heq => hjE (by rw [heq]; exact E.walk.end_mem_support)
  have heven := E.even_append_of_chord_and_cross hlen q hq hqC hno he heEnds
    hx hxC hdq hds hdf hxd
  have hqlen : q.length = C.length - k := by
    simp only [q, Walk.length_copy, CycleArc.wrap_length C k 0 (Nat.zero_le _), Nat.add_zero]
  rw [hqlen, Nat.even_iff] at heven
  rw [Nat.odd_iff] at hodd ⊢
  omega

/-- The same complement argument for a rim segment with arbitrary
indexed endpoints, rather than one based at the cycle's initial vertex. -/
theorem odd_segment_of_complement_spoke
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : C.IsCycle) (hodd : Odd C.length) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 2 ≤ E.walk.length)
    {i j k : ℕ} (hij : i < j) (hjN : j < C.length)
    (hstart : C.getVert i = E.start) (hfinish : C.getVert j = E.finish)
    (hk : k ≤ i ∨ j ≤ k)
    {e : Sym2 V} (he : E.walk.IsChord e) (heEnds : e ≠ s(E.start, E.finish))
    {x : V} (hx : x ∈ E.walk.support) (hxC : x ∉ C.support)
    (hkE : C.getVert k ∉ E.walk.support) (hxd : G.Adj x (C.getVert k)) :
    Odd (E.walk.length + (j - i)) := by
  let q := (CycleArc.wrap C j i).copy hfinish hstart
  have hq : q.IsPath := (Walk.isPath_copy _ _ _).mpr (CycleArc.wrap_isPath C hC hij hjN)
  have hqsup : q.support = (CycleArc.wrap C j i).support := Walk.support_copy _ _ _
  have hqC : ∀ v ∈ q.support, v ∈ C.support := by
    intro v hv
    exact CycleArc.wrap_support_subset C j i v (hqsup ▸ hv)
  have hdq : C.getVert k ∈ q.support := by
    rw [hqsup]
    rcases hk with hk | hk
    · exact CycleArc.getVert_mem_wrap_of_le_end C j i k hk
    · exact CycleArc.getVert_mem_wrap_of_le C j i k hk
  have hds : C.getVert k ≠ E.start := fun heq => hkE (by rw [heq]; exact E.walk.start_mem_support)
  have hdf : C.getVert k ≠ E.finish := fun heq => hkE (by rw [heq]; exact E.walk.end_mem_support)
  have heven := E.even_append_of_chord_and_cross hlen q hq hqC hno he heEnds
    hx hxC hdq hds hdf hxd
  have hqlen : q.length = C.length - j + i :=
    (Walk.length_copy _ _ _).trans (CycleArc.wrap_length C j i (by omega))
  rw [hqlen, Nat.even_iff] at heven
  rw [Nat.odd_iff] at hodd ⊢
  omega

/-- An odd segment closure excludes every additional spoke endpoint
from the entire closed index interval of that segment. -/
theorem external_spoke_index_not_between
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : C.IsCycle) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 2 ≤ E.walk.length)
    {i j k : ℕ} (hij : i ≤ j) (hjN : j < C.length)
    (hstart : C.getVert i = E.start) (hfinish : C.getVert j = E.finish)
    (hodd : Odd (E.walk.length + (j - i)))
    {e : Sym2 V} (he : E.walk.IsChord e) (heEnds : e ≠ s(E.start, E.finish))
    {x : V} (hx : x ∈ E.walk.support) (hxC : x ∉ C.support)
    (hkE : C.getVert k ∉ E.walk.support) (hxd : G.Adj x (C.getVert k)) :
    ¬ (i ≤ k ∧ k ≤ j) := by
  let p := Erdos1105.pathSegment C i j hij
  let q := p.reverse.copy hfinish hstart
  have hp : p.IsPath := CycleArc.segment_isPath C hC i j hij hjN
  have hq : q.IsPath := (Walk.isPath_copy _ _ _).mpr hp.reverse
  have hqsup : q.support = p.reverse.support := Walk.support_copy _ _ _
  have hqC : ∀ v ∈ q.support, v ∈ C.support := by
    intro v hv
    rw [hqsup, Walk.support_reverse, List.mem_reverse] at hv
    exact Erdos1105.pathSegment_support_subset C i j hij hjN.le hv
  have hqlen : q.length = j - i := by
    calc
      _ = p.length := (Walk.length_copy _ _ _).trans (Walk.length_reverse _)
      _ = _ := Erdos1105.pathSegment_length C i j hij hjN.le
  have hnot := E.external_spoke_not_mem_odd_closure hlen hno q hq hqC
    (by rwa [hqlen]) he heEnds hx hxC hkE hxd
  rintro ⟨hik, hkj⟩
  apply hnot
  rw [hqsup, Walk.support_reverse, List.mem_reverse]
  exact (Erdos1105.mem_pathSegment_support C i j hij hjN.le).mpr ⟨k, hik, hkj, rfl⟩

#print axioms external_spoke_not_mem_odd_closure
#print axioms odd_prefix_of_complement_spoke
#print axioms odd_segment_of_complement_spoke
#print axioms external_spoke_index_not_between

end Erdos1091.Voss.Ear
