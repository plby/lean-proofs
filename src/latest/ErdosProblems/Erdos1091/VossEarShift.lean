/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossAttachments

/-!
# Replacing an attachment endpoint of an ear

The internal path and its length are unchanged when the first spoke is
replaced by a return edge. This operation is used in Voss's Cases 2 and 3.
-/

open SimpleGraph

namespace Erdos1091.Voss.Ear

variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- Change the presentation of the attachment set without changing the
underlying walk or either endpoint. -/
def changeSet (E : Ear G S) {T : Set V} (hST : ∀ v, v ∈ S ↔ v ∈ T) : Ear G T where
  start := E.start
  finish := E.finish
  walk := E.walk
  isPath := E.isPath
  start_mem := (hST E.start).mp E.start_mem
  finish_mem := (hST E.finish).mp E.finish_mem
  endpoints_ne := E.endpoints_ne
  only_ends := fun v hv hvT => E.only_ends v hv ((hST v).mpr hvT)

theorem start_notMem_tail (E : Ear G S) : E.start ∉ E.walk.tail.support := by
  rw [E.walk.support_tail_of_not_nil E.not_nil]
  have hn := E.isPath.support_nodup
  rw [← E.walk.cons_tail_support, List.nodup_cons] at hn
  exact hn.1

theorem mem_tail_attachment_eq_finish (E : Ear G S) {v : V}
    (hv : v ∈ E.walk.tail.support) (hvS : v ∈ S) : v = E.finish := by
  have hvTail : v ∈ E.walk.support.tail := by
    rwa [E.walk.support_tail_of_not_nil E.not_nil] at hv
  rcases E.only_ends v (List.mem_of_mem_tail hvTail) hvS with hvStart | hvFinish
  · exact (E.start_notMem_tail (hvStart ▸ hv)).elim
  · exact hvFinish

/-- Change the initial attachment, retaining the whole tail of the ear. -/
def replaceStart (E : Ear G S) {a : V} (ha : a ∈ S) (haf : a ≠ E.finish)
    (hadj : G.Adj a E.walk.snd) : Ear G S where
  start := a
  finish := E.finish
  walk := Walk.cons hadj E.walk.tail
  isPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_cons, List.nodup_cons]
    exact ⟨fun hv => haf (E.mem_tail_attachment_eq_finish hv ha), E.isPath.tail.support_nodup⟩
  start_mem := ha
  finish_mem := E.finish_mem
  endpoints_ne := haf
  only_ends := by
    intro v hv hvS
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (E.mem_tail_attachment_eq_finish hv hvS)

@[simp] theorem replaceStart_length (E : Ear G S) {a : V}
    (ha : a ∈ S) (haf : a ≠ E.finish) (hadj : G.Adj a E.walk.snd) :
    (E.replaceStart ha haf hadj).walk.length = E.walk.length := by
  have hlen := E.walk.length_tail_add_one E.not_nil
  simp only [replaceStart, Walk.length_cons]
  omega

theorem mem_tail_of_mem_ne_start (E : Ear G S) {v : V}
    (hv : v ∈ E.walk.support) (hvStart : v ≠ E.start) : v ∈ E.walk.tail.support := by
  rw [E.walk.support_tail_of_not_nil E.not_nil]
  exact ((Walk.mem_support_iff E.walk).mp hv).resolve_left hvStart

theorem mem_replaceStart_of_mem_ne_start (E : Ear G S) {a v : V}
    (ha : a ∈ S) (haf : a ≠ E.finish) (hadj : G.Adj a E.walk.snd)
    (hv : v ∈ E.walk.support) (hvStart : v ≠ E.start) :
    v ∈ (E.replaceStart ha haf hadj).walk.support :=
  List.mem_cons_of_mem _ (E.mem_tail_of_mem_ne_start hv hvStart)

@[simp] theorem replaceStart_snd (E : Ear G S) {a : V}
    (ha : a ∈ S) (haf : a ≠ E.finish) (hadj : G.Adj a E.walk.snd) :
    (E.replaceStart ha haf hadj).walk.snd = E.walk.snd := by
  simp [replaceStart]

theorem replaceStart_penultimate (E : Ear G S) (hlen : 2 ≤ E.walk.length) {a : V}
    (ha : a ∈ S) (haf : a ≠ E.finish) (hadj : G.Adj a E.walk.snd) :
    (E.replaceStart ha haf hadj).walk.penultimate = E.walk.penultimate := by
  have htail : ¬ E.walk.tail.Nil := by
    rw [Walk.not_nil_iff_lt_length, Walk.length_tail]
    omega
  calc
    _ = E.walk.tail.penultimate := Walk.penultimate_cons_of_not_nil _ _ htail
    _ = E.walk.penultimate := by
      have h := Walk.penultimate_cons_of_not_nil (E.walk.adj_snd E.not_nil) E.walk.tail htail
      rw [E.walk.cons_tail_eq E.not_nil] at h
      exact h.symm

theorem isChord_replaceStart (E : Ear G S) {a x y : V}
    (ha : a ∈ S) (haf : a ≠ E.finish) (hadj : G.Adj a E.walk.snd)
    (haE : a ∉ E.walk.support) (he : E.walk.IsChord s(x, y))
    (hxStart : x ≠ E.start) (hyStart : y ≠ E.start) :
    (E.replaceStart ha haf hadj).walk.IsChord s(x, y) := by
  obtain ⟨hxy, hnot, hx, hy⟩ := Walk.isChord_sym2Mk.mp he
  refine ⟨hxy, ?_, ?_, ?_⟩
  · intro hnew
    change s(x, y) ∈ s(a, E.walk.snd) :: E.walk.tail.edges at hnew
    rcases List.mem_cons.mp hnew with heq | htail
    · rcases Sym2.eq_iff.mp heq with ⟨hxa, _⟩ | ⟨_, hya⟩
      · exact haE (hxa ▸ hx)
      · exact haE (hya ▸ hy)
    · rw [Walk.edges_tail] at htail
      exact hnot (List.mem_of_mem_tail htail)
  · exact List.mem_cons_of_mem _ (E.mem_tail_of_mem_ne_start hx hxStart)
  · exact List.mem_cons_of_mem _ (E.mem_tail_of_mem_ne_start hy hyStart)

theorem old_start_notMem_replaceStart (E : Ear G S) {a : V}
    (ha : a ∈ S) (haf : a ≠ E.finish) (hadj : G.Adj a E.walk.snd) (has : a ≠ E.start) :
    E.start ∉ (E.replaceStart ha haf hadj).walk.support := by
  intro hv
  change E.start ∈ a :: E.walk.tail.support at hv
  rcases List.mem_cons.mp hv with heq | hv
  · exact has heq.symm
  · exact E.start_notMem_tail hv

/-- A new first attachment joined to a retained vertex other than the
first inner vertex gives a chord of the modified ear. -/
theorem isChord_from_new_start (E : Ear G S) {a x : V}
    (ha : a ∈ S) (haf : a ≠ E.finish) (hadj : G.Adj a E.walk.snd)
    (haE : a ∉ E.walk.support) (hx : x ∈ E.walk.support)
    (hxStart : x ≠ E.start) (hxSnd : x ≠ E.walk.snd) (hax : G.Adj a x) :
    (E.replaceStart ha haf hadj).walk.IsChord s(a, x) := by
  refine ⟨hax, ?_, List.mem_cons_self, ?_⟩
  · intro he
    change s(a, x) ∈ s(a, E.walk.snd) :: E.walk.tail.edges at he
    rcases List.mem_cons.mp he with heq | he
    · exact hxSnd ((Sym2.mkEmbedding a).injective heq)
    · have haTail := E.walk.tail.fst_mem_support_of_mem_edges he
      rw [E.walk.support_tail_of_not_nil E.not_nil] at haTail
      exact haE (List.mem_of_mem_tail haTail)
  · exact E.mem_replaceStart_of_mem_ne_start ha haf hadj hx hxStart

theorem isChord_reverse {a b : V} (p : G.Walk a b) {e : Sym2 V}
    (he : p.IsChord e) : p.reverse.IsChord e := by
  induction e using Sym2.ind with
  | _ x y =>
    simpa only [Walk.isChord_sym2Mk, Walk.edges_reverse, Walk.support_reverse,
      List.mem_reverse] using he

/-- Replace the final spoke, retaining the internal path of the ear. -/
def replaceFinish (E : Ear G S) {b : V} (hb : b ∈ S) (hbs : b ≠ E.start)
    (hadj : G.Adj E.walk.penultimate b) : Ear G S :=
  (E.reverse.replaceStart hb hbs (by
    simpa only [reverse, Walk.snd_reverse] using hadj.symm)).reverse

@[simp] theorem replaceFinish_length (E : Ear G S) {b : V}
    (hb : b ∈ S) (hbs : b ≠ E.start) (hadj : G.Adj E.walk.penultimate b) :
    (E.replaceFinish hb hbs hadj).walk.length = E.walk.length := by
  calc
    _ = (E.reverse.replaceStart hb hbs _).walk.length := Walk.length_reverse _
    _ = E.reverse.walk.length := E.reverse.replaceStart_length _ _ _
    _ = E.walk.length := Walk.length_reverse _

@[simp] theorem replaceFinish_penultimate (E : Ear G S) {b : V}
    (hb : b ∈ S) (hbs : b ≠ E.start) (hadj : G.Adj E.walk.penultimate b) :
    (E.replaceFinish hb hbs hadj).walk.penultimate = E.walk.penultimate := by
  calc
    _ = (E.reverse.replaceStart hb hbs _).walk.snd := Walk.penultimate_reverse _
    _ = E.reverse.walk.snd := E.reverse.replaceStart_snd _ _ _
    _ = E.walk.penultimate := Walk.snd_reverse _

theorem replaceFinish_snd (E : Ear G S) (hlen : 2 ≤ E.walk.length) {b : V}
    (hb : b ∈ S) (hbs : b ≠ E.start) (hadj : G.Adj E.walk.penultimate b) :
    (E.replaceFinish hb hbs hadj).walk.snd = E.walk.snd := by
  have hrlen : 2 ≤ E.reverse.walk.length := by simpa only [reverse, Walk.length_reverse] using hlen
  calc
    _ = (E.reverse.replaceStart hb hbs _).walk.penultimate := Walk.snd_reverse _
    _ = E.reverse.walk.penultimate := E.reverse.replaceStart_penultimate hrlen _ _ _
    _ = E.walk.snd := Walk.penultimate_reverse _

theorem mem_replaceFinish_of_mem_ne_finish (E : Ear G S) {b v : V}
    (hb : b ∈ S) (hbs : b ≠ E.start) (hadj : G.Adj E.walk.penultimate b)
    (hv : v ∈ E.walk.support) (hvFinish : v ≠ E.finish) :
    v ∈ (E.replaceFinish hb hbs hadj).walk.support := by
  have hvR : v ∈ E.reverse.walk.support := by
    simpa only [reverse, Walk.support_reverse, List.mem_reverse] using hv
  have hm := E.reverse.mem_replaceStart_of_mem_ne_start hb hbs
    (by simpa only [reverse, Walk.snd_reverse] using hadj.symm) hvR hvFinish
  change v ∈ (E.reverse.replaceStart hb hbs _).walk.reverse.support
  simpa only [Walk.support_reverse, List.mem_reverse] using hm

/-- An internal ear chord and an additional cross edge force the closed
cycle to be even under the odd-two-chord exclusion. -/
theorem even_append_of_chord_and_cross (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (q : G.Walk E.finish E.start) (hq : q.IsPath) (hqS : ∀ v ∈ q.support, v ∈ S)
    (hno : ¬ HasOddCycleWithTwoChords G) {e : Sym2 V}
    (he : E.walk.IsChord e) (heEnds : e ≠ s(E.start, E.finish)) {x y : V}
    (hx : x ∈ E.walk.support) (hxS : x ∉ S) (hy : y ∈ q.support)
    (hyStart : y ≠ E.start) (hyFinish : y ≠ E.finish) (hxy : G.Adj x y) :
    Even (E.walk.length + q.length) := by
  have hne : e ≠ s(x, y) := by
    intro heq
    have he' : E.walk.IsChord s(x, y) := heq ▸ he
    rcases E.only_ends y he'.2.2.2 (hqS y hy) with hyEq | hyEq
    · exact hyStart hyEq
    · exact hyFinish hyEq
  apply Nat.not_odd_iff_even.mp
  intro hodd
  apply hno
  exact ⟨E.start, E.walk.append q, E.isCycle_append hlen q hq hqS,
    by simpa only [Walk.length_append] using hodd, e, s(x, y), hne,
    E.isChord_append q hqS he heEnds,
    E.isChord_cross_append q hqS hx hxS hy hyStart hyFinish hxy⟩

end Erdos1091.Voss.Ear
