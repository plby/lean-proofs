/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossReturnClassification

/-! # The chordless inner cycle in Voss's remaining case -/

open SimpleGraph

namespace Erdos1091.Voss.Ear

variable {V : Type*} {G : SimpleGraph V} {S : Set V}

theorem snd_dropLast (E : Ear G S) (hlen : 2 ≤ E.walk.length) :
    E.walk.dropLast.snd = E.walk.snd :=
  Walk.getVert_dropLast (p := E.walk) (by omega : 1 < E.walk.length)

/-- Delete the two spokes of the ear. -/
def innerPath (E : Ear G S) (hlen : 2 ≤ E.walk.length) :
    G.Walk E.walk.snd E.walk.penultimate :=
  E.walk.dropLast.tail.copy (E.snd_dropLast hlen) rfl

theorem innerPath_isPath (E : Ear G S) (hlen : 2 ≤ E.walk.length) :
    (E.innerPath hlen).IsPath :=
  (Walk.isPath_copy _ _ _).mpr E.isPath.dropLast.tail

theorem innerPath_length (E : Ear G S) (hlen : 2 ≤ E.walk.length) :
    (E.innerPath hlen).length = E.walk.length - 2 := by
  simp only [innerPath, Walk.length_copy, Walk.length_tail, Walk.length_dropLast]
  omega

theorem innerPath_edges_subset (E : Ear G S) (hlen : 2 ≤ E.walk.length) :
    (E.innerPath hlen).edges ⊆ E.walk.edges := by
  intro e he
  rw [innerPath, Walk.edges_copy, Walk.edges_tail] at he
  have he' := List.mem_of_mem_tail he
  change e ∈ (E.walk.take (E.walk.length - 1)).edges at he'
  rw [Walk.edges_take] at he'
  exact List.mem_of_mem_take he'

theorem innerPath_support_subset (E : Ear G S) (hlen : 2 ≤ E.walk.length) :
    (E.innerPath hlen).support ⊆ E.walk.support := by
  intro v hv
  rw [innerPath, Walk.support_copy] at hv
  have hn : ¬ E.walk.dropLast.Nil := by
    rw [Walk.not_nil_iff_lt_length, Walk.length_dropLast]
    omega
  rw [Walk.support_tail_of_not_nil _ hn] at hv
  have hv' := List.mem_of_mem_tail hv
  change v ∈ (E.walk.take (E.walk.length - 1)).support at hv'
  rw [Walk.support_take] at hv'
  exact List.mem_of_mem_take hv'

theorem innerPath_notMem (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    {v : V} (hv : v ∈ (E.innerPath hlen).support) : v ∉ S := by
  intro hvS
  have hvTail : v ∈ E.walk.dropLast.tail.support := by
    simpa only [innerPath, Walk.support_copy] using hv
  have hn : ¬ E.walk.dropLast.Nil := by
    rw [Walk.not_nil_iff_lt_length, Walk.length_dropLast]
    omega
  rw [Walk.support_tail_of_not_nil _ hn] at hvTail
  have hvDrop := List.mem_of_mem_tail hvTail
  have hvStart := (E.dropLastPath hlen).only_start v hvDrop hvS
  change v = E.start at hvStart
  have hnodup := E.isPath.dropLast.support_nodup
  rw [← E.walk.dropLast.cons_tail_support, List.nodup_cons] at hnodup
  exact hnodup.1 (hvStart ▸ hvTail)

/-- The closing chord followed by the reversed internal path. -/
def innerCycle (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (hxy : G.Adj E.walk.snd E.walk.penultimate) : G.Walk E.walk.snd E.walk.snd :=
  Walk.cons hxy (E.innerPath hlen).reverse

theorem innerCycle_isCycle (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (he : E.walk.IsChord s(E.walk.snd, E.walk.penultimate)) :
    (E.innerCycle hlen (Walk.isChord_sym2Mk.mp he).1).IsCycle := by
  apply (Walk.cons_isCycle_iff _ _).mpr
  refine ⟨(E.innerPath_isPath hlen).reverse, ?_⟩
  intro hmem
  rw [Walk.edges_reverse, List.mem_reverse] at hmem
  exact he.2.1 (E.innerPath_edges_subset hlen hmem)

theorem innerCycle_length (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (hxy : G.Adj E.walk.snd E.walk.penultimate) :
    (E.innerCycle hlen hxy).length = E.walk.length - 1 := by
  simp only [innerCycle, Walk.length_cons, Walk.length_reverse, E.innerPath_length]
  omega

theorem innerCycle_snd (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (hxy : G.Adj E.walk.snd E.walk.penultimate) :
    (E.innerCycle hlen hxy).snd = E.walk.penultimate := by
  simp [innerCycle]

theorem innerCycle_support_subset (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (hxy : G.Adj E.walk.snd E.walk.penultimate) :
    (E.innerCycle hlen hxy).support ⊆ E.walk.support := by
  intro v hv
  simp only [innerCycle, Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse] at hv
  rcases hv with rfl | hv
  · exact E.walk.getVert_mem_support 1
  · exact E.innerPath_support_subset hlen hv

theorem innerCycle_notMem (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (hxy : G.Adj E.walk.snd E.walk.penultimate)
    {v : V} (hv : v ∈ (E.innerCycle hlen hxy).support) : v ∉ S := by
  simp only [innerCycle, Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse] at hv
  rcases hv with rfl | hv
  · exact E.snd_notMem hlen
  · exact E.innerPath_notMem hlen hv

/-- The original ear consists of its two spokes and the internal path. -/
theorem edges_eq_spokes_innerPath (E : Ear G S) (hlen : 2 ≤ E.walk.length) :
    E.walk.edges = s(E.start, E.walk.snd) ::
      ((E.innerPath hlen).edges ++ [s(E.walk.penultimate, E.finish)]) := by
  have hn : ¬ E.walk.dropLast.Nil := by
    rw [Walk.not_nil_iff_lt_length, Walk.length_dropLast]
    omega
  have hfirst := congrArg (fun p : G.Walk E.start E.walk.penultimate => p.edges)
    (E.walk.dropLast.cons_tail_eq hn)
  have hlast : E.walk.edges = E.walk.dropLast.edges ++ [s(E.walk.penultimate, E.finish)] := by
    calc
      _ = (E.walk.dropLast.concat (E.walk.adj_penultimate E.not_nil)).edges := by
        rw [Walk.concat_dropLast]
      _ = _ := by simpa only [List.concat_eq_append] using Walk.edges_concat _ _
  rw [hlast, ← hfirst]
  simp only [Walk.edges_cons, E.snd_dropLast hlen, innerPath, Walk.edges_copy, List.cons_append]

/-- An additional inner-cycle chord would be a second internal ear
chord, so the inner cycle is chordless. -/
theorem innerCycle_isChordless {z : V} (C : G.Walk z z) (hC : C.IsCycle)
    (hodd : Odd C.length) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 2 ≤ E.walk.length)
    (he : E.walk.IsChord s(E.walk.snd, E.walk.penultimate)) :
    (E.innerCycle hlen (Walk.isChord_sym2Mk.mp he).1).IsChordless := by
  intro e heCycle
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hxy, hnot, hx, hy⟩ := Walk.isChord_sym2Mk.mp heCycle
    have hxS := E.innerCycle_notMem hlen _ hx
    have hyS := E.innerCycle_notMem hlen _ hy
    have hnotE : s(x, y) ∉ E.walk.edges := by
      intro hm
      rw [E.edges_eq_spokes_innerPath hlen, List.mem_cons, List.mem_append,
        List.mem_singleton] at hm
      rcases hm with heq | hm | heq
      · rcases Sym2.eq_iff.mp heq with ⟨hxa, _⟩ | ⟨_, hya⟩
        · exact hxS (hxa ▸ E.start_mem)
        · exact hyS (hya ▸ E.start_mem)
      · apply hnot
        change s(x, y) ∈ s(E.walk.snd, E.walk.penultimate) :: (E.innerPath hlen).reverse.edges
        exact List.mem_cons_of_mem _ (by simpa only [Walk.edges_reverse, List.mem_reverse] using hm)
      · rcases Sym2.eq_iff.mp heq with ⟨_, hyb⟩ | ⟨hxb, _⟩
        · exact hyS (hyb ▸ E.finish_mem)
        · exact hxS (hxb ▸ E.finish_mem)
    have heE : E.walk.IsChord s(x, y) :=
      ⟨hxy, hnotE, E.innerCycle_support_subset hlen _ hx, E.innerCycle_support_subset hlen _ hy⟩
    have heq := E.chords_eq_of_no_odd_two_chords C hC hodd hno hlen heE he
      (E.edge_ne_endpoints_of_notMem hxS) (E.edge_ne_endpoints_of_notMem (E.snd_notMem hlen))
    apply hnot
    rw [heq]
    exact List.mem_cons_self

/-- A rim neighbour of any other inner vertex is a genuinely new
attachment, different from both original ear endpoints. -/
theorem inner_vertex_rim_neighbor_notMem {z : V} (C : G.Walk z z) (hC : C.IsCycle)
    (hodd : Odd C.length) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 2 ≤ E.walk.length)
    (he : E.walk.IsChord s(E.walk.snd, E.walk.penultimate))
    {v a : V} (hv : v ∈ E.walk.support) (hvC : v ∉ C.support)
    (hvX : v ≠ E.walk.snd) (hvY : v ≠ E.walk.penultimate)
    (haC : a ∈ C.support) (hva : G.Adj v a) : a ∉ E.walk.support := by
  intro haE
  have hnot : s(v, a) ∉ E.walk.edges := by
    intro hm
    rcases E.only_ends a haE haC with ha | ha
    · have hm' : s(E.start, v) ∈ E.walk.edges := by simpa only [ha, Sym2.eq_swap] using hm
      exact hvX (E.isPath.eq_snd_of_mem_edges hm')
    · have hm' : s(E.finish, v) ∈ E.walk.edges := by simpa only [ha, Sym2.eq_swap] using hm
      exact hvY (E.isPath.eq_penultimate_of_mem_edges hm')
  exact no_new_chord_at_other_vertex C hC hodd hno E hlen he
    (E.edge_ne_endpoints_of_notMem (E.snd_notMem hlen)) hv hvC
    (by simpa only [Sym2.mem_iff, not_or] using And.intro hvX hvY) haE hva hnot

#print axioms innerCycle_isChordless

end Erdos1091.Voss.Ear

namespace Erdos1091.Voss.CycleArc

variable {V : Type*} {G : SimpleGraph V} {z : V}

/-- Traverse the entire cycle except for the forward edge `i,i+1`. -/
def avoidingEdge (C : G.Walk z z) (i : ℕ) :
    G.Walk (C.getVert i) (C.getVert (i + 1)) :=
  (wrap C (i + 1) i).reverse

theorem avoidingEdge_isPath (C : G.Walk z z) (hC : C.IsCycle) {i : ℕ}
    (hi : i + 1 < C.length) : (avoidingEdge C i).IsPath :=
  (wrap_isPath C hC (Nat.lt_succ_self i) hi).reverse

theorem avoidingEdge_length (C : G.Walk z z) {i : ℕ} (hi : i + 1 < C.length) :
    (avoidingEdge C i).length + 1 = C.length := by
  rw [avoidingEdge, Walk.length_reverse, wrap_length C (i + 1) i (by omega)]
  omega

theorem avoidingEdge_support (C : G.Walk z z) (i : ℕ) (v : V) :
    v ∈ (avoidingEdge C i).support ↔ v ∈ C.support := by
  rw [avoidingEdge, Walk.support_reverse, List.mem_reverse]
  constructor
  · exact wrap_support_subset C (i + 1) i v
  · intro hv
    obtain ⟨k, hk, _⟩ := Walk.mem_support_iff_exists_getVert.mp hv
    rw [← hk]
    by_cases hki : k ≤ i
    · exact getVert_mem_wrap_of_le_end C (i + 1) i k hki
    · exact getVert_mem_wrap_of_le C (i + 1) i k (by omega)

/-- Prepend one attachment spoke to the traversal omitting the next
cycle edge. This has the full inner-cycle length. -/
def spokePath {S : Set V} (C : G.Walk z z) (hC : C.IsCycle)
    (hCS : ∀ v ∈ C.support, v ∉ S) {i : ℕ} (hi : i + 1 < C.length)
    {a : V} (ha : a ∈ S) (hadj : G.Adj a (C.getVert i)) : AttachmentPath G S where
  start := a
  finish := C.getVert (i + 1)
  walk := Walk.cons hadj (avoidingEdge C i)
  isPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_cons, List.nodup_cons]
    exact ⟨fun hm => hCS a ((avoidingEdge_support C i a).mp hm) ha,
      (avoidingEdge_isPath C hC hi).support_nodup⟩
  start_mem := ha
  finish_notMem := hCS _ (C.getVert_mem_support _)
  only_start := by
    intro v hv hvS
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with hv | hv
    · exact hv
    · exact (hCS v ((avoidingEdge_support C i v).mp hv) hvS).elim

theorem spokePath_length {S : Set V} (C : G.Walk z z) (hC : C.IsCycle)
    (hCS : ∀ v ∈ C.support, v ∉ S) {i : ℕ} (hi : i + 1 < C.length)
    {a : V} (ha : a ∈ S) (hadj : G.Adj a (C.getVert i)) :
    (spokePath C hC hCS hi ha hadj).walk.length = C.length := by
  change (avoidingEdge C i).length + 1 = C.length
  exact avoidingEdge_length C hi

/-- A chordless inner cycle of maximum attachment-path length propagates
an attachment from one vertex to its successor. -/
theorem exists_next_attachment [Fintype V] [DecidableRel G.Adj] {S : Set V}
    (C : G.Walk z z) (hC : C.IsCycle) (hchordless : C.IsChordless)
    (hCS : ∀ v ∈ C.support, v ∉ S)
    (hmax : ∀ P : AttachmentPath G S, P.walk.length ≤ C.length)
    {i : ℕ} (hi : i + 1 < C.length) (hdegree : 3 ≤ G.degree (C.getVert (i + 1)))
    {a : V} (ha : a ∈ S) (hadj : G.Adj a (C.getVert i)) :
    ∃ b, G.Adj (C.getVert (i + 1)) b ∧ b ∈ S := by
  classical
  let P := spokePath C hC hCS hi ha hadj
  have hPlen : P.walk.length = C.length := spokePath_length C hC hCS hi ha hadj
  have hPmax : ∀ Q : AttachmentPath G S, Q.walk.length ≤ P.walk.length := by
    intro Q
    rw [hPlen]
    exact hmax Q
  by_contra h
  push Not at h
  obtain ⟨b, hb⟩ := exists_chord_at_of_three_le_degree C hC (C.getVert_mem_support _)
    hdegree (by
      intro w hw
      rcases P.neighbor_mem_of_longest hPmax hw with hwP | hwS
      · change w ∈ a :: (avoidingEdge C i).support at hwP
        rcases List.mem_cons.mp hwP with heq | hm
        · exact (h w hw (heq ▸ ha)).elim
        · exact (avoidingEdge_support C i w).mp hm
      · exact (h w hw hwS).elim)
  exact hchordless hb

/-- Close a cycle traversal with a second, distinct attachment spoke. -/
def spokeEar {S : Set V} (C : G.Walk z z) (hC : C.IsCycle)
    (hCS : ∀ v ∈ C.support, v ∉ S) {i : ℕ} (hi : i + 1 < C.length)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (haC : G.Adj a (C.getVert i)) (hCb : G.Adj (C.getVert (i + 1)) b) : Ear G S :=
  (spokePath C hC hCS hi ha haC).close hCb (by
    intro hm
    have heq := (spokePath C hC hCS hi ha haC).only_start b hm hb
    exact hba heq) hb

theorem spokeEar_length {S : Set V} (C : G.Walk z z) (hC : C.IsCycle)
    (hCS : ∀ v ∈ C.support, v ∉ S) {i : ℕ} (hi : i + 1 < C.length)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (haC : G.Adj a (C.getVert i)) (hCb : G.Adj (C.getVert (i + 1)) b) :
    (spokeEar C hC hCS hi ha hb hba haC hCb).walk.length = C.length + 1 := by
  exact (Walk.length_concat (spokePath C hC hCS hi ha haC).walk hCb).trans
    (congrArg (· + 1) (spokePath_length C hC hCS hi ha haC))

theorem spokeEar_penultimate {S : Set V} (C : G.Walk z z) (hC : C.IsCycle)
    (hCS : ∀ v ∈ C.support, v ∉ S) {i : ℕ} (hi : i + 1 < C.length)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (haC : G.Adj a (C.getVert i)) (hCb : G.Adj (C.getVert (i + 1)) b) :
    (spokeEar C hC hCS hi ha hb hba haC hCb).walk.penultimate = C.getVert (i + 1) :=
  Walk.penultimate_concat _ _

theorem spokeEar_snd {S : Set V} (C : G.Walk z z) (hC : C.IsCycle)
    (hCS : ∀ v ∈ C.support, v ∉ S) {i : ℕ} (hi : i + 1 < C.length)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (haC : G.Adj a (C.getVert i)) (hCb : G.Adj (C.getVert (i + 1)) b) :
    (spokeEar C hC hCS hi ha hb hba haC hCb).walk.snd = C.getVert i := by
  simp [spokeEar, AttachmentPath.close, spokePath, Walk.concat]

theorem mem_spokeEar_of_mem_cycle {S : Set V} (C : G.Walk z z) (hC : C.IsCycle)
    (hCS : ∀ v ∈ C.support, v ∉ S) {i : ℕ} (hi : i + 1 < C.length)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (haC : G.Adj a (C.getVert i)) (hCb : G.Adj (C.getVert (i + 1)) b)
    {v : V} (hv : v ∈ C.support) :
    v ∈ (spokeEar C hC hCS hi ha hb hba haC hCb).walk.support := by
  have hm : v ∈ (spokePath C hC hCS hi ha haC).walk.support :=
    List.mem_cons_of_mem _ ((avoidingEdge_support C i v).mpr hv)
  exact (Walk.support_concat (spokePath C hC hCS hi ha haC).walk hCb).symm ▸
    List.mem_append_left [b] hm

#print axioms exists_next_attachment

end Erdos1091.Voss.CycleArc

namespace Erdos1091.Voss.Ear

/-- The first propagation step gives a third attachment distinct from
both endpoints of the original maximum ear. -/
theorem innerCycle_third_attachment
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v)
    (he : E.walk.IsChord s(E.walk.snd, E.walk.penultimate)) :
    ∃ a, G.Adj ((E.innerCycle (by omega) (Walk.isChord_sym2Mk.mp he).1).getVert 2) a ∧
      a ∈ C.support ∧ a ∉ E.walk.support := by
  let D := E.innerCycle (by omega : 2 ≤ E.walk.length) (Walk.isChord_sym2Mk.mp he).1
  have hD : D.IsCycle := E.innerCycle_isCycle (by omega) he
  have hDchordless : D.IsChordless := E.innerCycle_isChordless C hC.1 hC.2.1 hno (by omega) he
  have hDlen : D.length = E.walk.length - 1 := E.innerCycle_length _ _
  have hDthree := hD.three_le_length
  have hDout : ∀ v ∈ D.support, v ∉ C.support := fun v hv => E.innerCycle_notMem _ _ hv
  have hDmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length ≤ D.length := by
    intro P
    have hP := hmax P
    omega
  have hBY : G.Adj E.finish (D.getVert 1) := by
    change G.Adj E.finish D.snd
    rw [E.innerCycle_snd]
    exact (E.walk.adj_penultimate E.not_nil).symm
  obtain ⟨a, haAdj, haC⟩ := CycleArc.exists_next_attachment D hD hDchordless hDout
    hDmax (i := 1) (by omega) (hdegree _) E.finish_mem hBY
  refine ⟨a, haAdj, haC, ?_⟩
  have hZX : D.getVert 2 ≠ E.walk.snd := by
    intro heq
    have hi := (hD.getVert_endpoint_iff (by omega : 2 ≤ D.length)).mp heq
    omega
  have hZY : D.getVert 2 ≠ E.walk.penultimate := by
    intro heq
    have hY : D.getVert 1 = E.walk.penultimate := E.innerCycle_snd _ _
    have hi : 2 = 1 := hD.getVert_injOn' (show 2 ≤ D.length - 1 by omega)
      (show 1 ≤ D.length - 1 by omega) (heq.trans hY.symm)
    omega
  exact E.inner_vertex_rim_neighbor_notMem C hC.1 hC.2.1 hno (by omega) he
    (E.innerCycle_support_subset _ _ (D.getVert_mem_support 2))
    (hDout _ (D.getVert_mem_support 2)) hZX hZY haC haAdj

/-- If the inner cycle has at least four vertices, propagation once
more gives a fourth attachment distinct from all previous three. -/
theorem innerCycle_fourth_attachment
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 5 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v)
    (he : E.walk.IsChord s(E.walk.snd, E.walk.penultimate))
    {a : V} (haC : a ∈ C.support) (haE : a ∉ E.walk.support)
    (haAdj : G.Adj ((E.innerCycle (by omega) (Walk.isChord_sym2Mk.mp he).1).getVert 2) a) :
    ∃ b, G.Adj ((E.innerCycle (by omega) (Walk.isChord_sym2Mk.mp he).1).getVert 3) b ∧
      b ∈ C.support ∧ b ∉ E.walk.support ∧ b ≠ a := by
  let D := E.innerCycle (by omega : 2 ≤ E.walk.length) (Walk.isChord_sym2Mk.mp he).1
  have hD : D.IsCycle := E.innerCycle_isCycle (by omega) he
  have hDchordless : D.IsChordless := E.innerCycle_isChordless C hC.1 hC.2.1 hno (by omega) he
  have hDlen : D.length = E.walk.length - 1 := E.innerCycle_length _ _
  have hDout : ∀ v ∈ D.support, v ∉ C.support := fun v hv => E.innerCycle_notMem _ _ hv
  have hDmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length ≤ D.length := by
    intro P
    have hP := hmax P
    omega
  have hBY : G.Adj E.finish (D.getVert 1) := by
    change G.Adj E.finish D.snd
    rw [E.innerCycle_snd]
    exact (E.walk.adj_penultimate E.not_nil).symm
  have haB : a ≠ E.finish := fun heq => haE (by rw [heq]; exact E.walk.end_mem_support)
  let F := CycleArc.spokeEar D hD hDout (i := 1) (by omega)
    E.finish_mem haC haB hBY haAdj
  have hFlen : F.walk.length = E.walk.length := by
    have hf := CycleArc.spokeEar_length D hD hDout (i := 1) (by omega)
      E.finish_mem haC haB hBY haAdj
    change F.walk.length = D.length + 1 at hf
    omega
  have hFmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ F.walk.length := by
    intro P
    rw [hFlen]
    exact hmax P
  have hFX : F.walk.snd = D.getVert 1 := CycleArc.spokeEar_snd _ _ _ _ _ _ _ _ _
  have hFY : F.walk.penultimate = D.getVert 2 := CycleArc.spokeEar_penultimate _ _ _ _ _ _ _ _ _
  have hFchord := F.inner_closing_chord C hC hno (by omega) hFmax hdegree
  obtain ⟨b, hbAdj, hbC⟩ := CycleArc.exists_next_attachment D hD hDchordless hDout
    hDmax (i := 2) (by omega) (hdegree _) haC haAdj.symm
  have hinj : ∀ i : ℕ, i < 3 → D.getVert 3 ≠ D.getVert i := by
    intro i hi heq
    have heq' : 3 = i := hD.getVert_injOn' (show 3 ≤ D.length - 1 by omega)
      (show i ≤ D.length - 1 by omega) heq
    omega
  have hWX : D.getVert 3 ≠ E.walk.snd := by simpa only [Walk.getVert_zero] using hinj 0 (by omega)
  have hWY : D.getVert 3 ≠ E.walk.penultimate := by
    have hY : D.getVert 1 = E.walk.penultimate := E.innerCycle_snd _ _
    rw [← hY]
    exact hinj 1 (by omega)
  have hbE := E.inner_vertex_rim_neighbor_notMem C hC.1 hC.2.1 hno (by omega) he
    (E.innerCycle_support_subset _ _ (D.getVert_mem_support 3))
    (hDout _ (D.getVert_mem_support 3)) hWX hWY hbC hbAdj
  have hWF : D.getVert 3 ∈ F.walk.support :=
    CycleArc.mem_spokeEar_of_mem_cycle _ _ _ _ _ _ _ _ _ (D.getVert_mem_support 3)
  have hbF := F.inner_vertex_rim_neighbor_notMem C hC.1 hC.2.1 hno (by omega) hFchord
    hWF (hDout _ (D.getVert_mem_support 3))
    (by rw [hFX]; exact hinj 1 (by omega)) (by rw [hFY]; exact hinj 2 (by omega)) hbC hbAdj
  refine ⟨b, hbAdj, hbC, hbE, ?_⟩
  intro heq
  apply hbF
  rw [heq]
  exact F.walk.end_mem_support

#print axioms innerCycle_third_attachment
#print axioms innerCycle_fourth_attachment

end Erdos1091.Voss.Ear
