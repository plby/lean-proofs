/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossLinkage
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Attachments to a shortest odd cycle

These lemmas implement the preliminary reduction in Voss's structural proof:
three neighbours of a vertex outside a shortest odd cycle force that cycle
to be a triangle, and hence give a complete graph on four vertices.
-/

open SimpleGraph

namespace Erdos1091.Voss

namespace Ear

variable {V : Type*} {G : SimpleGraph V} {S : Set V}

theorem not_nil (E : Ear G S) : ¬ E.walk.Nil := by
  rw [E.isPath.nil_iff_eq]
  exact E.endpoints_ne

theorem finish_notMem_dropLast (E : Ear G S) : E.finish ∉ E.walk.dropLast.support := by
  intro hv
  obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hlen := E.walk.length_dropLast_add_one E.not_nil
  have hiC : i < E.walk.length := by omega
  rw [Walk.getVert_dropLast hiC] at hi
  have heq : i = E.walk.length :=
    E.isPath.getVert_injOn hiC.le (show E.walk.length ≤ E.walk.length from le_rfl)
      (hi.trans E.walk.getVert_length.symm)
  omega

theorem penultimate_notMem (E : Ear G S) (hlen : 2 ≤ E.walk.length) :
    E.walk.penultimate ∉ S := by
  intro hvS
  have hv : E.walk.penultimate ∈ E.walk.support := E.walk.getVert_mem_support _
  rcases E.only_ends _ hv hvS with hvStart | hvEnd
  · have hi : E.walk.length - 1 = 0 := E.isPath.getVert_injOn (Nat.sub_le _ _)
      (show 0 ≤ E.walk.length by omega)
      (hvStart.trans E.walk.getVert_zero.symm)
    omega
  · exact (E.walk.adj_penultimate E.not_nil).ne hvEnd

/-- Deleting the final edge of an ear of length at least two gives an
attachment path whose terminal vertex is the penultimate ear vertex. -/
def dropLastPath (E : Ear G S) (hlen : 2 ≤ E.walk.length) : AttachmentPath G S where
  start := E.start
  finish := E.walk.penultimate
  walk := E.walk.dropLast
  isPath := E.isPath.dropLast
  start_mem := E.start_mem
  finish_notMem := E.penultimate_notMem hlen
  only_start := by
    intro v hv hvS
    have hvE : v ∈ E.walk.support := by
      change v ∈ (E.walk.take (E.walk.length - 1)).support at hv
      rw [Walk.support_take] at hv
      exact List.mem_of_mem_take hv
    rcases E.only_ends v hvE hvS with hvStart | hvFinish
    · exact hvStart
    · exact (E.finish_notMem_dropLast (hvFinish ▸ hv)).elim

@[simp] theorem dropLastPath_length_add_one (E : Ear G S) (hlen : 2 ≤ E.walk.length) :
    (E.dropLastPath hlen).walk.length + 1 = E.walk.length :=
  E.walk.length_dropLast_add_one E.not_nil

/-- Reversing an ear exchanges the attachment endpoints. -/
def reverse (E : Ear G S) : Ear G S where
  start := E.finish
  finish := E.start
  walk := E.walk.reverse
  isPath := E.isPath.reverse
  start_mem := E.finish_mem
  finish_mem := E.start_mem
  endpoints_ne := E.endpoints_ne.symm
  only_ends := by
    intro v hv hvS
    have hvE : v ∈ E.walk.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hv
    exact (E.only_ends v hvE hvS).symm

theorem snd_notMem (E : Ear G S) (hlen : 2 ≤ E.walk.length) : E.walk.snd ∉ S := by
  have h := E.reverse.penultimate_notMem (by
    simpa only [reverse, Walk.length_reverse] using hlen)
  simpa only [reverse, Walk.penultimate_reverse] using h

theorem snd_ne_penultimate (E : Ear G S) (hlen : 3 ≤ E.walk.length) :
    E.walk.snd ≠ E.walk.penultimate := by
  intro he
  have hi : 1 = E.walk.length - 1 := E.isPath.getVert_injOn
    (show 1 ≤ E.walk.length by omega) (Nat.sub_le _ _) he
  omega

theorem edge_ne_endpoints_of_notMem (E : Ear G S) {x y : V} (hx : x ∉ S) :
    s(x, y) ≠ s(E.start, E.finish) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨hxE, _⟩ | ⟨hxE, _⟩
  · exact hx (by rw [hxE]; exact E.start_mem)
  · exact hx (by rw [hxE]; exact E.finish_mem)

/-- In Case 1, the two off-ear returns must be the same edge, joining
the two inner end-neighbours of the ear. -/
theorem returns_inside_eq {z : V} (C : G.Walk z z) (hC : C.IsCycle)
    (hodd : Odd C.length) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    {x y : V} (hx : x ∈ E.walk.support) (hy : y ∈ E.walk.support)
    (hadjX : G.Adj E.walk.snd x) (hadjY : G.Adj E.walk.penultimate y)
    (hedgeX : s(E.walk.snd, x) ∉ E.walk.edges)
    (hedgeY : s(E.walk.penultimate, y) ∉ E.walk.edges) :
    x = E.walk.penultimate ∧ y = E.walk.snd := by
  have hX : E.walk.IsChord s(E.walk.snd, x) :=
    ⟨hadjX, hedgeX, E.walk.getVert_mem_support 1, hx⟩
  have hY : E.walk.IsChord s(E.walk.penultimate, y) :=
    ⟨hadjY, hedgeY, E.walk.getVert_mem_support _, hy⟩
  have heq := chords_eq_of_no_odd_two_chords C hC hodd hno E (by omega) hX hY
    (E.edge_ne_endpoints_of_notMem (E.snd_notMem (by omega)))
    (E.edge_ne_endpoints_of_notMem (E.penultimate_notMem (by omega)))
  rcases Sym2.eq_iff.mp heq with ⟨hXY, _⟩ | ⟨hXy, hxY⟩
  · exact (E.snd_ne_penultimate hlen hXY).elim
  · exact ⟨hxY, hXy.symm⟩

/-- In a maximum-length ear, each terminal-neighbour return stays on the
ear or reaches the attachment set. -/
theorem neighbor_penultimate_mem (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G S, P.walk.length + 1 ≤ E.walk.length)
    {v : V} (hv : G.Adj E.walk.penultimate v) : v ∈ E.walk.support ∨ v ∈ S := by
  have hmax' : ∀ P : AttachmentPath G S, P.walk.length ≤ (E.dropLastPath hlen).walk.length := by
    intro P
    have hp := hmax P
    have he := E.dropLastPath_length_add_one hlen
    omega
  rcases (E.dropLastPath hlen).neighbor_mem_of_longest hmax' hv with hvP | hvS
  · left
    change v ∈ (E.walk.take (E.walk.length - 1)).support at hvP
    rw [Walk.support_take] at hvP
    exact List.mem_of_mem_take hvP
  · exact Or.inr hvS

/-- A third neighbour at the penultimate vertex gives a return edge not
traversed by the ear. -/
theorem exists_return_at_penultimate [Fintype V] [DecidableRel G.Adj]
    (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G S, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : 3 ≤ G.degree E.walk.penultimate) :
    ∃ v, G.Adj E.walk.penultimate v ∧ s(E.walk.penultimate, v) ∉ E.walk.edges ∧
      (v ∈ E.walk.support ∨ v ∈ S) := by
  classical
  have hpair : ({E.finish, E.walk.dropLast.penultimate} : Finset V).card ≤ 2 := by
    simpa using Finset.card_insert_le E.finish ({E.walk.dropLast.penultimate} : Finset V)
  have hsmall : ({E.finish, E.walk.dropLast.penultimate} : Finset V).card <
      (G.neighborFinset E.walk.penultimate).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨v, hvN, hvpair⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hv : G.Adj E.walk.penultimate v := by simpa using hvN
  refine ⟨v, hv, ?_, E.neighbor_penultimate_mem hlen hmax hv⟩
  intro he
  have hsplit : E.walk.edges = E.walk.dropLast.edges ++ [s(E.walk.penultimate, E.finish)] := by
    calc
      _ = (E.walk.dropLast.concat (E.walk.adj_penultimate E.not_nil)).edges := by
        rw [Walk.concat_dropLast]
      _ = _ := by simpa only [List.concat_eq_append] using Walk.edges_concat _ _
  rw [hsplit, List.mem_append, List.mem_singleton] at he
  rcases he with he | he
  · have hvprev := E.isPath.dropLast.eq_penultimate_of_mem_edges he
    exact hvpair (by simp [hvprev])
  · have hvend := (Sym2.mkEmbedding E.walk.penultimate).injective he
    exact hvpair (by simp [hvend])

/-- The two off-ear return edges used in the three placement cases of
Voss's structural proof. -/
theorem exists_two_returns [Fintype V] [DecidableRel G.Adj]
    (E : Ear G S) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G S, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v) :
    ∃ x y, G.Adj E.walk.snd x ∧ G.Adj E.walk.penultimate y ∧
      s(E.walk.snd, x) ∉ E.walk.edges ∧ s(E.walk.penultimate, y) ∉ E.walk.edges ∧
      (x ∈ E.walk.support ∨ x ∈ S) ∧ (y ∈ E.walk.support ∨ y ∈ S) := by
  obtain ⟨y, hy, hyNot, hyMem⟩ :=
    E.exists_return_at_penultimate (by omega) hmax (hdegree E.walk.penultimate)
  have hrlen : 2 ≤ E.reverse.walk.length := by
    simpa only [reverse, Walk.length_reverse] using (show 2 ≤ E.walk.length by omega)
  have hrmax : ∀ P : AttachmentPath G S, P.walk.length + 1 ≤ E.reverse.walk.length := by
    simpa only [reverse, Walk.length_reverse] using hmax
  obtain ⟨x, hx, hxNot, hxMem⟩ :=
    E.reverse.exists_return_at_penultimate hrlen hrmax (hdegree _)
  refine ⟨x, y, ?_, hy, ?_, hyNot, ?_, hyMem⟩
  · simpa only [reverse, Walk.penultimate_reverse] using hx
  · simpa only [reverse, Walk.penultimate_reverse, Walk.edges_reverse, List.mem_reverse] using hxNot
  · simpa only [reverse, Walk.support_reverse, List.mem_reverse] using hxMem

/-- Two spokes through a vertex outside the attachment set form an ear. -/
def twoSpokes {x y a : V} (hx : x ∈ S) (hy : y ∈ S) (ha : a ∉ S)
    (hxy : x ≠ y) (hax : G.Adj a x) (hay : G.Adj a y) : Ear G S where
  start := x
  finish := y
  walk := Walk.cons hax.symm (Walk.cons hay Walk.nil)
  isPath := by
    apply Walk.IsPath.mk'
    simp [hax.ne.symm, hxy, hay.ne]
  start_mem := hx
  finish_mem := hy
  endpoints_ne := hxy
  only_ends := by
    intro v hv hvS
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (ha hvS).elim
    · exact Or.inr rfl

/-- An edge from an interior ear vertex to an interior vertex of the
attachment-set arc is a chord of their union. -/
theorem isChord_cross_append (E : Ear G S) (q : G.Walk E.finish E.start)
    (hqS : ∀ v ∈ q.support, v ∈ S) {x y : V}
    (hx : x ∈ E.walk.support) (hxS : x ∉ S) (hy : y ∈ q.support)
    (hyStart : y ≠ E.start) (hyFinish : y ≠ E.finish) (hxy : G.Adj x y) :
    (E.walk.append q).IsChord s(x, y) := by
  refine ⟨hxy, ?_, (Walk.mem_support_append_iff _ _).mpr (Or.inl hx),
    (Walk.mem_support_append_iff _ _).mpr (Or.inr hy)⟩
  intro he
  rw [Walk.edges_append, List.mem_append] at he
  rcases he with he | he
  · have hyE := E.walk.snd_mem_support_of_mem_edges he
    rcases E.only_ends y hyE (hqS y hy) with hyEq | hyEq
    · exact hyStart hyEq
    · exact hyFinish hyEq
  · exact hxS (hqS x (q.fst_mem_support_of_mem_edges he))

/-- With two distinct return edges, the ear plus the attachment-set arc
must be even when odd cycles with two chords have been excluded. -/
theorem even_append_of_two_cross_edges (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (q : G.Walk E.finish E.start) (hq : q.IsPath) (hqS : ∀ v ∈ q.support, v ∈ S)
    (hno : ¬ HasOddCycleWithTwoChords G) {x₁ x₂ y₁ y₂ : V}
    (hx₁ : x₁ ∈ E.walk.support) (hx₁S : x₁ ∉ S)
    (hx₂ : x₂ ∈ E.walk.support) (hx₂S : x₂ ∉ S)
    (hy₁ : y₁ ∈ q.support) (hy₁Start : y₁ ≠ E.start) (hy₁Finish : y₁ ≠ E.finish)
    (hy₂ : y₂ ∈ q.support) (hy₂Start : y₂ ≠ E.start) (hy₂Finish : y₂ ≠ E.finish)
    (h₁ : G.Adj x₁ y₁) (h₂ : G.Adj x₂ y₂) (hne : s(x₁, y₁) ≠ s(x₂, y₂)) :
    Even (E.walk.length + q.length) := by
  apply Nat.not_odd_iff_even.mp
  intro hodd
  apply hno
  refine ⟨E.start, E.walk.append q, E.isCycle_append hlen q hq hqS,
    ?_, s(x₁, y₁), s(x₂, y₂), hne, ?_, ?_⟩
  · simpa only [Walk.length_append] using hodd
  · exact E.isChord_cross_append q hqS hx₁ hx₁S hy₁ hy₁Start hy₁Finish h₁
  · exact E.isChord_cross_append q hqS hx₂ hx₂S hy₂ hy₂Start hy₂Finish h₂

end Ear

namespace IsShortestOddCycle

variable {V : Type*} {G : SimpleGraph V} {z : V} {C : G.Walk z z}

/-- Closing an odd arc with two spokes cannot produce a shorter odd cycle. -/
theorem le_odd_arc_length_add_two (hC : IsShortestOddCycle C)
    {x y a : V} (q : G.Walk x y) (hq : q.IsPath) (hqpos : 0 < q.length)
    (hqC : ∀ v ∈ q.support, v ∈ C.support) (ha : a ∉ C.support)
    (hax : G.Adj a x) (hay : G.Adj a y) (hodd : Odd q.length) :
    C.length ≤ q.length + 2 := by
  have hxy : x ≠ y := by
    intro he
    have hnil := hq.nil_iff_eq.mpr he
    have hzero := Walk.length_eq_zero_iff.mpr hnil
    omega
  let E := Ear.twoSpokes (S := {v | v ∈ C.support})
    (hqC x q.start_mem_support) (hqC y q.end_mem_support) ha hxy hax hay
  have hEC : (E.walk.append q.reverse).IsCycle := E.isCycle_append
    (by simp [E, Ear.twoSpokes]) q.reverse hq.reverse (by
      intro v hv
      have hs := q.support_reverse
      exact hqC v (List.mem_reverse.mp (hs ▸ hv)))
  have hlen : (E.walk.append q.reverse).length = q.length + 2 := by
    calc
      _ = E.walk.length + q.reverse.length := Walk.length_append _ _
      _ = E.walk.length + q.length := congrArg (Nat.add E.walk.length) q.length_reverse
      _ = q.length + 2 := by change 2 + q.length = _; omega
  have hodd' : Odd (E.walk.append q.reverse).length := by
    rw [hlen, Nat.odd_iff]
    rw [Nat.odd_iff] at hodd
    omega
  exact (hC.2.2 x (E.walk.append q.reverse) hEC hodd').trans_eq hlen

end IsShortestOddCycle

/-- The three positive arcs of an odd cycle, each minimal when odd, must
all be single edges when they are closed by the same pair of spokes. -/
theorem three_arcs_eq_one {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hodd : Odd (a + b + c))
    (hminA : Odd a → a + b + c ≤ a + 2)
    (hminB : Odd b → a + b + c ≤ b + 2)
    (hminC : Odd c → a + b + c ≤ c + 2) : a = 1 ∧ b = 1 ∧ c = 1 := by
  simp only [Nat.odd_iff] at hodd hminA hminB hminC
  omega

namespace IsShortestOddCycle

variable {V : Type*} {G : SimpleGraph V} {z : V} {C : G.Walk z z}

/-- Three spokes, in their cyclic order, force the shortest odd cycle to
have length three. -/
theorem length_eq_three_of_three_spokes (hC : IsShortestOddCycle C)
    {a : V} (ha : a ∉ C.support) {j k : ℕ}
    (hj : 0 < j) (hjk : j < k) (hk : k < C.length)
    (haz : G.Adj a z) (haj : G.Adj a (C.getVert j)) (hak : G.Adj a (C.getVert k)) :
    C.length = 3 ∧ j = 1 ∧ k = 2 := by
  let p := C.take j
  let q₀ := (C.drop j).take (k - j)
  have hend : (C.drop j).getVert (k - j) = C.getVert k := by
    rw [Walk.drop_getVert]
    congr 1
    omega
  let q := q₀.copy rfl hend
  let r := C.drop k
  have hp : p.IsPath := hC.1.isPath_take (by omega)
  have hq : q.IsPath := (Walk.isPath_copy _ _ _).mpr ((hC.1.isPath_drop hj).take (k - j))
  have hr : r.IsPath := hC.1.isPath_drop (by omega)
  have hpLen : p.length = j := by
    simp only [p, Walk.take_length, Nat.min_eq_left (by omega : j ≤ C.length)]
  have hqLen : q.length = k - j := by
    simp only [q, q₀, Walk.length_copy, Walk.take_length, Walk.drop_length,
      Nat.min_eq_left (by omega : k - j ≤ C.length - j)]
  have hrLen : r.length = C.length - k := Walk.drop_length _ _
  have hpC : ∀ v ∈ p.support, v ∈ C.support := by
    intro v hv
    rw [Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  have hqC : ∀ v ∈ q.support, v ∈ C.support := by
    intro v hv
    have hsup : q.support = q₀.support := Walk.support_copy _ _ _
    rw [hsup, Walk.support_take] at hv
    have hvd := List.mem_of_mem_take hv
    rw [Walk.drop_support_eq_support_drop_min] at hvd
    exact List.mem_of_mem_drop hvd
  have hrC : ∀ v ∈ r.support, v ∈ C.support := by
    intro v hv
    rw [Walk.drop_support_eq_support_drop_min] at hv
    exact List.mem_of_mem_drop hv
  have hsum : p.length + q.length + r.length = C.length := by omega
  have hodd : Odd (p.length + q.length + r.length) := by rw [hsum]; exact hC.2.1
  obtain ⟨hpOne, hqOne, hrOne⟩ := three_arcs_eq_one
    (by omega : 1 ≤ p.length) (by omega : 1 ≤ q.length) (by omega : 1 ≤ r.length) hodd
    (by
      intro hodd
      rw [hsum]
      exact hC.le_odd_arc_length_add_two p hp (by omega) hpC ha haz haj hodd)
    (by
      intro hodd
      rw [hsum]
      exact hC.le_odd_arc_length_add_two q hq (by omega) hqC ha haj hak hodd)
    (by
      intro hodd
      rw [hsum]
      exact hC.le_odd_arc_length_add_two r hr (by omega) hrC ha hak haz hodd)
  omega

/-- The triangular case of the three-spoke reduction is exactly a `K₄`. -/
theorem not_cliqueFree_of_three_spokes (hC : IsShortestOddCycle C)
    {a : V} (ha : a ∉ C.support) {j k : ℕ}
    (hj : 0 < j) (hjk : j < k) (hk : k < C.length)
    (haz : G.Adj a z) (haj : G.Adj a (C.getVert j)) (hak : G.Adj a (C.getVert k)) :
    ¬ G.CliqueFree 4 := by
  classical
  obtain ⟨hC3, rfl, rfl⟩ := hC.length_eq_three_of_three_spokes ha hj hjk hk haz haj hak
  have h01 : G.Adj z (C.getVert 1) := C.adj_snd hC.1.not_nil
  have h12 : G.Adj (C.getVert 1) (C.getVert 2) := C.adj_getVert_succ (by omega)
  have h20 : G.Adj (C.getVert 2) z := by
    have h := C.adj_getVert_succ (i := 2) (by omega)
    have h3 : 2 + 1 = C.length := by omega
    rw [h3, Walk.getVert_length] at h
    exact h
  have htri : G.IsNClique 3 {z, C.getVert 1, C.getVert 2} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h01, h20.symm, h12⟩
  have hfour : G.IsNClique 4 (insert a {z, C.getVert 1, C.getVert 2}) := htri.insert (by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact haz
    · exact haj
    · exact hak)
  exact fun hfree => hfree _ hfour

/-- Shortest oddness is invariant under choosing another starting vertex. -/
theorem rotate [DecidableEq V] (hC : IsShortestOddCycle C) {x : V} (hx : x ∈ C.support) :
    IsShortestOddCycle (C.rotate x hx) := by
  refine ⟨hC.1.rotate hx, ?_, ?_⟩
  · simpa only [Walk.length_rotate] using hC.2.1
  · intro v q hq hodd
    simpa only [Walk.length_rotate] using hC.2.2 v q hq hodd

/-- A vertex outside a shortest odd cycle of a `K₄`-free graph cannot
have three distinct neighbours on that cycle. -/
theorem not_three_neighbors (hC : IsShortestOddCycle C) (hfree : G.CliqueFree 4)
    {a x y w : V} (ha : a ∉ C.support)
    (hx : x ∈ C.support) (hy : y ∈ C.support) (hw : w ∈ C.support)
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w)
    (hax : G.Adj a x) (hay : G.Adj a y) (haw : G.Adj a w) : False := by
  classical
  let R := C.rotate x hx
  have hR : IsShortestOddCycle R := hC.rotate hx
  have haR : a ∉ R.support := by simpa [R] using ha
  have hyR : y ∈ R.support := by simpa [R] using hy
  have hwR : w ∈ R.support := by simpa [R] using hw
  obtain ⟨j, hjget, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hyR
  obtain ⟨k, hkget, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hwR
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    exact hxy (by simpa only [hj0, Walk.getVert_zero] using hjget)
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    exact hxw (by simpa only [hk0, Walk.getVert_zero] using hkget)
  have hjlt : j < R.length := by
    by_contra h
    have hje : j = R.length := by omega
    exact hxy (by simpa only [hje, Walk.getVert_length] using hjget)
  have hklt : k < R.length := by
    by_contra h
    have hke : k = R.length := by omega
    exact hxw (by simpa only [hke, Walk.getVert_length] using hkget)
  have hjk : j ≠ k := by
    intro he
    exact hyw (hjget.symm.trans (he ▸ hkget))
  have haj : G.Adj a (R.getVert j) := hjget ▸ hay
  have hak : G.Adj a (R.getVert k) := hkget ▸ haw
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · exact hR.not_cliqueFree_of_three_spokes haR hjpos hjk hklt hax haj hak hfree
  · exact hR.not_cliqueFree_of_three_spokes haR hkpos hkj hjlt hax hak haj hfree

/-- At most two neighbours of an external vertex lie on a shortest odd
cycle in a `K₄`-free graph. -/
theorem card_neighbors_le_two [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : IsShortestOddCycle C) (hfree : G.CliqueFree 4) {a : V} (ha : a ∉ C.support) :
    ((G.neighborFinset a).filter fun v => v ∈ C.support).card ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨x, hx, y, hy, w, hw, hxy, hxw, hyw⟩ := Finset.two_lt_card.mp (by omega :
    2 < ((G.neighborFinset a).filter fun v => v ∈ C.support).card)
  obtain ⟨hax, hxC⟩ := Finset.mem_filter.mp hx
  obtain ⟨hay, hyC⟩ := Finset.mem_filter.mp hy
  obtain ⟨haw, hwC⟩ := Finset.mem_filter.mp hw
  exact hC.not_three_neighbors hfree ha hxC hyC hwC hxy hxw hyw
    (by simpa using hax) (by simpa using hay) (by simpa using haw)

/-- Minimum degree three supplies a two-edge attachment path to a shortest
odd cycle, since that cycle is chordless and outside vertices have at most
two neighbours on it. -/
theorem exists_attachment_length_two [Fintype V] [DecidableRel G.Adj]
    (hC : IsShortestOddCycle C) (hfree : G.CliqueFree 4)
    (hdegree : ∀ v, 3 ≤ G.degree v) :
    ∃ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length = 2 := by
  classical
  have hpair : ({C.snd, C.penultimate} : Finset V).card ≤ 2 := by
    simpa using Finset.card_insert_le C.snd ({C.penultimate} : Finset V)
  have hsmall : ({C.snd, C.penultimate} : Finset V).card < (G.neighborFinset z).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have := hdegree z
    omega
  obtain ⟨v, hvN, hvpair⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hzv : G.Adj z v := by simpa using hvN
  have hvC : v ∉ C.support := by
    intro hv
    have he := hC.isChordless.mem_edges C.start_mem_support hv hzv
    rcases cycle_edge_at_base C hC.1 he with hv | hv
    · exact hvpair (by simp [hv])
    · exact hvpair (by simp [hv])
  have hvBound := hC.card_neighbors_le_two hfree hvC
  have hvSmall : ((G.neighborFinset v).filter fun w => w ∈ C.support).card <
      (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have := hdegree v
    omega
  obtain ⟨w, hwN, hwI⟩ := Finset.exists_mem_notMem_of_card_lt_card hvSmall
  have hvw : G.Adj v w := by simpa using hwN
  have hwC : w ∉ C.support := fun hw => hwI (Finset.mem_filter.mpr ⟨hwN, hw⟩)
  let P : AttachmentPath G {v | v ∈ C.support} := {
    start := z
    finish := v
    walk := hzv.toWalk
    isPath := hzv.isPath_toWalk
    start_mem := C.start_mem_support
    finish_notMem := hvC
    only_start := by
      intro x hx hxC
      change x ∈ [z, v] at hx
      rcases List.mem_cons.mp hx with hx | hx
      · exact hx
      · have hxv : x = v := List.mem_singleton.mp hx
        exact (hvC (hxv ▸ hxC)).elim }
  have hwP : w ∉ P.walk.support := by
    intro hw
    change w ∈ [z, v] at hw
    rcases List.mem_cons.mp hw with hw | hw
    · exact hwC (by rw [hw]; exact C.start_mem_support)
    · exact hvw.ne (List.mem_singleton.mp hw).symm
  refine ⟨P.extend hvw hwP hwC, ?_⟩
  simp [AttachmentPath.extend, P]

/-- The initial configuration for Voss's parity cases: an ear of length
at least three, one edge longer than every attachment path. -/
theorem exists_maximal_ear {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {z : V} {C : G.Walk z z}
    (hC : IsShortestOddCycle C) (hfree : G.CliqueFree 4)
    (hdegree : ∀ v, 3 ≤ G.degree v) (hno : ¬ HasOddCycleWithTwoChords G)
    (hconn : G.Connected) (hdelete : ∀ d : V, (G.induce {v | v ≠ d}).Connected) :
    ∃ E : Ear G {v | v ∈ C.support}, 3 ≤ E.walk.length ∧
      ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length := by
  obtain ⟨P₀, hP₀⟩ := hC.exists_attachment_length_two hfree hdegree
  obtain ⟨P, hmax⟩ := P₀.exists_longest
  obtain ⟨E, hE⟩ := AttachmentPath.exists_long_ear_of_odd_cycle C hC.1 hC.2.1 hno P hmax
    hconn hdelete (fun v _ => hdegree v)
  refine ⟨E, ?_, ?_⟩
  · have hle := hmax P₀
    omega
  · intro Q
    rw [hE]
    exact Nat.add_le_add_right (hmax Q) 1

end IsShortestOddCycle

/-- The explicit length contradiction for the noncrossed return-edge
configuration in Voss's Case 3. -/
theorem noncrossed_return_parity_contradiction {a b c d s : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hodd : Odd (a + b + c + d))
    (hfirst : Even (s + 2 + a + b + c))
    (hsecond : Even (s + 2 + a + c + d))
    (hminA : Odd (a + 2) → a + b + c + d ≤ a + 2)
    (hminC : Odd (c + 2) → a + b + c + d ≤ c + 2) : False := by
  simp only [Nat.odd_iff, Nat.even_iff] at hodd hfirst hsecond hminA hminC
  omega

/-- Case 2(a): the two even doubly-chorded cycles and shortest oddness
force the two rim arcs through the far endpoint to be edges. -/
theorem one_external_return_parity {a b c s : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hodd : Odd (a + b + c))
    (hfirst : Even (s + 2 + a + b)) (hsecond : Even (s + 2 + a + c))
    (hminA : Odd (a + 2) → a + b + c ≤ a + 2) :
    b = 1 ∧ c = 1 ∧ Even s := by
  simp only [Nat.odd_iff, Nat.even_iff] at hodd hfirst hsecond hminA ⊢
  omega

/-- Case 2(b): when the other return reaches the initial attachment, the
three even doubly-chorded cycles force the outer cycle to be a triangle. -/
theorem return_to_initial_parity {a b c s : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hodd : Odd (a + b + c))
    (hfirst : Even (s + 2 + a + c)) (hsecond : Even (s + 2 + b + c))
    (hthird : Even (s + 2 + a + b))
    (hminA : Odd (a + 2) → a + b + c ≤ a + 2)
    (hminC : Odd (c + 2) → a + b + c ≤ c + 2) :
    a = 1 ∧ b = 1 ∧ c = 1 ∧ Even s := by
  simp only [Nat.odd_iff, Nat.even_iff] at hodd hfirst hsecond hthird hminA hminC ⊢
  omega

#print axioms IsShortestOddCycle.exists_maximal_ear

end Erdos1091.Voss
