/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 767.
https://www.erdosproblems.com/forum/thread/767

Informal authors:
- Tao Jiang

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos767.md
-/
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib
import ErdosProblems.Erdos767.LongestCycle
import ErdosProblems.Erdos767.Dirac

/-!
# Erdős Problem 767

For positive `k`, Jiang proved that the maximum number of edges in an
`n`-vertex graph having no cycle with `k` distinct chords incident to one
cycle vertex is

`(k + 1) * n - (k + 1) ^ 2`

as soon as `3 * k + 3 ≤ n`.

The mathematical proof and a detailed map of the formalization are in
`tex/767.tex`.

Reference: T. Jiang, *A note on a conjecture about cycles with many incident
chords*, J. Graph Theory 46 (2004), 180--182.
-/

open Finset
open SimpleGraph
open scoped SimpleGraph

namespace Erdos767

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

/-- A graph has the forbidden configuration for Problem 767 when a simple
cycle has at least `k` distinct chord edges which share a cycle vertex.

The embedding selects distinct opposite endpoints.  `Walk.IsChord` says that
the selected ambient edge joins two vertices of the cycle and is not a rim
edge of the cycle.  The explicit support condition on the common endpoint is
needed when `k = 0`. -/
def HasCycleWithKIncidentChords {V : Type u} (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

/-- The admissibility predicate in the definition of `g_k(n)`. -/
def AvoidsCycleWithKIncidentChords {V : Type u} (k : ℕ) (G : SimpleGraph V) : Prop :=
  ¬HasCycleWithKIncidentChords k G

/-- The extremal number from Problem 767, using labelled graphs on `Fin n`.
Every finite graph on `n` vertices is isomorphic to one of these graphs. -/
def chordCycleExtremalNumber (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) =>
    AvoidsCycleWithKIncidentChords k G).sup fun G => G.edgeFinset.card

lemma bot_avoids (k : ℕ) {V : Type u} :
    AvoidsCycleWithKIncidentChords k (⊥ : SimpleGraph V) := by
  rintro ⟨v, c, hc, f, hf, hchord⟩
  exact SimpleGraph.isAcyclic_bot c hc

lemma mem_admissibleGraphs_iff {k n : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ (Finset.univ.filter fun H : SimpleGraph (Fin n) =>
      AvoidsCycleWithKIncidentChords k H) ↔
      AvoidsCycleWithKIncidentChords k G := by
  simp

lemma card_edgeFinset_le_chordCycleExtremalNumber {k n : ℕ}
    {G : SimpleGraph (Fin n)} (hG : AvoidsCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤ chordCycleExtremalNumber k n := by
  unfold chordCycleExtremalNumber
  exact Finset.le_sup
    (s := Finset.univ.filter fun H : SimpleGraph (Fin n) =>
      AvoidsCycleWithKIncidentChords k H)
    (f := fun H : SimpleGraph (Fin n) => H.edgeFinset.card)
    (b := G) (mem_admissibleGraphs_iff.mpr hG)

lemma exists_extremizer (k n : ℕ) :
    ∃ G : SimpleGraph (Fin n),
      AvoidsCycleWithKIncidentChords k G ∧
        G.edgeFinset.card = chordCycleExtremalNumber k n := by
  let A := Finset.univ.filter fun G : SimpleGraph (Fin n) =>
    AvoidsCycleWithKIncidentChords k G
  have hA : A.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [A, bot_avoids]
  obtain ⟨G, hGA, hG⟩ :=
    Finset.exists_mem_eq_sup A hA (fun H : SimpleGraph (Fin n) => H.edgeFinset.card)
  exact ⟨G, (Finset.mem_filter.mp hGA).2, hG.symm⟩

/-! ## Transport and heredity -/

lemma isChord_map_embedding {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G ↪g H) {a b : V} {c : G.Walk a b}
    {e : Sym2 V} (he : c.IsChord e) :
    (c.map φ.toHom).IsChord (e.map φ) := by
  induction e using Sym2.ind with
  | _ x y =>
      rw [SimpleGraph.Walk.isChord_sym2Mk] at he
      change (c.map φ.toHom).IsChord s(φ x, φ y)
      rw [SimpleGraph.Walk.isChord_sym2Mk]
      rcases he with ⟨hxy, hnot, hx, hy⟩
      refine ⟨φ.toHom.map_adj hxy, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_map]
        intro hmem
        obtain ⟨e, hec, heq⟩ := List.mem_map.mp hmem
        have heeq : e = s(x, y) := (Sym2.map.injective φ.injective) heq
        exact hnot (heeq ▸ hec)
      · simp only [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨x, hx, rfl⟩
      · simp only [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨y, hy, rfl⟩

lemma hasCycleWithKIncidentChords_map_embedding {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ↪g H) {k : ℕ}
    (hG : HasCycleWithKIncidentChords k G) :
    HasCycleWithKIncidentChords k H := by
  rcases hG with ⟨v, c, hc, f, hf, hchord⟩
  let f' : Fin k → W := fun i ↦ φ (f i)
  refine ⟨φ v, c.map φ.toHom, hc.map φ.injective, f', ?_, ?_⟩
  · exact φ.injective.comp hf
  · intro i
    change (c.map φ.toHom).IsChord s(φ v, φ (f i))
    simpa only [Sym2.map_mk] using isChord_map_embedding φ (hchord i)

lemma avoids_of_embedding {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G ↪g H) {k : ℕ}
    (hH : AvoidsCycleWithKIncidentChords k H) :
    AvoidsCycleWithKIncidentChords k G :=
  fun hG ↦ hH (hasCycleWithKIncidentChords_map_embedding φ hG)

lemma avoids_induce {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G) (s : Set V) :
    AvoidsCycleWithKIncidentChords k (G.induce s) :=
  avoids_of_embedding (Embedding.induce s) hG

lemma avoids_iff_of_iso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G ≃g H) (k : ℕ) :
    AvoidsCycleWithKIncidentChords k G ↔
      AvoidsCycleWithKIncidentChords k H := by
  constructor
  · exact avoids_of_embedding φ.symm.toEmbedding
  · exact avoids_of_embedding φ.toEmbedding

/-! ## The complete-bipartite lower construction -/

private def IsLeft {L R : Type*} : L ⊕ R → Prop
  | .inl _ => True
  | .inr _ => False

private def IsRight {L R : Type*} : L ⊕ R → Prop
  | .inl _ => False
  | .inr _ => True

@[simp] private lemma isLeft_inl {L R : Type*} (x : L) :
    IsLeft (R := R) (.inl x) := trivial

@[simp] private lemma not_isLeft_inr {L R : Type*} (x : R) :
    ¬IsLeft (L := L) (.inr x) := by simp [IsLeft]

@[simp] private lemma not_isRight_inl {L R : Type*} (x : L) :
    ¬IsRight (R := R) (.inl x) := by simp [IsRight]

@[simp] private lemma isRight_inr {L R : Type*} (x : R) :
    IsRight (L := L) (.inr x) := trivial

private lemma sum_isLeft_iff {L R : Type*} (x : L ⊕ R) :
    x.isLeft = true ↔ IsLeft x := by
  cases x <;> simp [IsLeft]

private lemma sum_isRight_iff {L R : Type*} (x : L ⊕ R) :
    x.isRight = true ↔ IsRight x := by
  cases x <;> simp [IsRight]

private lemma adj_left_iff_right {L R : Type*} {x y : L ⊕ R}
    (h : (completeBipartiteGraph L R).Adj x y) :
    IsLeft x ↔ IsRight y := by
  cases x <;> cases y <;>
    simp_all [completeBipartiteGraph_adj, IsLeft, IsRight]

private lemma adj_right_iff_left {L R : Type*} {x y : L ⊕ R}
    (h : (completeBipartiteGraph L R).Adj x y) :
    IsRight x ↔ IsLeft y := by
  cases x <;> cases y <;>
    simp_all [completeBipartiteGraph_adj, IsLeft, IsRight]

private def leftCount {L R : Type*} (l : List (L ⊕ R)) : ℕ :=
  l.countP Sum.isLeft

private def rightCount {L R : Type*} (l : List (L ⊕ R)) : ℕ :=
  l.countP Sum.isRight

private lemma leftCount_dropLast_eq_rightCount_dropLast {L R : Type*}
    {z : L ⊕ R} (p : (completeBipartiteGraph L R).Walk z z) :
    leftCount p.support.dropLast = rightCount p.support.dropLast := by
  calc
    leftCount p.support.dropLast = leftCount (p.darts.map (·.fst)) := by
      rw [p.map_fst_darts]
    _ = rightCount (p.darts.map (·.snd)) := by
      simp only [leftCount, rightCount, List.countP_map]
      apply congrArg (fun q ↦ List.countP q p.darts)
      funext d
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply]
      rw [sum_isLeft_iff, sum_isRight_iff]
      exact adj_left_iff_right d.adj
    _ = rightCount p.support.tail := by rw [p.map_snd_darts]
    _ = rightCount p.support.dropLast :=
      p.tail_support_perm_dropLast_support.countP_eq _

section FiniteSides

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]

private def cycleVertices {z : L ⊕ R}
    (p : (completeBipartiteGraph L R).Walk z z) : Finset (L ⊕ R) :=
  p.support.dropLast.toFinset

private def leftCycleVertices {z : L ⊕ R}
    (p : (completeBipartiteGraph L R).Walk z z) : Finset (L ⊕ R) :=
  (cycleVertices p).filter fun x ↦ x.isLeft

private def rightCycleVertices {z : L ⊕ R}
    (p : (completeBipartiteGraph L R).Walk z z) : Finset (L ⊕ R) :=
  (cycleVertices p).filter fun x ↦ x.isRight

private lemma card_leftCycleVertices {z : L ⊕ R}
    {p : (completeBipartiteGraph L R).Walk z z} (hp : p.IsCycle) :
    (leftCycleVertices p).card = leftCount p.support.dropLast := by
  simpa [leftCycleVertices, cycleVertices, leftCount] using
    (hp.nodup_dropLast_support.card_eq_countP (P := fun x ↦ x.isLeft))

private lemma card_rightCycleVertices {z : L ⊕ R}
    {p : (completeBipartiteGraph L R).Walk z z} (hp : p.IsCycle) :
    (rightCycleVertices p).card = rightCount p.support.dropLast := by
  simpa [rightCycleVertices, cycleVertices, rightCount] using
    (hp.nodup_dropLast_support.card_eq_countP (P := fun x ↦ x.isRight))

private lemma card_leftCycleVertices_eq_right {z : L ⊕ R}
    {p : (completeBipartiteGraph L R).Walk z z} (hp : p.IsCycle) :
    (leftCycleVertices p).card = (rightCycleVertices p).card := by
  rw [card_leftCycleVertices hp, card_rightCycleVertices hp,
    leftCount_dropLast_eq_rightCount_dropLast]

private lemma card_filter_univ_isLeft :
    (Finset.univ.filter fun x : L ⊕ R ↦ x.isLeft).card = Fintype.card L := by
  let e : L ↪ L ⊕ R := ⟨Sum.inl, Sum.inl_injective⟩
  rw [show (Finset.univ.filter fun x : L ⊕ R ↦ x.isLeft) =
      Finset.univ.map e by
    ext x
    cases x <;> simp [e]]
  simp

private lemma card_leftCycleVertices_le {z : L ⊕ R}
    (p : (completeBipartiteGraph L R).Walk z z) :
    (leftCycleVertices p).card ≤ Fintype.card L := by
  rw [← card_filter_univ_isLeft (L := L) (R := R)]
  exact Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      (Finset.mem_filter.mp hx).2⟩)

private lemma card_rightCycleVertices_le_left {z : L ⊕ R}
    {p : (completeBipartiteGraph L R).Walk z z} (hp : p.IsCycle) :
    (rightCycleVertices p).card ≤ Fintype.card L := by
  rw [← card_leftCycleVertices_eq_right hp]
  exact card_leftCycleVertices_le p

end FiniteSides

section SelectedVertices

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]
variable {z : L ⊕ R} {p : (completeBipartiteGraph L R).Walk z z}

private def selectedVertices {k : ℕ}
    (p : (completeBipartiteGraph L R).Walk z z) (f : Fin k → L ⊕ R) :
    Finset (L ⊕ R) :=
  {p.snd, p.penultimate} ∪ Finset.univ.image f

private lemma selected_pair_disjoint {k : ℕ} (hp : p.IsCycle)
    {f : Fin k → L ⊕ R} (hfchord : ∀ i, p.IsChord s(z, f i)) :
    Disjoint ({p.snd, p.penultimate} : Finset (L ⊕ R))
      (Finset.univ.image f) := by
  rw [Finset.disjoint_left]
  intro x hxpair hximage
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hximage
  have hnot := (SimpleGraph.Walk.isChord_sym2Mk.mp (hfchord i)).2.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
  rcases hxpair with h | h
  · exact hnot (by simpa only [h] using p.mk_start_snd_mem_edges hp.not_nil)
  · exact hnot (by
      simpa only [h, Sym2.eq_swap] using
        p.mk_penultimate_end_mem_edges hp.not_nil)

private lemma card_selectedVertices {k : ℕ} (hp : p.IsCycle)
    {f : Fin k → L ⊕ R} (hf : Function.Injective f)
    (hfchord : ∀ i, p.IsChord s(z, f i)) :
    (selectedVertices p f).card = k + 2 := by
  rw [selectedVertices,
    Finset.card_union_of_disjoint (selected_pair_disjoint hp hfchord)]
  have himage : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · exact hf.injOn
  rw [himage]
  simp [hp.snd_ne_penultimate]
  omega

private lemma snd_mem_cycleVertices (hp : p.IsCycle) :
    p.snd ∈ cycleVertices p := by
  rw [cycleVertices, List.mem_toFinset]
  exact p.tail_support_perm_dropLast_support.mem_iff.mp
    (p.snd_mem_tail_support hp.not_nil)

private lemma penultimate_mem_cycleVertices (hp : p.IsCycle) :
    p.penultimate ∈ cycleVertices p := by
  rw [cycleVertices, List.mem_toFinset]
  exact p.penultimate_mem_dropLast_support hp.not_nil

private lemma chord_endpoint_mem_cycleVertices {x : L ⊕ R}
    (hx : p.IsChord s(z, x)) : x ∈ cycleVertices p := by
  have h := SimpleGraph.Walk.isChord_sym2Mk.mp hx
  rw [cycleVertices, List.mem_toFinset]
  apply List.mem_dropLast_of_mem_of_ne_getLast h.2.2.2
  simpa only [p.getLast_support] using h.1.ne'

private lemma selected_subset_right_of_left {k : ℕ} (hp : p.IsCycle)
    (hz : IsLeft z) {f : Fin k → L ⊕ R}
    (hfchord : ∀ i, p.IsChord s(z, f i)) :
    selectedVertices p f ⊆ rightCycleVertices p := by
  intro x hx
  rw [selectedVertices, Finset.mem_union] at hx
  rw [rightCycleVertices, Finset.mem_filter]
  rcases hx with hxpair | hximage
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
    rcases hxpair with rfl | rfl
    · refine ⟨snd_mem_cycleVertices hp, ?_⟩
      exact (sum_isRight_iff _).mpr
        ((adj_left_iff_right (p.adj_snd hp.not_nil)).mp hz)
    · refine ⟨penultimate_mem_cycleVertices hp, ?_⟩
      exact (sum_isRight_iff _).mpr
        ((adj_left_iff_right (p.adj_penultimate hp.not_nil).symm).mp hz)
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hximage
    have hi := SimpleGraph.Walk.isChord_sym2Mk.mp (hfchord i)
    refine ⟨chord_endpoint_mem_cycleVertices (hfchord i), ?_⟩
    exact (sum_isRight_iff _).mpr ((adj_left_iff_right hi.1).mp hz)

private lemma selected_subset_left_of_right {k : ℕ} (hp : p.IsCycle)
    (hz : IsRight z) {f : Fin k → L ⊕ R}
    (hfchord : ∀ i, p.IsChord s(z, f i)) :
    selectedVertices p f ⊆ leftCycleVertices p := by
  intro x hx
  rw [selectedVertices, Finset.mem_union] at hx
  rw [leftCycleVertices, Finset.mem_filter]
  rcases hx with hxpair | hximage
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
    rcases hxpair with rfl | rfl
    · refine ⟨snd_mem_cycleVertices hp, ?_⟩
      exact (sum_isLeft_iff _).mpr
        ((adj_right_iff_left (p.adj_snd hp.not_nil)).mp hz)
    · refine ⟨penultimate_mem_cycleVertices hp, ?_⟩
      exact (sum_isLeft_iff _).mpr
        ((adj_right_iff_left (p.adj_penultimate hp.not_nil).symm).mp hz)
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hximage
    have hi := SimpleGraph.Walk.isChord_sym2Mk.mp (hfchord i)
    refine ⟨chord_endpoint_mem_cycleVertices (hfchord i), ?_⟩
    exact (sum_isLeft_iff _).mpr ((adj_right_iff_left hi.1).mp hz)

end SelectedVertices

lemma completeBipartite_avoids (k m : ℕ) :
    AvoidsCycleWithKIncidentChords k
      (completeBipartiteGraph (Fin (k + 1)) (Fin m)) := by
  rintro ⟨z, p, hp, f, hf, hfchord⟩
  have hcard : (selectedVertices p f).card = k + 2 :=
    card_selectedVertices hp hf hfchord
  cases z with
  | inl z =>
      have hsub := selected_subset_right_of_left hp (by simp) hfchord
      have hle := Finset.card_le_card hsub
      have hu := card_rightCycleVertices_le_left hp
      simp only [Fintype.card_fin] at hu
      rw [hcard] at hle
      omega
  | inr z =>
      have hsub := selected_subset_left_of_right hp (by simp) hfchord
      have hle := Finset.card_le_card hsub
      have hu := card_leftCycleVertices_le p
      simp only [Fintype.card_fin] at hu
      rw [hcard] at hle
      omega

private lemma card_edgeFinset_completeBipartiteFin (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).edgeFinset.card = a * b := by
  have h := encard_edgeSet_completeBipartiteGraph
    (W₁ := Fin a) (W₂ := Fin b)
  have h' := congrArg ENat.toNat h
  simpa [SimpleGraph.edgeFinset, Set.encard_eq_coe_toFinset_card] using h'

private abbrev LowerVertex (k n : ℕ) :=
  Fin (k + 1) ⊕ Fin (n - (k + 1))

private def lowerGraph (k n : ℕ) : SimpleGraph (LowerVertex k n) :=
  completeBipartiteGraph (Fin (k + 1)) (Fin (n - (k + 1)))

private lemma card_lowerVertex {k n : ℕ} (hkn : k + 1 ≤ n) :
    Fintype.card (LowerVertex k n) = n := by
  simp [LowerVertex]
  omega

private lemma lowerGraph_avoids (k n : ℕ) :
    AvoidsCycleWithKIncidentChords k (lowerGraph k n) :=
  completeBipartite_avoids k (n - (k + 1))

private lemma card_edgeFinset_lowerGraph (k n : ℕ) :
    (lowerGraph k n).edgeFinset.card =
      (k + 1) * n - (k + 1) ^ 2 := by
  rw [lowerGraph, card_edgeFinset_completeBipartiteFin]
  rw [Nat.mul_sub_left_distrib]
  simp [pow_two]

lemma lower_bound (k n : ℕ) (hkn : k + 1 ≤ n) :
    (k + 1) * n - (k + 1) ^ 2 ≤ chordCycleExtremalNumber k n := by
  let H := lowerGraph k n
  let Hn : SimpleGraph (Fin n) := H.overFin (card_lowerVertex hkn)
  have hfree : AvoidsCycleWithKIncidentChords k Hn := by
    rw [show Hn = H.overFin (card_lowerVertex hkn) by rfl]
    exact (avoids_iff_of_iso (H.overFinIso (card_lowerVertex hkn)) k).mp
      (lowerGraph_avoids k n)
  have hcard : Hn.edgeFinset.card =
      (k + 1) * n - (k + 1) ^ 2 := by
    rw [show Hn = H.overFin (card_lowerVertex hkn) by rfl]
    rw [← (H.overFinIso (card_lowerVertex hkn)).card_edgeFinset_eq]
    exact card_edgeFinset_lowerGraph k n
  rw [← hcard]
  exact card_edgeFinset_le_chordCycleExtremalNumber hfree

/-! ## The longest-path low-degree lemma -/

private lemma isChord_rotate_iff {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u v : V}
    (c : G.Walk u u) (hv : v ∈ c.support) (e : Sym2 V) :
    (c.rotate v hv).IsChord e ↔ c.IsChord e := by
  induction e using Sym2.ind with
  | _ x y =>
      simp only [SimpleGraph.Walk.isChord_sym2Mk,
        SimpleGraph.Walk.mem_support_rotate_iff]
      rw [(c.rotate_edges v hv).mem_iff]

lemma hasCycleWithKIncidentChords_of_isLongestPath_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    {a b : V} {p : G.Walk a b}
    (hp : Erdos767LongestCycle.IsLongestPath p)
    (hdeg : k + 2 ≤ G.degree b) :
    HasCycleWithKIncidentChords k G := by
  let I : Finset ℕ := (Finset.range p.length).filter fun i ↦
    G.Adj b (p.getVert i)
  have htwo : 2 ≤ G.degree b := by omega
  have hplen : 2 ≤ p.length := htwo.trans hp.degree_end_le_length
  have hI : I.Nonempty := by
    refine ⟨p.length - 1, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    exact p.adj_penultimate (by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      omega) |>.symm
  let j : ℕ := I.min' hI
  have hjI : j ∈ I := Finset.min'_mem I hI
  have hjlt : j < p.length :=
    (Finset.mem_filter.mp hjI).1 |> Finset.mem_range.mp
  have hbj : G.Adj b (p.getVert j) := (Finset.mem_filter.mp hjI).2
  let r : G.Walk (p.getVert j) b := p.drop j
  have hrpath : r.IsPath := hp.1.drop j
  have hneighbor : G.neighborFinset b ⊆ r.support.toFinset.erase b := by
    intro x hx
    have hbx : G.Adj b x := (G.mem_neighborFinset b x).mp hx
    have hxP : x ∈ p.support := hp.end_neighbor_mem_support hbx
    obtain ⟨i, hi, hile⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxP
    have hilt : i < p.length := by
      rcases hile.lt_or_eq with hilt | rfl
      · exact hilt
      · rw [p.getVert_length] at hi
        exact (hbx.ne hi).elim
    have hiI : i ∈ I := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hilt, hi.symm ▸ hbx⟩
    have hji : j ≤ i := Finset.min'_le I i hiI
    have hxR : x ∈ r.support := by
      have hm : r.getVert (i - j) = x := by
        change (p.drop j).getVert (i - j) = x
        rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hji, hi]
      exact hm ▸ r.getVert_mem_support (i - j)
    exact Finset.mem_erase.mpr
      ⟨hbx.ne.symm, List.mem_toFinset.mpr hxR⟩
  have hdegree_le : G.degree b ≤ r.length := by
    rw [← G.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset b).card ≤ (r.support.toFinset.erase b).card :=
        Finset.card_le_card hneighbor
      _ = r.length := by
        rw [Finset.card_erase_of_mem
          (List.mem_toFinset.mpr r.end_mem_support)]
        rw [List.toFinset_card_of_nodup hrpath.support_nodup,
          r.length_support]
        omega
  have hrlen : 2 ≤ r.length := htwo.trans hdegree_le
  have hedge : s(p.getVert j, b) ∉ r.reverse.edges := by
    intro hedge
    have hedge' : s(p.getVert j, b) ∈ r.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using hedge
    have hone := hrpath.length_eq_one_of_mem_edges hedge'
    omega
  let c : G.Walk (p.getVert j) (p.getVert j) := r.reverse.cons hbj.symm
  have hc : c.IsCycle := by
    exact (SimpleGraph.Walk.cons_isCycle_iff r.reverse hbj.symm).mpr
      ⟨hrpath.reverse, hedge⟩
  have hbmem : b ∈ c.support := by
    simp only [c, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_reverse, List.mem_cons, List.mem_reverse]
    exact Or.inr r.end_mem_support
  let A : Finset V := G.neighborFinset b
  let B : Finset V := (c.toSubgraph.neighborSet b).toFinset
  have hBcard : B.card = 2 := by
    simpa [B] using hc.ncard_neighborSet_toSubgraph_eq_two hbmem
  have hBsub : B ⊆ A := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    exact (G.mem_neighborFinset b x).mpr (c.toSubgraph.adj_sub hx)
  let T : Finset V := A \ B
  have hTcard : k ≤ T.card := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset hBsub, hBcard]
    change k ≤ G.degree b - 2
    omega
  let g : Fin k ↪ T :=
    (Fin.castLEEmb hTcard).trans (Finset.equivFin T).symm.toEmbedding
  let f : Fin k → V := fun i ↦ (g i).1
  have hf : Function.Injective f := by
    intro i i' hii'
    apply g.injective
    exact Subtype.ext hii'
  let c' : G.Walk b b := c.rotate b hbmem
  have hc' : c'.IsCycle := by simpa [c'] using hc.rotate hbmem
  refine ⟨b, c', hc', f, hf, ?_⟩
  intro i
  have hxT : f i ∈ T := (g i).2
  have hxAB : f i ∈ A ∧ f i ∉ B := Finset.mem_sdiff.mp hxT
  have hbx : G.Adj b (f i) :=
    (G.mem_neighborFinset b (f i)).mp hxAB.1
  change (c.rotate b hbmem).IsChord s(b, f i)
  apply (isChord_rotate_iff c hbmem s(b, f i)).mpr
  rw [SimpleGraph.Walk.isChord_sym2Mk]
  refine ⟨hbx, ?_, hbmem, ?_⟩
  · intro he
    apply hxAB.2
    change f i ∈ (c.toSubgraph.neighborSet b).toFinset
    rw [Set.mem_toFinset, Subgraph.mem_neighborSet,
      SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    exact he
  · have hxR := hneighbor hxAB.1
    have hxRs : f i ∈ r.support :=
      List.mem_toFinset.mp (Finset.mem_of_mem_erase hxR)
    simp only [c, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_reverse, List.mem_cons, List.mem_reverse]
    exact Or.inr hxRs

lemma exists_degree_le_add_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G) :
    ∃ v : V, G.degree v ≤ k + 1 := by
  obtain ⟨a, b, p, hp⟩ :=
    Erdos767LongestCycle.exists_isLongestPath (G := G)
  refine ⟨b, ?_⟩
  by_contra h
  exact hG (hasCycleWithKIncidentChords_of_isLongestPath_degree hp (by omega))

/-! ## Induction above Jiang's base order -/

lemma edge_count_add_sq_le_of_base (k : ℕ)
    (hbase : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = 3 * (k + 1) →
        AvoidsCycleWithKIncidentChords k H →
        H.edgeFinset.card ≤ 2 * (k + 1) ^ 2) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      3 * (k + 1) ≤ Fintype.card V →
        AvoidsCycleWithKIncidentChords k G →
        G.edgeFinset.card + (k + 1) ^ 2 ≤
          (k + 1) * Fintype.card V := by
  intro V _ _ G _ hn hG
  generalize hcard : Fintype.card V = n at hn ⊢
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases heq : n = 3 * (k + 1)
      · have hb := hbase V G (hcard.trans heq) hG
        nlinarith
      · have hlt : 3 * (k + 1) < n :=
          lt_of_le_of_ne hn (Ne.symm heq)
        letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
        obtain ⟨v, hvdeg⟩ := exists_degree_le_add_one hG
        let W : Type u := {x : V // x ∈ ({v}ᶜ : Set V)}
        let H : SimpleGraph W := G.induce ({v}ᶜ : Set V)
        have hWcard : Fintype.card W = n - 1 := by
          dsimp [W]
          change Fintype.card {x : V // x ≠ v} = n - 1
          rw [Fintype.card_subtype_compl (fun x : V ↦ x = v)]
          simp [hcard]
        have hHfree : AvoidsCycleWithKIncidentChords k H :=
          avoids_induce hG ({v}ᶜ : Set V)
        have hIH := ih (n - 1) (by omega) W H hHfree hWcard (by omega)
        have hdegcard : G.degree v ≤ G.edgeFinset.card :=
          G.degree_le_card_edgeFinset v
        have hedge : H.edgeFinset.card + G.degree v = G.edgeFinset.card := by
          dsimp [H]
          rw [G.card_edgeFinset_induce_compl_singleton,
            G.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel hdegcard]
        have hnsub : n - 1 + 1 = n := by omega
        nlinarith

lemma edge_count_le_of_base (k : ℕ)
    (hbase : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = 3 * (k + 1) →
        AvoidsCycleWithKIncidentChords k H →
        H.edgeFinset.card ≤ 2 * (k + 1) ^ 2)
    (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 * (k + 1) ≤ Fintype.card V)
    (hG : AvoidsCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤
      (k + 1) * Fintype.card V - (k + 1) ^ 2 := by
  exact Nat.le_sub_of_add_le
    (edge_count_add_sq_le_of_base k hbase V G hn hG)

/-! ## Jiang's sharp base case, reduced to Bondy's longest-cycle estimate -/

private lemma hasCycleWithKIncidentChords_of_hamiltonianCycle_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    {z : V} {c : G.Walk z z} (hc : c.IsHamiltonianCycle)
    (x : V) (hdeg : k + 2 ≤ G.degree x) :
    HasCycleWithKIncidentChords k G := by
  have hx : x ∈ c.support := hc.mem_support x
  let A : Finset V := G.neighborFinset x
  let B : Finset V := (c.toSubgraph.neighborSet x).toFinset
  have hBcard : B.card = 2 := by
    simpa [B] using hc.isCycle.ncard_neighborSet_toSubgraph_eq_two hx
  have hBsub : B ⊆ A := by
    intro y hy
    rw [Set.mem_toFinset] at hy
    exact (G.mem_neighborFinset x y).mpr (c.toSubgraph.adj_sub hy)
  let T : Finset V := A \ B
  have hTcard : k ≤ T.card := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset hBsub, hBcard]
    change k ≤ G.degree x - 2
    omega
  let g : Fin k ↪ T :=
    (Fin.castLEEmb hTcard).trans (Finset.equivFin T).symm.toEmbedding
  let f : Fin k → V := fun i ↦ (g i).1
  have hf : Function.Injective f := by
    intro i j hij
    apply g.injective
    exact Subtype.ext hij
  let c' : G.Walk x x := c.rotate x hx
  refine ⟨x, c', hc.isCycle.rotate hx, f, hf, ?_⟩
  intro i
  have hfi : f i ∈ T := (g i).2
  have hAB : f i ∈ A ∧ f i ∉ B := Finset.mem_sdiff.mp hfi
  have hadj : G.Adj x (f i) := (G.mem_neighborFinset x (f i)).mp hAB.1
  apply (isChord_rotate_iff c hx s(x, f i)).mpr
  rw [SimpleGraph.Walk.isChord_sym2Mk]
  refine ⟨hadj, ?_, hx, hc.mem_support (f i)⟩
  intro he
  apply hAB.2
  change f i ∈ (c.toSubgraph.neighborSet x).toFinset
  rw [Set.mem_toFinset, Subgraph.mem_neighborSet,
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  exact he

lemma degree_le_add_one_on_hamiltonianCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G)
    {z : V} {c : G.Walk z z} (hc : c.IsHamiltonianCycle)
    (x : V) : G.degree x ≤ k + 1 := by
  by_contra h
  exact hG (hasCycleWithKIncidentChords_of_hamiltonianCycle_degree hc x (by omega))

lemma two_mul_card_edges_le_of_hamiltonianCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G)
    {z : V} {c : G.Walk z z} (hc : c.IsHamiltonianCycle) :
    2 * G.edgeFinset.card ≤ (k + 1) * Fintype.card V := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  calc
    ∑ x, G.degree x ≤ ∑ _x : V, (k + 1) := by
      exact Finset.sum_le_sum fun x _hx ↦
        degree_le_add_one_on_hamiltonianCycle hG hc x
    _ = (k + 1) * Fintype.card V := by
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
      exact Nat.mul_comm _ _

private lemma avoids_zero_of_isAcyclic
    {V : Type u} {G : SimpleGraph V} (hG : G.IsAcyclic) :
    AvoidsCycleWithKIncidentChords 0 G := by
  rintro ⟨v, c, hc, f, hf, hchord⟩
  exact hG c hc

lemma card_edgeFinset_le_card_sub_one_of_isAcyclic
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V - 1 := by
  generalize hcard : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hn : n ≤ 1
      · have hedge := G.card_edgeFinset_le_card_choose_two
        rw [hcard] at hedge
        interval_cases n <;> simp_all
      · obtain ⟨v, hv⟩ := exists_degree_le_add_one
          (avoids_zero_of_isAcyclic hG)
        let W : Type u := {x : V // x ∈ ({v}ᶜ : Set V)}
        let H : SimpleGraph W := G.induce ({v}ᶜ : Set V)
        have hWcard : Fintype.card W = n - 1 := by
          dsimp [W]
          change Fintype.card {x : V // x ≠ v} = n - 1
          rw [Fintype.card_subtype_compl (fun x : V ↦ x = v)]
          simp [hcard]
        letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
        have hHacyc : H.IsAcyclic := hG.induce ({v}ᶜ : Set V)
        have hIH := ih (n - 1) (by omega) (V := W) H hHacyc hWcard
        have hdegcard : G.degree v ≤ G.edgeFinset.card :=
          G.degree_le_card_edgeFinset v
        have hedge : H.edgeFinset.card + G.degree v = G.edgeFinset.card := by
          dsimp [H]
          rw [G.card_edgeFinset_induce_compl_singleton,
            G.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel hdegcard]
        omega

/-! ## Longest-cycle induction across cut vertices -/

/-- The local longest-cycle predicate used by the induction below. -/
private def InductionLongestCycle {V : Type u} {G : SimpleGraph V}
    {z : V} (q : G.Walk z z) : Prop :=
  q.IsCycle ∧ ∀ (w : V) (r : G.Walk w w), r.IsCycle → r.length ≤ q.length

private lemma isCycle_length_le_card
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {z : V} {q : G.Walk z z} (hq : q.IsCycle) :
    q.length ≤ Fintype.card V := by
  rw [← Erdos767LongestCycle.cycleCarrier_card hq]
  exact Finset.card_le_univ _

private lemma card_setCoe_finset
    {V : Type u} [Fintype V] [DecidableEq V] (A : Finset V) :
    Fintype.card (↑A : Set V) = A.card := by
  simpa using Set.ncard_coe_finset A

private lemma card_insert_add_card_compl
    {V : Type u} [Fintype V] [DecidableEq V]
    (c : V) (A : Finset V) (hcA : c ∉ A) :
    (insert c A).card + Aᶜ.card = Fintype.card V + 1 := by
  have hle : A.card ≤ Fintype.card V := by simpa using Finset.card_le_univ A
  rw [Finset.card_insert_of_notMem hcA, Finset.card_compl]
  omega

private lemma card_insert_lt_card_of_mem_compl_erase
    {V : Type u} [Fintype V] [DecidableEq V]
    (c : V) (A : Finset V) {y : V} (hy : y ∈ Aᶜ.erase c) :
    (insert c A).card < Fintype.card V := by
  have hyA : y ∉ A := Finset.mem_compl.mp (Finset.mem_erase.mp hy).2
  have hyc : y ≠ c := (Finset.mem_erase.mp hy).1
  have hsub : insert c A ⊆ Finset.univ.erase y := by
    intro z hz
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ z⟩
    intro hzy
    subst z
    simp only [Finset.mem_insert] at hz
    exact hz.elim (fun h ↦ hyc h) (fun h ↦ hyA h)
  have hle := Finset.card_le_card hsub
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  have herase : (Finset.univ.erase y).card = Fintype.card V - 1 := by simp
  rw [herase] at hle
  omega

private lemma card_compl_lt_card_of_mem
    {V : Type u} [Fintype V] [DecidableEq V]
    (A : Finset V) {x : V} (hx : x ∈ A) :
    Aᶜ.card < Fintype.card V := by
  rw [Finset.card_compl]
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hle : A.card ≤ Fintype.card V := by simpa using Finset.card_le_univ A
  omega

private lemma cut_edge_cover
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (A : Finset V) (hcA : c ∉ A)
    (hcross : G.interedges A (Aᶜ.erase c) = ∅) :
    ∀ u v, G.Adj u v →
      (u ∈ insert c A ∧ v ∈ insert c A) ∨ (u ∈ Aᶜ ∧ v ∈ Aᶜ) := by
  intro u v huv
  by_cases huA : u ∈ A
  · by_cases hvA : v ∈ A
    · exact Or.inl ⟨by simp [huA], by simp [hvA]⟩
    · by_cases hvc : v = c
      · subst v
        exact Or.inl ⟨by simp [huA], by simp⟩
      · exfalso
        have he : (u, v) ∈ G.interedges A (Aᶜ.erase c) :=
          G.mk_mem_interedges_iff.mpr
            ⟨huA, Finset.mem_erase.mpr ⟨hvc, Finset.mem_compl.mpr hvA⟩, huv⟩
        simpa [hcross] using he
  · by_cases hvA : v ∈ A
    · by_cases huc : u = c
      · subst u
        exact Or.inl ⟨by simp, by simp [hvA]⟩
      · exfalso
        have he : (v, u) ∈ G.interedges A (Aᶜ.erase c) :=
          G.mk_mem_interedges_iff.mpr
            ⟨hvA, Finset.mem_erase.mpr ⟨huc, Finset.mem_compl.mpr huA⟩, huv.symm⟩
        simpa [hcross] using he
    · exact Or.inr ⟨Finset.mem_compl.mpr huA, Finset.mem_compl.mpr hvA⟩

private lemma cut_inter_card_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (c : V) (A : Finset V) (hcA : c ∉ A) :
    ((insert c A) ∩ Aᶜ).card ≤ 1 := by
  have hsub : insert c A ∩ Aᶜ ⊆ {c} := by
    intro x hx
    have hxL := (Finset.mem_inter.mp hx).1
    have hxR := (Finset.mem_inter.mp hx).2
    simp only [Finset.mem_insert] at hxL
    rcases hxL with rfl | hxA
    · simp
    · exact False.elim ((Finset.mem_compl.mp hxR) hxA)
  simpa using Finset.card_le_card hsub

private lemma card_edgeFinset_eq_add_induce_of_cut
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (A : Finset V) (hcA : c ∉ A)
    (hcross : G.interedges A (Aᶜ.erase c) = ∅) :
    G.edgeFinset.card =
      (G.induce (↑(insert c A) : Set V)).edgeFinset.card +
        (G.induce (↑(Aᶜ) : Set V)).edgeFinset.card := by
  exact E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_of_separation
    G (insert c A) Aᶜ (cut_edge_cover G c A hcA hcross)
      (cut_inter_card_le_one c A hcA)

private lemma reachable_induce_of_mem_support
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {u v x y : V} (p : G.Walk u v)
    (hS : ∀ z ∈ p.support, z ∈ S)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    (G.induce S).Reachable ⟨x, hS x hx⟩ ⟨y, hS y hy⟩ := by
  have hr := p.connected_induce_support.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  exact hr.map (G.induceHomOfLE hS).toHom

private lemma cycle_vertices_reachable_delete
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v c x y : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxc : x ≠ c) (hyc : y ≠ c) :
    (G.induce {z : V | z ≠ c}).Reachable ⟨x, hxc⟩ ⟨y, hyc⟩ := by
  by_cases hc : c ∈ p.support
  · let q : G.Walk c c := p.rotate c hc
    have hq : q.IsCycle := hp.rotate hc
    have hqtail : ¬ q.tail.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      have hlen := hq.three_le_length
      have ht := q.length_tail_add_one hq.not_nil
      omega
    let r := q.tail.dropLast
    have hrSupport : r.support = q.tail.support.dropLast :=
      q.tail.support_dropLast hqtail
    have hxq : x ∈ q.support := (p.mem_support_rotate_iff c hc).mpr hx
    have hyq : y ∈ q.support := (p.mem_support_rotate_iff c hc).mpr hy
    have hxt : x ∈ q.tail.support := by
      rw [q.support_tail_of_not_nil hq.not_nil]
      rw [q.support_eq_cons] at hxq
      exact (List.mem_cons.mp hxq).resolve_left hxc
    have hyt : y ∈ q.tail.support := by
      rw [q.support_tail_of_not_nil hq.not_nil]
      rw [q.support_eq_cons] at hyq
      exact (List.mem_cons.mp hyq).resolve_left hyc
    have hxdrop : x ∈ q.tail.support.dropLast := by
      apply List.mem_dropLast_of_mem_of_ne_getLast hxt
      simpa only [q.tail.getLast_support] using hxc
    have hydrop : y ∈ q.tail.support.dropLast := by
      apply List.mem_dropLast_of_mem_of_ne_getLast hyt
      simpa only [q.tail.getLast_support] using hyc
    have hcnot : c ∉ q.tail.support.dropLast := by
      have hdecomp := List.dropLast_append_getLast
        (l := q.tail.support) q.tail.support_ne_nil
      have hnodup := hq.isPath_tail.support_nodup
      rw [← hdecomp] at hnodup
      simp only [q.tail.getLast_support, List.nodup_append,
        List.nodup_singleton, true_and, List.mem_singleton, forall_eq] at hnodup
      exact fun hcMem ↦ (hnodup.2 c hcMem) rfl
    have hS : ∀ z ∈ r.support, z ∈ ({z : V | z ≠ c} : Set V) := by
      intro z hz hzc
      subst z
      apply hcnot
      rw [← hrSupport]
      exact hz
    have hxr : x ∈ r.support := by rwa [hrSupport]
    have hyr : y ∈ r.support := by rwa [hrSupport]
    simpa using reachable_induce_of_mem_support r hS hxr hyr
  · have hS : ∀ z ∈ p.support, z ∈ ({z : V | z ≠ c} : Set V) := by
      intro z hz hzc
      subst z
      exact hc hz
    simpa using reachable_induce_of_mem_support p hS hx hy

private noncomputable def cutComponent
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (x : {v : V // v ≠ c}) : Finset V :=
  (Finset.univ.filter fun y : {v : V // v ≠ c} ↦
    (G.induce {v : V | v ≠ c}).Reachable x y).map
      (Function.Embedding.subtype _)

@[simp] private lemma mem_cutComponent
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {c : V} {x : {v : V // v ≠ c}} {z : V} :
    z ∈ cutComponent G c x ↔
      ∃ hz : z ≠ c, (G.induce {v : V | v ≠ c}).Reachable x ⟨z, hz⟩ := by
  simp [cutComponent]

private lemma cutVertex_not_mem_cutComponent
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (x : {v : V // v ≠ c}) : c ∉ cutComponent G c x := by
  simp

private lemma interedges_cutComponent_compl_erase_eq_empty
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (x : {v : V // v ≠ c}) :
    G.interedges (cutComponent G c x) ((cutComponent G c x)ᶜ.erase c) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' :
      (e.1 ∈ cutComponent G c x ∧ e.2 ∈ (cutComponent G c x)ᶜ.erase c) ∧
        G.Adj e.1 e.2 := by
    simpa [SimpleGraph.interedges_def] using he
  obtain ⟨hu, hxu⟩ := mem_cutComponent.mp he'.1.1
  have hv : e.2 ≠ c := (Finset.mem_erase.mp he'.1.2).1
  have huv : (G.induce {v : V | v ≠ c}).Adj ⟨e.1, hu⟩ ⟨e.2, hv⟩ :=
    SimpleGraph.induce_adj.mpr he'.2
  have hxv := hxu.trans huv.reachable
  exact (Finset.mem_compl.mp (Finset.mem_erase.mp he'.1.2).2)
    (mem_cutComponent.mpr ⟨hv, hxv⟩)

private lemma cycle_support_subset_cut_side
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v c : V} {p : G.Walk v v} (hp : p.IsCycle)
    (x : {z : V // z ≠ c}) :
    (∀ z ∈ p.support, z ∈ insert c (cutComponent G c x)) ∨
      (∀ z ∈ p.support, z ∈ (cutComponent G c x)ᶜ) := by
  have hsnd : p.snd ∈ p.support :=
    List.mem_of_mem_tail (p.snd_mem_tail_support hp.not_nil)
  have hpen : p.penultimate ∈ p.support :=
    List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hp.not_nil)
  obtain ⟨w, hw, hwc⟩ : ∃ w, w ∈ p.support ∧ w ≠ c := by
    by_cases hsc : p.snd = c
    · exact ⟨p.penultimate, hpen,
        fun hpc ↦ hp.snd_ne_penultimate (hsc.trans hpc.symm)⟩
    · exact ⟨p.snd, hsnd, hsc⟩
  by_cases hwA : w ∈ cutComponent G c x
  · left
    intro z hz
    by_cases hzc : z = c
    · simp [hzc]
    · apply Finset.mem_insert.mpr
      right
      obtain ⟨_, hxw⟩ := mem_cutComponent.mp hwA
      have hwz := cycle_vertices_reachable_delete hp hw hz hwc hzc
      exact mem_cutComponent.mpr ⟨hzc, hxw.trans hwz⟩
  · right
    intro z hz
    apply Finset.mem_compl.mpr
    intro hzA
    by_cases hzc : z = c
    · subst z
      exact cutVertex_not_mem_cutComponent G c x hzA
    · obtain ⟨_, hxz⟩ := mem_cutComponent.mp hzA
      have hwz := cycle_vertices_reachable_delete hp hw hz hwc hzc
      apply hwA
      exact mem_cutComponent.mpr ⟨hwc, hxz.trans hwz.symm⟩

private lemma induce_isCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hS : ∀ z ∈ p.support, z ∈ S) :
    (p.induce S hS).IsCycle := by
  have hm : ((p.induce S hS).map
      (SimpleGraph.Embedding.induce (G := G) S).toHom).IsCycle := by
    simpa using hp
  exact hm.of_map

private lemma length_induce_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {x y : V} (p : G.Walk x y)
    (hS : ∀ z ∈ p.support, z ∈ S) :
    (p.induce S hS).length = p.length := by
  have hm := congrArg (fun r ↦ r.length) (SimpleGraph.Walk.map_induce p hS)
  simp only [SimpleGraph.Walk.length_map] at hm
  exact hm

private lemma induce_isLongestCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {v : V} {p : G.Walk v v}
    (hp : InductionLongestCycle p)
    (hS : ∀ z ∈ p.support, z ∈ S) :
    InductionLongestCycle (p.induce S hS) := by
  refine ⟨induce_isCycle hp.1 hS, ?_⟩
  intro w q hq
  have hqG : (q.map (SimpleGraph.Embedding.induce (G := G) S).toHom).IsCycle :=
    hq.map (SimpleGraph.Embedding.induce (G := G) S).injective
  have hlen := hp.2 w.1
    (q.map (SimpleGraph.Embedding.induce (G := G) S).toHom) hqG
  rw [length_induce_eq p hS]
  exact (SimpleGraph.Walk.length_map _ q).symm ▸ hlen

private def componentFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : Finset V :=
  Finset.univ.filter fun z ↦ G.Reachable r z

@[simp] private lemma mem_componentFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r z : V} :
    z ∈ componentFinset G r ↔ G.Reachable r z := by
  simp [componentFinset]

private lemma root_mem_componentFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : r ∈ componentFinset G r := by simp

private lemma cycle_support_subset_component
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V} (p : G.Walk v v) :
    ∀ z ∈ p.support, z ∈ componentFinset G v := by
  intro z hz
  rw [mem_componentFinset]
  exact (p.takeUntil z hz).reachable

private lemma card_edgeFinset_eq_add_induce_component
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    G.edgeFinset.card =
      (G.induce (↑(componentFinset G r) : Set V)).edgeFinset.card +
        (G.induce (↑((componentFinset G r)ᶜ) : Set V)).edgeFinset.card := by
  apply E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_compl
  intro u v huv
  simp only [mem_componentFinset]
  constructor
  · exact fun hu ↦ hu.trans huv.reachable
  · exact fun hv ↦ hv.trans huv.symm.reachable

private lemma cyclic_cut_arithmetic {n nL nR c a eL eR : ℕ}
    (hcard : nL + nR = n + 1) (hcL : c ≤ nL) (hRpos : 0 < nR)
    (hL : 2 * eL ≤ a * c + c * (nL - c))
    (hR : 2 * eR ≤ c * (nR - 1)) :
    2 * (eL + eR) ≤ a * c + c * (n - c) := by
  have hparts : (nL - c) + (nR - 1) = n - c := by omega
  calc
    2 * (eL + eR) = 2 * eL + 2 * eR := by omega
    _ ≤ (a * c + c * (nL - c)) + c * (nR - 1) := Nat.add_le_add hL hR
    _ = a * c + c * ((nL - c) + (nR - 1)) := by rw [Nat.mul_add]; omega
    _ = a * c + c * (n - c) := by rw [hparts]

private lemma cyclic_disconnected_arithmetic {n nL nR c a eL eR : ℕ}
    (hcard : nL + nR = n) (hcL : c ≤ nL) (hRpos : 0 < nR)
    (hL : 2 * eL ≤ a * c + c * (nL - c))
    (hR : 2 * eR ≤ c * (nR - 1)) :
    2 * (eL + eR) ≤ a * c + c * (n - c) := by
  have hparts : (nL - c) + (nR - 1) ≤ n - c := by omega
  calc
    2 * (eL + eR) = 2 * eL + 2 * eR := by omega
    _ ≤ (a * c + c * (nL - c)) + c * (nR - 1) := Nat.add_le_add hL hR
    _ = a * c + c * ((nL - c) + (nR - 1)) := by rw [Nat.mul_add]; omega
    _ ≤ a * c + c * (n - c) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left c hparts) _

/-- Edges whose two endpoints lie on a fixed finite vertex carrier. -/
def cycleInsideEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ C

/-- Edges with at least one endpoint outside a fixed finite vertex carrier. -/
def cycleOutsideEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset \ cycleInsideEdges G C

lemma cycleInsideEdges_subset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    cycleInsideEdges G C ⊆ G.edgeFinset := by
  intro e he
  exact (Finset.mem_filter.mp he).1

lemma card_inside_add_outside {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    (cycleInsideEdges G C).card + (cycleOutsideEdges G C).card =
      G.edgeFinset.card := by
  rw [cycleOutsideEdges, Finset.card_sdiff_of_subset (cycleInsideEdges_subset G C)]
  exact Nat.add_sub_of_le (Finset.card_le_card (cycleInsideEdges_subset G C))

lemma card_cycleInsideEdges_eq_induce {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    (cycleInsideEdges G C).card = (G.induce (C : Set V)).edgeFinset.card := by
  exact G.card_filter_edgeFinset_toFinset_subset C

lemma two_mul_card_cycleInsideEdges_le
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G)
    {z : V} {c : G.Walk z z} (hc : c.IsCycle) :
    2 * (cycleInsideEdges G c.support.toFinset).card ≤
      (k + 1) * c.length := by
  let C : Finset V := c.support.toFinset
  let hC : ∀ x ∈ c.support, x ∈ (C : Set V) := fun x hx ↦
    List.mem_toFinset.mpr hx
  let q : (G.induce (C : Set V)).Walk ⟨z, hC z c.start_mem_support⟩
      ⟨z, hC z c.end_mem_support⟩ := c.induce (C : Set V) hC
  have hq : q.IsHamiltonianCycle := by
    simpa [C, hC, q] using
      (Erdos767LongestCycle.induced_cycle_isHamiltonianCycle hc)
  have hfree : AvoidsCycleWithKIncidentChords k (G.induce (C : Set V)) :=
    avoids_induce hG (C : Set V)
  have hbound := two_mul_card_edges_le_of_hamiltonianCycle hfree hq
  rw [card_cycleInsideEdges_eq_induce]
  change 2 * (G.induce (C : Set V)).edgeFinset.card ≤ (k + 1) * c.length
  convert hbound using 1
  exact congrArg ((k + 1) * ·) <| ((Fintype.card_coe C).trans
    (Erdos767LongestCycle.cycleCarrier_card hc)).symm

/-- Strong cyclic estimate used in Jiang's base case.  The longest cycle is
allowed to change after a low-degree deletion; this is why the global
best-lollipop theorem suffices. -/
lemma cyclic_free_edge_bound
    (k : ℕ) :
    ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj]
      (z : W) (q : H.Walk z z),
      AvoidsCycleWithKIncidentChords k H →
      InductionLongestCycle q →
      2 * H.edgeFinset.card ≤
        (k + 1) * q.length +
          q.length * (Fintype.card W - q.length) := by
  intro W _ _ H _ z q hfree hq
  generalize hn : Fintype.card W = n
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
    have hqcard : q.length ≤ Fintype.card W := isCycle_length_le_card hq.1
    have hqthree : 3 ≤ q.length := hq.1.three_le_length
    have hcycles (X : Type u) [Fintype X] [DecidableEq X]
        (K : SimpleGraph X) [DecidableRel K.Adj]
        (f : K ↪g H) :
        ∀ (w : X) (r : K.Walk w w), r.IsCycle → r.length ≤ q.length := by
      intro w r hr
      have ht := hq.2 (f w) (r.map f.toHom) (hr.map f.injective)
      calc
        r.length = (r.map f.toHom).length :=
          (SimpleGraph.Walk.length_map _ r).symm
        _ ≤ q.length := ht
    by_cases hpre : H.Preconnected
    · letI : Nonempty W := ⟨z⟩
      have hconn : H.Connected := ⟨hpre⟩
      have hcard3 : 3 ≤ Fintype.card W := hqthree.trans hqcard
      by_cases hdel : ∀ c : W, (H.induce ({c}ᶜ : Set W)).Connected
      · have htwo : Erdos58.TwoConnected H := ⟨hcard3, hconn, hdel⟩
        by_cases hspan : Fintype.card W = q.length
        · have hham : q.IsHamiltonianCycle :=
            SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
              ⟨hq.1, hspan.symm⟩
          have hbase := two_mul_card_edges_le_of_hamiltonianCycle hfree hham
          rw [hspan] at hbase
          rw [← hn, hspan]
          simpa using hbase
        · have hnonspan : q.length < Fintype.card W :=
            lt_of_le_of_ne hqcard (Ne.symm hspan)
          have hqN : Erdos767LongestCycle.IsLongestCycle q := by
            refine ⟨hq.1, ?_⟩
            intro z' r hr
            exact hq.2 z' r hr
          obtain ⟨w, r, v, hrN, hv, hdeg⟩ :=
            Erdos767Dirac.exists_nonspanning_longestCycle_lowDegree
              H htwo hqN hnonspan
          have hr : InductionLongestCycle r :=
            ⟨hrN.1, fun _ r' hr' ↦ hrN.2 r' hr'⟩
          have hrq : r.length = q.length := by
            apply Nat.le_antisymm
            · exact hq.2 w r hr.1
            · exact hr.2 z q hq.1
          let S : Set W := {v}ᶜ
          have hrS : ∀ x ∈ r.support, x ∈ S := by
            intro x hx
            simp only [S, Set.mem_compl_iff, Set.mem_singleton_iff]
            intro hxv
            subst x
            exact hv hx
          let K : SimpleGraph S := H.induce S
          let p := r.induce S hrS
          have hp : InductionLongestCycle p := induce_isLongestCycle hr hrS
          have hfreeK : AvoidsCycleWithKIncidentChords k K :=
            avoids_induce hfree S
          have hScard : Fintype.card S = Fintype.card W - 1 := by
            dsimp [S]
            rw [Fintype.card_compl_set, Set.card_singleton]
          have hSlt : Fintype.card S < n := by omega
          have hind := ih (Fintype.card S) hSlt S K
            ⟨w, hrS w r.start_mem_support⟩ p hfreeK hp rfl
          rw [show p.length = r.length by exact length_induce_eq r hrS,
            hrq, hScard] at hind
          have hdegcard : H.degree v ≤ H.edgeFinset.card :=
            H.degree_le_card_edgeFinset v
          have hedge : K.edgeFinset.card + H.degree v = H.edgeFinset.card := by
            dsimp [K, S]
            rw [H.card_edgeFinset_induce_compl_singleton,
              H.card_edgeFinset_deleteIncidenceSet,
              Nat.sub_add_cancel hdegcard]
          calc
            2 * H.edgeFinset.card =
                2 * K.edgeFinset.card + 2 * H.degree v := by omega
            _ ≤ ((k + 1) * q.length +
                q.length * (Fintype.card W - 1 - q.length)) + q.length :=
              Nat.add_le_add hind (hrq ▸ hdeg)
            _ = (k + 1) * q.length + q.length * (n - q.length) := by
              rw [← hn, show Fintype.card W - q.length =
                (Fintype.card W - 1 - q.length) + 1 by omega, Nat.mul_add]
              omega
      · push Not at hdel
        obtain ⟨c, hc⟩ := hdel
        have hdelcard : 0 < Fintype.card ({c}ᶜ : Set W) := by
          rw [Fintype.card_compl_set, Set.card_singleton]
          omega
        letI : Nonempty ({c}ᶜ : Set W) := Fintype.card_pos_iff.mp hdelcard
        have hnotpre : ¬ (H.induce ({c}ᶜ : Set W)).Preconnected := by
          intro hp
          exact hc ⟨hp⟩
        simp only [SimpleGraph.Preconnected] at hnotpre
        push Not at hnotpre
        obtain ⟨x, y, hxy⟩ := hnotpre
        let A := cutComponent H c x
        have hcA : c ∉ A := cutVertex_not_mem_cutComponent H c x
        have hxA : x.1 ∈ A := mem_cutComponent.mpr
          ⟨x.2, SimpleGraph.Reachable.rfl⟩
        have hyB : y.1 ∈ Aᶜ.erase c := by
          apply Finset.mem_erase.mpr
          refine ⟨y.2, Finset.mem_compl.mpr ?_⟩
          intro hyA
          exact hxy (mem_cutComponent.mp hyA).2
        have hcross := interedges_cutComponent_compl_erase_eq_empty H c x
        have hcardSplit := card_insert_add_card_compl c A hcA
        have hleftlt := card_insert_lt_card_of_mem_compl_erase c A hyB
        have hrightlt := card_compl_lt_card_of_mem A hxA
        rcases cycle_support_subset_cut_side H hq.1 x with hqL | hqR
        · let S := insert c A
          let pL := q.induce (↑S : Set W) hqL
          have hpL := induce_isLongestCycle hq hqL
          have hfreeL := avoids_induce hfree (↑S : Set W)
          have hIL := ih S.card (by simpa [S, hn] using hleftlt)
            (↑S : Set W) (H.induce (↑S : Set W))
            ⟨z, hqL z q.start_mem_support⟩ pL hfreeL hpL
            (by simp [Fintype.card_coe])
          rw [show pL.length = q.length by exact length_induce_eq q hqL] at hIL
          have hcyclesR := hcycles (↑(Aᶜ) : Set W)
            (H.induce (↑(Aᶜ) : Set W))
            (SimpleGraph.Embedding.induce (G := H) _)
          have hER := Erdos767Dirac.erdosGallai_cycle
            (H.induce (↑(Aᶜ) : Set W)) q.length (by omega) hcyclesR
          rw [card_setCoe_finset (Aᶜ)] at hER
          have hedge := card_edgeFinset_eq_add_induce_of_cut H c A hcA hcross
          rw [hedge]
          exact cyclic_cut_arithmetic
            (n := n) (nL := S.card) (nR := Aᶜ.card)
            (c := q.length) (a := k + 1)
            (by simpa [S, hn] using hcardSplit)
            (by
              rw [← length_induce_eq q hqL]
              have ht := isCycle_length_le_card hpL.1
              rw [card_setCoe_finset S] at ht
              exact ht)
            (Finset.card_pos.mpr ⟨y.1, (Finset.mem_erase.mp hyB).2⟩)
            hIL hER
        · let S := Aᶜ
          let pR := q.induce (↑S : Set W) hqR
          have hpR := induce_isLongestCycle hq hqR
          have hfreeR := avoids_induce hfree (↑S : Set W)
          have hIR := ih S.card (by simpa [S, hn] using hrightlt)
            (↑S : Set W) (H.induce (↑S : Set W))
            ⟨z, hqR z q.start_mem_support⟩ pR hfreeR hpR
            (by simp [Fintype.card_coe])
          rw [show pR.length = q.length by exact length_induce_eq q hqR] at hIR
          have hcyclesL := hcycles (↑(insert c A) : Set W)
            (H.induce (↑(insert c A) : Set W))
            (SimpleGraph.Embedding.induce (G := H) _)
          have hEL := Erdos767Dirac.erdosGallai_cycle
            (H.induce (↑(insert c A) : Set W)) q.length (by omega) hcyclesL
          rw [card_setCoe_finset (insert c A)] at hEL
          have hedge := card_edgeFinset_eq_add_induce_of_cut H c A hcA hcross
          rw [hedge, Nat.add_comm]
          exact cyclic_cut_arithmetic
            (n := n) (nL := S.card) (nR := (insert c A).card)
            (c := q.length) (a := k + 1)
            (by simpa [S, hn, Nat.add_comm] using hcardSplit)
            (by
              rw [← length_induce_eq q hqR]
              have ht := isCycle_length_le_card hpR.1
              rw [card_setCoe_finset S] at ht
              exact ht)
            (Finset.card_pos.mpr ⟨c, by simp⟩) hIR hEL
    · have hy : ∃ y : W, ¬ H.Reachable z y := by
        by_contra hall
        push Not at hall
        apply hpre
        intro x y
        exact (hall x).symm.trans (hall y)
      obtain ⟨y, hzy⟩ := hy
      let S := componentFinset H z
      have hzS : z ∈ S := root_mem_componentFinset H z
      have hySc : y ∈ Sᶜ := Finset.mem_compl.mpr (by simpa [S] using hzy)
      have hSlt : S.card < Fintype.card W := by
        rw [← Finset.card_univ]
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_univ _, fun heq ↦
            (Finset.mem_compl.mp hySc) (heq.symm ▸ Finset.mem_univ y)⟩)
      have hqS := cycle_support_subset_component q
      let pS := q.induce (↑S : Set W) hqS
      have hpS := induce_isLongestCycle hq hqS
      have hfreeS := avoids_induce hfree (↑S : Set W)
      have hIS := ih S.card (by simpa [hn] using hSlt)
        (↑S : Set W) (H.induce (↑S : Set W)) ⟨z, hzS⟩ pS hfreeS hpS
        (by simp [Fintype.card_coe])
      rw [show pS.length = q.length by exact length_induce_eq q hqS] at hIS
      have hcyclesC := hcycles (↑(Sᶜ) : Set W)
        (H.induce (↑(Sᶜ) : Set W))
        (SimpleGraph.Embedding.induce (G := H) _)
      have hEC := Erdos767Dirac.erdosGallai_cycle
        (H.induce (↑(Sᶜ) : Set W)) q.length (by omega) hcyclesC
      rw [card_setCoe_finset (Sᶜ)] at hEC
      have hedge := card_edgeFinset_eq_add_induce_component H z
      rw [hedge]
      exact cyclic_disconnected_arithmetic
        (n := n) (nL := S.card) (nR := Sᶜ.card)
        (c := q.length) (a := k + 1)
        (by rw [Finset.card_compl, hn]; omega)
        (by
          rw [← length_induce_eq q hqS]
          have ht := isCycle_length_le_card hpS.1
          rw [card_setCoe_finset S] at ht
          exact ht)
        (Finset.card_pos.mpr ⟨y, hySc⟩) hIS hEC

/-- Jiang's base case follows from the division-free form of Bondy's
longest-cycle external-edge estimate. -/
lemma jiang_base_of_bondy
    (hbondy : ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (z : V) (c : G.Walk z z), c.IsCycle →
        (∀ (w : V) (d : G.Walk w w), d.IsCycle → d.length ≤ c.length) →
        2 * (cycleOutsideEdges G c.support.toFinset).card ≤
          c.length * (Fintype.card V - c.length))
    (k : ℕ) (hk : 0 < k)
    (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 3 * (k + 1))
    (hG : AvoidsCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤ 2 * (k + 1) ^ 2 := by
  by_cases hacyc : G.IsAcyclic
  · letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hforest := card_edgeFinset_le_card_sub_one_of_isAcyclic G hacyc
    rw [hcard] at hforest
    have hthree : 3 ≤ 2 * (k + 1) := by omega
    have hmul : 3 * (k + 1) ≤ 2 * (k + 1) ^ 2 := by
      calc
        3 * (k + 1) ≤ (2 * (k + 1)) * (k + 1) :=
          Nat.mul_le_mul_right (k + 1) hthree
        _ = 2 * (k + 1) ^ 2 := by ring
    omega
  · have hex : ∃ (z : V) (c : G.Walk z z), c.IsCycle := by
      simp only [SimpleGraph.IsAcyclic] at hacyc
      push Not at hacyc
      obtain ⟨z, c, hc⟩ := hacyc
      exact ⟨z, c, hc⟩
    obtain ⟨z₀, c₀, hc₀⟩ := hex
    have hnonempty : (Erdos767LongestCycle.cycleLengths G).Nonempty := by
      exact ⟨c₀.length,
        Erdos767LongestCycle.mem_cycleLengths_iff.mpr ⟨z₀, c₀, hc₀, rfl⟩⟩
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image
      (Erdos767LongestCycle.cycleLengths G) id hnonempty
    obtain ⟨z, c, hc, hcm⟩ :=
      Erdos767LongestCycle.mem_cycleLengths_iff.mp hm
    subst m
    have hlong : ∀ (w : V) (d : G.Walk w w),
        d.IsCycle → d.length ≤ c.length := by
      intro w d hd
      have hdmem := Erdos767LongestCycle.mem_cycleLengths_iff.mpr
        ⟨w, d, hd, rfl⟩
      simpa using hmax d.length hdmem
    have hin := two_mul_card_cycleInsideEdges_le hG hc
    have hout := hbondy V G z c hc hlong
    have hpartition := card_inside_add_outside G c.support.toFinset
    have hclen := Erdos767LongestCycle.isCycle_length_le_card hc
    rw [hcard] at hout hclen
    have hsum : c.length + ((k + 1) + (3 * (k + 1) - c.length)) =
        4 * (k + 1) := by omega
    have hamgm := four_mul_le_sq_add c.length
      ((k + 1) + (3 * (k + 1) - c.length))
    rw [hsum] at hamgm
    have hquad : c.length * ((k + 1) + (3 * (k + 1) - c.length)) ≤
        4 * (k + 1) ^ 2 := by
      nlinarith
    have htwo : 2 * G.edgeFinset.card ≤ 4 * (k + 1) ^ 2 := by
      calc
        2 * G.edgeFinset.card =
            2 * (cycleInsideEdges G c.support.toFinset).card +
              2 * (cycleOutsideEdges G c.support.toFinset).card := by omega
        _ ≤ (k + 1) * c.length +
              c.length * (3 * (k + 1) - c.length) := Nat.add_le_add hin hout
        _ = c.length * ((k + 1) + (3 * (k + 1) - c.length)) := by ring
        _ ≤ 4 * (k + 1) ^ 2 := hquad
    omega

/-- Jiang's sharp estimate at the threshold order `3 * (k + 1)`. -/
lemma jiang_base
    (k : ℕ) (hk : 0 < k)
    (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 3 * (k + 1))
    (hG : AvoidsCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤ 2 * (k + 1) ^ 2 := by
  by_cases hacyc : G.IsAcyclic
  · letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hforest := card_edgeFinset_le_card_sub_one_of_isAcyclic G hacyc
    rw [hcard] at hforest
    have hthree : 3 ≤ 2 * (k + 1) := by omega
    have hmul : 3 * (k + 1) ≤ 2 * (k + 1) ^ 2 := by
      calc
        3 * (k + 1) ≤ (2 * (k + 1)) * (k + 1) :=
          Nat.mul_le_mul_right (k + 1) hthree
        _ = 2 * (k + 1) ^ 2 := by ring
    omega
  · have hex : ∃ (z : V) (c : G.Walk z z), c.IsCycle := by
      simp only [SimpleGraph.IsAcyclic] at hacyc
      push Not at hacyc
      obtain ⟨z, c, hc⟩ := hacyc
      exact ⟨z, c, hc⟩
    obtain ⟨z₀, c₀, hc₀⟩ := hex
    have hnonempty : (Erdos767LongestCycle.cycleLengths G).Nonempty := by
      exact ⟨c₀.length,
        Erdos767LongestCycle.mem_cycleLengths_iff.mpr ⟨z₀, c₀, hc₀, rfl⟩⟩
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image
      (Erdos767LongestCycle.cycleLengths G) id hnonempty
    obtain ⟨z, c, hc, hcm⟩ :=
      Erdos767LongestCycle.mem_cycleLengths_iff.mp hm
    subst m
    have hlong : ∀ (w : V) (d : G.Walk w w),
        d.IsCycle → d.length ≤ c.length := by
      intro w d hd
      have hdmem := Erdos767LongestCycle.mem_cycleLengths_iff.mpr
        ⟨w, d, hd, rfl⟩
      simpa using hmax d.length hdmem
    have hbound := cyclic_free_edge_bound k V G z c hG ⟨hc, hlong⟩
    have hclen := Erdos767LongestCycle.isCycle_length_le_card hc
    rw [hcard] at hbound hclen
    have hsum : c.length + ((k + 1) + (3 * (k + 1) - c.length)) =
        4 * (k + 1) := by omega
    have hamgm := four_mul_le_sq_add c.length
      ((k + 1) + (3 * (k + 1) - c.length))
    rw [hsum] at hamgm
    have hquad : c.length * ((k + 1) + (3 * (k + 1) - c.length)) ≤
        4 * (k + 1) ^ 2 := by
      nlinarith
    have htwo : 2 * G.edgeFinset.card ≤ 4 * (k + 1) ^ 2 := by
      calc
        2 * G.edgeFinset.card ≤ (k + 1) * c.length +
            c.length * (3 * (k + 1) - c.length) := hbound
        _ = c.length * ((k + 1) + (3 * (k + 1) - c.length)) := by ring
        _ ≤ 4 * (k + 1) ^ 2 := hquad
    omega

/-- Resolution of Erdős Problem 767: for positive `k` and
`n ≥ 3 * k + 3`, the complete-bipartite construction is extremal. -/
theorem erdos_767 (k n : ℕ) (hk : 0 < k) (hn : 3 * k + 3 ≤ n) :
    chordCycleExtremalNumber k n =
      (k + 1) * n - (k + 1) ^ 2 := by
  apply Nat.le_antisymm
  · obtain ⟨G, hG, hGcard⟩ := exists_extremizer k n
    rw [← hGcard]
    simpa using edge_count_le_of_base k (jiang_base k hk) (Fin n) G
      (by
        rw [Fintype.card_fin]
        omega) hG
  · exact lower_bound k n (by omega)

#print axioms Erdos767.erdos_767

end

end Erdos767
