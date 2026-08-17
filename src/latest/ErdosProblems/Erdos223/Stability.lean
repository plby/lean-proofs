/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos223.Turan
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Data.Finset.CastCard
import Mathlib.Algebra.Order.Chebyshev

/-!
# The finite partition language for Erdős--Simonovits stability

For a map `c : V → Fin p`, `monochromaticEdges G c` is the set of edges of
`G` whose endpoints lie in one fibre of `c`.  Deleting exactly these edges
gives the spanning `p`-partite graph `partiteCore G c`.

This is the form of graph stability used in the proof of Erdős Problem 223:
the fibres are the prospective Lenz classes and `monochromaticEdges` are the
exceptional diameter pairs that still lie inside a class.
-/

open Filter
open scoped SimpleGraph

namespace Erdos223
namespace Stability

open Finset Fintype SimpleGraph

variable {V : Type*} [Fintype V]

/-- Edges whose two endpoints receive the same colour. -/
def monochromaticEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} (c : V → Fin p) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ (e.map c).IsDiag

@[simp] lemma mem_monochromaticEdges {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : ℕ} (c : V → Fin p) {e : Sym2 V} :
    e ∈ monochromaticEdges G c ↔ e ∈ G.edgeFinset ∧ (e.map c).IsDiag := by
  simp [monochromaticEdges]

lemma mk_mem_monochromaticEdges_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : ℕ} (c : V → Fin p) (v w : V) :
    s(v, w) ∈ monochromaticEdges G c ↔ G.Adj v w ∧ c v = c w := by
  simp [monochromaticEdges, Sym2.mk_isDiag_iff]

/-- The spanning subgraph retaining precisely the edges between distinct
colour classes. -/
def partiteCore (G : SimpleGraph V) {p : ℕ} (c : V → Fin p) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ c v ≠ c w
  symm.symm v w h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl v h := h.1.ne rfl

@[simp] lemma partiteCore_adj {G : SimpleGraph V} {p : ℕ} (c : V → Fin p)
    {v w : V} : (partiteCore G c).Adj v w ↔ G.Adj v w ∧ c v ≠ c w := Iff.rfl

noncomputable instance partiteCore.instDecidableRelAdj {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : ℕ} (c : V → Fin p) : DecidableRel (partiteCore G c).Adj :=
  Classical.decRel _

lemma partiteCore_le (G : SimpleGraph V) {p : ℕ} (c : V → Fin p) :
    partiteCore G c ≤ G := fun _ _ h ↦ h.1

/-- The fibres of `c` are independent after the monochromatic edges have
been deleted. -/
def partiteCoreColoring (G : SimpleGraph V) {p : ℕ} (c : V → Fin p) :
    (partiteCore G c).Coloring (Fin p) :=
  Coloring.mk c fun h ↦ h.2

lemma partiteCore_colorable (G : SimpleGraph V) {p : ℕ} (c : V → Fin p) :
    (partiteCore G c).Colorable p := ⟨partiteCoreColoring G c⟩

lemma colorFiber_isIndepSet_partiteCore (G : SimpleGraph V) {p : ℕ}
    (c : V → Fin p) (i : Fin p) :
    (partiteCore G c).IsIndepSet {v | c v = i} := by
  intro v hv w hw _ hvw
  exact hvw.2 (hv.trans hw.symm)

lemma edgeFinset_partiteCore {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : ℕ} (c : V → Fin p) :
    (partiteCore G c).edgeFinset =
      G.edgeFinset.filter fun e ↦ ¬(e.map c).IsDiag := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ v w => simp [Sym2.mk_isDiag_iff]

/-- Exact edge accounting for a prescribed partition. -/
lemma card_edgeFinset_eq_card_partiteCore_add_card_monochromatic
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : ℕ} (c : V → Fin p) :
    #G.edgeFinset = #(partiteCore G c).edgeFinset + #(monochromaticEdges G c) := by
  classical
  rw [edgeFinset_partiteCore]
  unfold monochromaticEdges
  simpa [add_comm] using
    (card_filter_add_card_filter_not
      (s := G.edgeFinset) (p := fun e ↦ (e.map c).IsDiag)).symm

/-- A colourable spanning subgraph with few deleted edges produces the
partition conclusion used by stability. -/
theorem exists_partition_of_colorable_subgraph
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {p k : ℕ} (hHG : H ≤ G) (hcolor : H.Colorable p)
    (hdelete : #G.edgeFinset ≤ #H.edgeFinset + k) :
    ∃ c : V → Fin p, #(monochromaticEdges G c) ≤ k := by
  obtain ⟨C⟩ := hcolor
  refine ⟨C, ?_⟩
  have hcore : H ≤ partiteCore G C := by
    intro v w hvw
    exact ⟨hHG hvw, C.valid hvw⟩
  have hedge : #H.edgeFinset ≤ #(partiteCore G C).edgeFinset :=
    card_le_card (edgeFinset_mono hcore)
  rw [card_edgeFinset_eq_card_partiteCore_add_card_monochromatic C] at hdelete
  omega

/-- The real-valued version avoids rounding when the stability error is
written as `ε n²`. -/
theorem exists_partition_of_colorable_subgraph_real
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {p : ℕ} {K : ℝ} (hHG : H ≤ G) (hcolor : H.Colorable p)
    (hdelete : (#G.edgeFinset : ℝ) ≤ #H.edgeFinset + K) :
    ∃ c : V → Fin p, (#(monochromaticEdges G c) : ℝ) ≤ K := by
  obtain ⟨C⟩ := hcolor
  refine ⟨C, ?_⟩
  have hcore : H ≤ partiteCore G C := by
    intro v w hvw
    exact ⟨hHG hvw, C.valid hvw⟩
  have hedgeNat : #H.edgeFinset ≤ #(partiteCore G C).edgeFinset :=
    card_le_card (edgeFinset_mono hcore)
  have hedge : (#H.edgeFinset : ℝ) ≤ #(partiteCore G C).edgeFinset := by
    exact_mod_cast hedgeNat
  have hcount :=
    card_edgeFinset_eq_card_partiteCore_add_card_monochromatic (G := G) C
  have hcountR : (#G.edgeFinset : ℝ) =
      #(partiteCore G C).edgeFinset + #(monochromaticEdges G C) := by
    exact_mod_cast hcount
  nlinarith

/-! ## Exact counting for the clique-free stability induction -/

/-- Edges with both endpoints in a finite vertex set, counted in the
ambient graph. -/
def edgesInside [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S

@[simp] lemma mem_edgesInside [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V} {e : Sym2 V} :
    e ∈ edgesInside G S ↔ e ∈ G.edgeFinset ∧ e.toFinset ⊆ S := by
  simp [edgesInside]

lemma card_edgesInside [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    #(edgesInside G S) = #(G.induce (↑S : Set V)).edgeFinset := by
  simpa [edgesInside] using G.card_filter_edgeFinset_toFinset_subset S

open Function.Embedding in
lemma card_filter_edgeFinset_eq_card_induce [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    #{x ∈ G.edgeFinset | ∀ v ∈ x, v ∈ s} = #(G.induce s).edgeFinset := by
  rw [← card_map (sym2Map (subtype _))]
  congr
  ext e
  cases e using Sym2.inductionOn with | _ a b
  suffices G.Adj a b ∧ a ∈ s ∧ b ∈ s ↔
      ∃ a' ∈ s, ∃ b', G.Adj a' b' ∧ b' ∈ s ∧
        (a' = a ∧ b' = b ∨ a' = b ∧ b' = a) by
    simpa [Sym2.exists, Function.Embedding.subtype_apply] using this
  simp only [and_or_left, exists_or, ↓existsAndEq]
  tauto

lemma card_edgeFinset_decomp [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    #G.edgeFinset = #(G.induce s).edgeFinset +
      #{e ∈ s ×ˢ sᶜ | G.Adj e.1 e.2} +
      #(G.induce (sᶜ : Finset V)).edgeFinset := by
  rw [← card_filter_add_card_filter_not (∀ v ∈ ·, v ∈ s)]
  nth_rw 2 [← card_filter_add_card_filter_not (∀ v ∈ ·, v ∈ sᶜ), add_comm]
  rw [← add_assoc]
  congr!
  · exact card_filter_edgeFinset_eq_card_induce G _
  · let f (e : V × V) := s(e.1, e.2)
    have fio : Set.InjOn f ({e ∈ s ×ˢ sᶜ | G.Adj e.1 e.2} : Finset _) := by
      rintro ⟨v₁, v₂⟩ mv ⟨w₁, w₂⟩ mw h
      grind [mem_compl]
    rw [← card_image_of_injOn fio]
    congr
    ext e
    cases e using Sym2.inductionOn with | _ a b
    simp_rw [mem_image, mem_filter, f, Prod.exists, mem_edgeFinset, mem_edgeSet]
    suffices (G.Adj a b ∧ (a ∈ s → b ∉ s)) ∧ (a ∉ s → b ∈ s) ↔
        (a ∈ s ∧ b ∉ s) ∧ G.Adj a b ∨ (b ∈ s ∧ a ∉ s) ∧ G.Adj b a by
      simpa [and_or_left, exists_or]
    tauto
  · rw [filter_filter, ← card_filter_edgeFinset_eq_card_induce G]
    congr! with e
    cases e using Sym2.inductionOn with | _ a b
    simp_all

lemma sum_degrees_compl_eq_cross_add_twice_inside [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    ∑ x ∈ sᶜ, G.degree x = #{e ∈ s ×ˢ sᶜ | G.Adj e.1 e.2} +
      2 * #(G.induce (↑sᶜ : Set V)).edgeFinset := by
  classical
  let T : Finset V := sᶜ
  let C : ℕ := #{e ∈ s ×ˢ T | G.Adj e.1 e.2}
  have hsplit (x : V) : G.degree x =
      #(G.neighborFinset x ∩ s) + #(G.neighborFinset x ∩ T) := by
    rw [← G.card_neighborFinset_eq_degree]
    have hd : Disjoint s T := by
      change Disjoint s sᶜ
      exact disjoint_compl_right
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_right Finset.inter_subset_right
        (Finset.disjoint_of_subset_left Finset.inter_subset_right hd))]
    congr
    ext y
    by_cases hy : y ∈ s <;> simp [T, hy]
  have hcross : ∑ x ∈ T, #(G.neighborFinset x ∩ s) = C := by
    dsimp [C]
    calc
      ∑ x ∈ T, #(G.neighborFinset x ∩ s) =
          ∑ x ∈ T, ∑ y ∈ s, if G.Adj x y then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        have heq : G.neighborFinset x ∩ s = s.filter (G.Adj x) := by
          ext y
          simp [and_comm]
        rw [heq, Finset.card_filter]
      _ = ∑ y ∈ s, ∑ x ∈ T, if G.Adj y x then 1 else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro x hx
        simp only [G.adj_comm]
      _ = #{e ∈ s ×ˢ T | G.Adj e.1 e.2} := by
        rw [Finset.card_filter, Finset.sum_product]
  have hinternal : ∑ x ∈ T, #(G.neighborFinset x ∩ T) =
      2 * #(G.induce (↑T : Set V)).edgeFinset := by
    have hdeg (x : T) : (G.induce (↑T : Set V)).degree x =
        #(G.neighborFinset x ∩ T) := by
      rw [← (G.induce (↑T : Set V)).card_neighborFinset_eq_degree]
      refine Finset.card_bij (fun y _ ↦ (y : V)) ?_ ?_ ?_
      · intro y hy
        simpa using hy
      · intro y₁ hy₁ y₂ hy₂ h
        exact Subtype.ext h
      · intro y hy
        refine ⟨⟨y, (Finset.mem_inter.mp hy).2⟩, ?_, rfl⟩
        simpa using (Finset.mem_inter.mp hy).1
    rw [← (G.induce (↑T : Set V)).sum_degrees_eq_twice_card_edges]
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro x hx
    exact (hdeg x).symm
  rw [show sᶜ = T from rfl]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, hcross, hinternal]

/-- If `s` is a maximum-degree neighbourhood, the internal edges in its
complement are controlled by the internal edges in `s` and the complete
cross-term. -/
lemma card_edges_add_induce_compl_le [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    #G.edgeFinset + #(G.induce (↑sᶜ : Set V)).edgeFinset ≤
      #(G.induce (↑s : Set V)).edgeFinset + #sᶜ * G.maxDegree := by
  have hsum : ∑ x ∈ sᶜ, G.degree x ≤ #sᶜ * G.maxDegree := by
    calc
      _ ≤ ∑ _x ∈ sᶜ, G.maxDegree :=
        Finset.sum_le_sum fun x _ ↦ G.degree_le_maxDegree x
      _ = _ := by simp [mul_comm]
  have hdecomp := card_edgeFinset_decomp G s
  have hdegrees := sum_degrees_compl_eq_cross_add_twice_inside G s
  omega

/-- Extend a coloring of an induced subgraph by one new color on its
complement.  A monochromatic edge is then either monochromatic inside the
old set or lies completely in the complement. -/
lemma monochromaticEdges_extension_le [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V) {q : ℕ}
    (cN : {x // x ∈ N} → Fin q) :
    let c : V → Fin (q + 1) := fun x ↦
      if hx : x ∈ N then Fin.castSucc (cN ⟨x, hx⟩) else Fin.last q
    #(monochromaticEdges G c) ≤
      #(monochromaticEdges (G.induce (↑N : Set V)) cN) +
        #(G.induce (↑Nᶜ : Set V)).edgeFinset := by
  classical
  dsimp only
  let c : V → Fin (q + 1) := fun x ↦
    if hx : x ∈ N then Fin.castSucc (cN ⟨x, hx⟩) else Fin.last q
  let f : {x // x ∈ N} ↪ V := Function.Embedding.subtype _
  let A : Finset (Sym2 V) :=
    (monochromaticEdges (G.induce (↑N : Set V)) cN).map f.sym2Map
  let B : Finset (Sym2 V) := edgesInside G Nᶜ
  have hsub : monochromaticEdges G c ⊆ A ∪ B := by
    intro e he
    rw [mem_monochromaticEdges] at he
    rcases e with ⟨⟨x, y⟩⟩
    simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at he
    have hxy : G.Adj x y := by simpa using he.1
    by_cases hx : x ∈ N
    · have hy : y ∈ N := by
        by_contra hy
        have hc : Fin.castSucc (cN ⟨x, hx⟩) = Fin.last q := by
          simpa [c, hx, hy] using he.2
        exact Fin.castSucc_ne_last _ hc
      apply Finset.mem_union.mpr
      left
      let xN : {x // x ∈ N} := ⟨x, hx⟩
      let yN : {x // x ∈ N} := ⟨y, hy⟩
      simp only [A, Finset.mem_map]
      refine ⟨s(xN, yN), ?_, ?_⟩
      · rw [mem_monochromaticEdges]
        constructor
        · simpa [xN, yN] using hxy
        · simpa [xN, yN, c, hx, hy] using he.2
      · simp [f, xN, yN]
    · have hy : y ∉ N := by
        intro hy
        have hc : Fin.castSucc (cN ⟨y, hy⟩) = Fin.last q := by
          simpa [c, hx, hy] using he.2.symm
        exact Fin.castSucc_ne_last _ hc
      apply Finset.mem_union.mpr
      right
      simp only [B, mem_edgesInside]
      refine ⟨he.1, ?_⟩
      intro z hz
      rw [mem_compl]
      simp [Sym2.toFinset_mk_eq] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
  calc
    #(monochromaticEdges G c) ≤ #(A ∪ B) := card_le_card hsub
    _ ≤ #A + #B := card_union_le _ _
    _ = _ := by simp [A, B, card_edgesInside]

/-- Füredi's exact defect form of Turán's theorem: a `K_(p+1)`-free
graph has a `p`-coloring for which the number of edges plus the number of
monochromatic edges is at most the continuous Turán bound. -/
theorem cliqueFree_majorization (p : ℕ) (hp : 0 < p)
    {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (hfree : G.CliqueFree (p + 1)) :
    ∃ c : W → Fin p,
      (#G.edgeFinset : ℝ) + #(monochromaticEdges G c) ≤
        ((p : ℝ) - 1) / (2 * p) * (Fintype.card W : ℝ) ^ 2 := by
  induction p using Nat.strong_induction_on generalizing W with
  | h p ih =>
      classical
      obtain rfl | q := p
      · omega
      by_cases hq : q = 0
      · subst q
        have hbot : G = ⊥ := SimpleGraph.cliqueFree_two.mp (by simpa using hfree)
        subst G
        let c : W → Fin 1 := fun _ ↦ 0
        refine ⟨c, ?_⟩
        simp [monochromaticEdges]
      have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      cases isEmpty_or_nonempty W with
      | inl hW =>
          let c : W → Fin (q + 1) := fun x ↦ isEmptyElim x
          refine ⟨c, ?_⟩
          have he : #G.edgeFinset = 0 := by
            apply Nat.eq_zero_of_le_zero
            simpa [Fintype.card_eq_zero] using G.card_edgeFinset_le_card_choose_two
          simp [monochromaticEdges, he]
      | inr hW =>
          obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
          let N : Finset W := G.neighborFinset v
          have hNcard : #N = G.maxDegree := by
            rw [hv, G.card_neighborFinset_eq_degree]
          have hcfOn : G.CliqueFreeOn (↑N : Set W) (q + 1) := by
            have h := SimpleGraph.CliqueFreeOn.of_succ
              (G := G) (s := Set.univ) (a := v)
              (hfree.cliqueFreeOn (s := Set.univ)) (Set.mem_univ v)
            simpa [N] using h
          have hcfN : (G.induce (↑N : Set W)).CliqueFree (q + 1) :=
            (SimpleGraph.cliqueFree_induce_iff (G := G) (↑N : Set W) (q + 1)).2 hcfOn
          obtain ⟨cN, hcN⟩ := ih q (by omega) hqpos (G.induce (↑N : Set W)) hcfN
          let c : W → Fin (q + 1) := fun x ↦
            if hx : x ∈ N then Fin.castSucc (cN ⟨x, hx⟩) else Fin.last q
          refine ⟨c, ?_⟩
          have hmono := monochromaticEdges_extension_le G N cN
          have hedge := card_edges_add_induce_compl_le G N
          have hcard : #N + #Nᶜ = Fintype.card W := by
            rw [card_add_card_compl]
          have hmonoR : (#(monochromaticEdges G c) : ℝ) ≤
              #(monochromaticEdges (G.induce (↑N : Set W)) cN) +
                #(G.induce (↑Nᶜ : Set W)).edgeFinset := by
            exact_mod_cast hmono
          have hedgeR : (#G.edgeFinset : ℝ) +
                #(G.induce (↑Nᶜ : Set W)).edgeFinset ≤
              #(G.induce (↑N : Set W)).edgeFinset + (#Nᶜ : ℝ) * #N := by
            rw [hNcard]
            exact_mod_cast hedge
          have hrec :
              ((q : ℝ) - 1) / (2 * q) * (#N : ℝ) ^ 2 + (#Nᶜ : ℝ) * #N ≤
                (((q + 1 : ℕ) : ℝ) - 1) / (2 * (q + 1)) *
                  ((#N : ℝ) + #Nᶜ) ^ 2 := by
            have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
            norm_num [Nat.cast_add, Nat.cast_one]
            field_simp
            nlinarith [sq_nonneg ((q : ℝ) * (#Nᶜ : ℝ) - (#N : ℝ))]
          have hcN' : (#(G.induce (↑N : Set W)).edgeFinset : ℝ) +
                #(monochromaticEdges (G.induce (↑N : Set W)) cN) ≤
              ((q : ℝ) - 1) / (2 * q) * (#N : ℝ) ^ 2 := by
            simpa using hcN
          have hcomb : (#G.edgeFinset : ℝ) + #(monochromaticEdges G c) ≤
              (#(G.induce (↑N : Set W)).edgeFinset : ℝ) +
                #(monochromaticEdges (G.induce (↑N : Set W)) cN) +
                  (#Nᶜ : ℝ) * #N := by
            linarith
          calc
            (#G.edgeFinset : ℝ) + #(monochromaticEdges G c)
                ≤ (#(G.induce (↑N : Set W)).edgeFinset : ℝ) +
                    #(monochromaticEdges (G.induce (↑N : Set W)) cN) +
                      (#Nᶜ : ℝ) * #N := hcomb
            _ ≤ ((q : ℝ) - 1) / (2 * q) * (#N : ℝ) ^ 2 +
                  (#Nᶜ : ℝ) * #N := by linarith
            _ ≤ (((q + 1 : ℕ) : ℝ) - 1) / (2 * (q + 1)) *
                  ((#N : ℝ) + #Nᶜ) ^ 2 := hrec
            _ = (((q + 1 : ℕ) : ℝ) - 1) / (2 * ((q : ℝ) + 1)) *
                  (Fintype.card W : ℝ) ^ 2 := by
              rw [← Nat.cast_add, hcard]
            _ = (((q + 1 : ℕ) : ℝ) - 1) / (2 * ((q + 1 : ℕ) : ℝ)) *
                  (Fintype.card W : ℝ) ^ 2 := by
              norm_num [Nat.cast_add, Nat.cast_one]

/-! ## Edge loss in a parameter-separated regularity reduction -/

open SzemerediRegularity

/-- The edges omitted by a reduced graph lie in a nonuniform pair, inside
one partition class, or in a pair below the density threshold.  Mathlib's
version fixes the two parameters in a `1 : 2` ratio; the separated form is
needed to embed a fixed multipartite graph. -/
lemma unreduced_edges_subset_general
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ρ d : ℝ} :
    (univ ×ˢ univ).filter (fun (x, y) ↦
        G.Adj x y ∧ ¬(G.regularityReduced P ρ d).Adj x y) ⊆
      (P.nonUniforms G ρ).biUnion (fun (U, W) ↦ U ×ˢ W) ∪
        P.parts.biUnion offDiag ∪
          (P.sparsePairs G d).biUnion fun (U, W) ↦ G.interedges U W := by
  rintro ⟨x, y⟩
  simp only [mem_filter, SimpleGraph.regularityReduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs,
    SimpleGraph.mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem hx
  obtain ⟨W, hW, hy⟩ := P.exists_mem hy
  obtain rfl | hUW := eq_or_ne U W
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases h₂ : G.IsUniform ρ U W
  · exact Or.inr <| Or.inr ⟨U, W, hU, hW, hUW, h' _ hU _ hW hx hy hUW h₂,
      hx, hy, h⟩
  · exact Or.inl ⟨U, W, hU, hW, hUW, h₂, hx, hy⟩

/-- General reduced-graph edge loss. `ρ` is the regularity tolerance,
`d` the density threshold, and `ξ` controls the loss inside partition
classes through the lower bound `4 / ξ` on the number of classes. -/
lemma regularityReduced_edge_loss_lt_general
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    {P : Finpartition (univ : Finset V)} {ρ d ξ : ℝ}
    (hρ : 0 < ρ) (hd : 0 ≤ d) (hξ : 0 < ξ)
    (hP : P.IsEquipartition) (hPρ : P.IsUniform G ρ)
    (hP' : 4 / ξ ≤ #P.parts) :
    (#G.edgeFinset - #(G.regularityReduced P ρ d).edgeFinset : ℝ)
      < (2 * ρ + ξ / 4 + 2 * d) * (Fintype.card V : ℝ) ^ 2 := by
  let A := (P.nonUniforms G ρ).biUnion fun (U, W) ↦ U ×ˢ W
  let B := P.parts.biUnion offDiag
  let C := (P.sparsePairs G d).biUnion fun (U, W) ↦ G.interedges U W
  have htwo :
      2 * (#G.edgeFinset - #(G.regularityReduced P ρ d).edgeFinset : ℝ)
        < (4 * ρ + ξ / 2 + 4 * d) * (Fintype.card V : ℝ) ^ 2 := by
    calc
      _ = (#((univ ×ˢ univ).filter fun (x, y) ↦
            G.Adj x y ∧ ¬(G.regularityReduced P ρ d).Adj x y) : ℝ) := by
        rw [univ_product_univ, mul_sub, filter_and_not, cast_card_sdiff]
        · norm_cast
          rw [SimpleGraph.two_mul_card_edgeFinset, SimpleGraph.two_mul_card_edgeFinset]
        · gcongr with xy _
          exact fun hxy ↦ SimpleGraph.regularityReduced_le hxy
      _ ≤ #(A ∪ B ∪ C) := by
        gcongr
        exact unreduced_edges_subset_general
      _ ≤ #(A ∪ B) + #C := mod_cast card_union_le _ _
      _ ≤ #A + #B + #C := by gcongr; exact_mod_cast card_union_le _ _
      _ < 4 * ρ * Fintype.card V ^ 2 + _ + _ := by
        gcongr
        exact hP.sum_nonUniforms_lt univ_nonempty hρ hPρ
      _ ≤ _ + ξ / 2 * Fintype.card V ^ 2 + 4 * d * Fintype.card V ^ 2 := by
        gcongr
        · exact hP.card_biUnion_offDiag_le hξ hP'
        · exact hP.card_interedges_sparsePairs_le (G := G) hd
      _ = (4 * ρ + ξ / 2 + 4 * d) * (Fintype.card V : ℝ) ^ 2 := by ring
  nlinarith

/-- An edge of the reduced graph canonically identifies two distinct
partition classes and certifies that the pair is regular and dense. -/
lemma regularityReduced_adj_parts
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ρ d : ℝ} {x y : V}
    (hxy : (G.regularityReduced P ρ d).Adj x y) :
    P.part x ≠ P.part y ∧ G.IsUniform ρ (P.part x) (P.part y) ∧
      d ≤ G.edgeDensity (P.part x) (P.part y) := by
  obtain ⟨-, U, hU, W, hW, hxU, hyW, hUW, hreg, hd⟩ := hxy
  have hx : P.part x = U := P.part_eq_of_mem hU hxU
  have hy : P.part y = W := P.part_eq_of_mem hW hyW
  simpa [hx, hy] using ⟨hUW, hreg, hd⟩

lemma part_injectiveOn_of_isClique_regularityReduced
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ρ d : ℝ} {s : Finset V}
    (hs : (G.regularityReduced P ρ d).IsClique s) :
    Set.InjOn P.part s := by
  intro x hx y hy hparts
  by_contra hxy
  exact (regularityReduced_adj_parts (hs hx hy hxy)).1 hparts

lemma uniform_dense_parts_of_isClique_regularityReduced
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ρ d : ℝ} {s : Finset V}
    (hs : (G.regularityReduced P ρ d).IsClique s)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    G.IsUniform ρ (P.part x) (P.part y) ∧
      d ≤ G.edgeDensity (P.part x) (P.part y) :=
  (regularityReduced_adj_parts (hs hx hy hxy)).2

/-- Canonically enumerate the partition classes represented by an
`r`-clique of the reduced graph. -/
noncomputable def reducedCliqueParts
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ρ d : ℝ} {r : ℕ} {s : Finset V}
    (hs : (G.regularityReduced P ρ d).IsNClique r s) :
    Fin r → Finset V :=
  fun i ↦ P.part ((Finset.equivFinOfCardEq hs.card_eq).symm i).1

lemma reducedCliqueParts_mem_parts
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ρ d : ℝ} {r : ℕ} {s : Finset V}
    (hs : (G.regularityReduced P ρ d).IsNClique r s) (i : Fin r) :
    reducedCliqueParts hs i ∈ P.parts := by
  apply P.part_mem.2
  simp

lemma reducedCliqueParts_ne
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ρ d : ℝ} {r : ℕ} {s : Finset V}
    (hs : (G.regularityReduced P ρ d).IsNClique r s)
    {i j : Fin r} (hij : i ≠ j) :
    reducedCliqueParts hs i ≠ reducedCliqueParts hs j := by
  let e := (Finset.equivFinOfCardEq hs.card_eq).symm
  have he : e i ≠ e j := e.injective.ne hij
  have hadj : (G.regularityReduced P ρ d).Adj (e i).1 (e j).1 :=
    hs.isClique (e i).2 (e j).2 (fun h ↦ he (Subtype.ext h))
  exact (regularityReduced_adj_parts hadj).1

lemma reducedCliqueParts_uniform_dense
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ρ d : ℝ} {r : ℕ} {s : Finset V}
    (hs : (G.regularityReduced P ρ d).IsNClique r s)
    {i j : Fin r} (hij : i ≠ j) :
    G.IsUniform ρ (reducedCliqueParts hs i) (reducedCliqueParts hs j) ∧
      d ≤ G.edgeDensity (reducedCliqueParts hs i) (reducedCliqueParts hs j) := by
  let e := (Finset.equivFinOfCardEq hs.card_eq).symm
  have he : e i ≠ e j := e.injective.ne hij
  exact (regularityReduced_adj_parts <|
    hs.isClique (e i).2 (e j).2 (fun h ↦ he (Subtype.ext h))).2

lemma reducedCliqueParts_disjoint
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ρ d : ℝ} {r : ℕ} {s : Finset V}
    (hs : (G.regularityReduced P ρ d).IsNClique r s)
    {i j : Fin r} (hij : i ≠ j) :
    Disjoint (reducedCliqueParts hs i) (reducedCliqueParts hs j) :=
  P.disjoint (reducedCliqueParts_mem_parts hs i) (reducedCliqueParts_mem_parts hs j)
    (reducedCliqueParts_ne hs hij)

/-- Package a coordinate family of equal-sized, pairwise completely joined
sets into Mathlib's complete-equipartite containment interface. -/
lemma completeEquipartiteGraph_isContained_of_parts
    {G : SimpleGraph V} {r t : ℕ} (C : Fin r → Finset V)
    (hCinj : Function.Injective C)
    (hcard : ∀ i, #(C i) = t)
    (hcomplete : ∀ ⦃i j : Fin r⦄, i ≠ j → G.IsCompleteBetween (C i) (C j)) :
    completeEquipartiteGraph r t ⊑ G := by
  let f : Fin r ↪ Finset V := ⟨C, hCinj⟩
  let K : G.CompleteEquipartiteSubgraph r t := by
    refine ⟨univ.map f, ?_, ?_, ?_⟩
    · left
      simp [f]
    · intro p hp
      simp only [Finset.mem_map, mem_univ, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      exact hcard i
    · intro p hp q hq hpq
      simp only [mem_coe, Finset.mem_map, mem_univ, true_and] at hp hq
      obtain ⟨i, rfl⟩ := hp
      obtain ⟨j, rfl⟩ := hq
      apply hcomplete
      intro hij
      apply hpq
      exact congrArg C hij
  exact completeEquipartiteGraph_isContained_iff.2 ⟨K⟩

/-- End-to-end regularity reduction, conditional only on the fixed-size
embedding lemma. -/
lemma exists_cliqueFree_regularityReduced_of_embedding
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    {r : ℕ} {ρ d ξ : ℝ}
    (hρ : 0 < ρ) (hd : 0 ≤ d) (hξ : 0 < ξ)
    (hl : ⌈4 / ξ⌉₊ ≤ Fintype.card V)
    (hfree : (completeEquipartiteGraph r 3).Free G)
    (hembed : ∀ (P : Finpartition (univ : Finset V)),
      P.IsEquipartition → P.IsUniform G ρ →
      ∀ s, (G.regularityReduced P ρ d).IsNClique r s →
        completeEquipartiteGraph r 3 ⊑ G) :
    ∃ P : Finpartition (univ : Finset V),
      P.IsEquipartition ∧ P.IsUniform G ρ ∧
      (G.regularityReduced P ρ d).CliqueFree r ∧
      (G.regularityReduced P ρ d ≤ G) ∧
      (#G.edgeFinset - #(G.regularityReduced P ρ d).edgeFinset : ℝ)
        < (2 * ρ + ξ / 4 + 2 * d) * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, hPeq, hPlower, -, hPreg⟩ :=
    szemeredi_regularity G hρ hl
  have hPparts : 4 / ξ ≤ (#P.parts : ℝ) :=
    (Nat.le_ceil (4 / ξ)).trans (Nat.cast_le.2 hPlower)
  have hclique : (G.regularityReduced P ρ d).CliqueFree r := by
    intro s hs
    exact hfree (hembed P hPeq hPreg s hs)
  exact ⟨P, hPeq, hPreg, hclique, SimpleGraph.regularityReduced_le,
    regularityReduced_edge_loss_lt_general hρ hd hξ hPeq hPreg hPparts⟩

/-- Same reduction with the large-cluster estimate needed by a concrete
greedy embedding theorem. -/
lemma exists_cliqueFree_regularityReduced_of_large_clusters
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    {r M : ℕ} {ρ d ξ : ℝ}
    (hρ : 0 < ρ) (hd : 0 ≤ d) (hξ : 0 < ξ)
    (hl : ⌈4 / ξ⌉₊ ≤ Fintype.card V)
    (hlarge : M * SzemerediRegularity.bound ρ ⌈4 / ξ⌉₊ ≤ Fintype.card V)
    (hfree : (completeEquipartiteGraph r 3).Free G)
    (hembed : ∀ (P : Finpartition (univ : Finset V)),
      P.IsEquipartition → P.IsUniform G ρ →
      ∀ s, (G.regularityReduced P ρ d).IsNClique r s →
        (∀ x ∈ s, M ≤ #(P.part x)) →
        completeEquipartiteGraph r 3 ⊑ G) :
    ∃ P : Finpartition (univ : Finset V),
      P.IsEquipartition ∧ P.IsUniform G ρ ∧
      (G.regularityReduced P ρ d).CliqueFree r ∧
      (G.regularityReduced P ρ d ≤ G) ∧
      (#G.edgeFinset - #(G.regularityReduced P ρ d).edgeFinset : ℝ)
        < (2 * ρ + ξ / 4 + 2 * d) * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, hPeq, hPlower, hPupper, hPreg⟩ :=
    szemeredi_regularity G hρ hl
  have hPparts : 4 / ξ ≤ (#P.parts : ℝ) :=
    (Nat.le_ceil (4 / ξ)).trans (Nat.cast_le.2 hPlower)
  have hkpos : 0 < #P.parts := (P.parts_nonempty univ_nonempty.ne_empty).card_pos
  have hMk : M * #P.parts ≤ Fintype.card V :=
    (Nat.mul_le_mul_left M hPupper).trans hlarge
  have hMavg : M ≤ Fintype.card V / #P.parts :=
    (Nat.le_div_iff_mul_le hkpos).2 hMk
  have hcluster : ∀ x : V, M ≤ #(P.part x) := by
    intro x
    exact hMavg.trans (hPeq.average_le_card_part (P.part_mem.2 (mem_univ x)))
  have hclique : (G.regularityReduced P ρ d).CliqueFree r := by
    intro s hs
    exact hfree (hembed P hPeq hPreg s hs fun x _ ↦ hcluster x)
  exact ⟨P, hPeq, hPreg, hclique, SimpleGraph.regularityReduced_le,
    regularityReduced_edge_loss_lt_general hρ hd hξ hPeq hPreg hPparts⟩

variable {V : Type*} [Fintype V]

/-- The vertices in one fiber of a proposed Turan coloring. -/
noncomputable def colorFiber {p : ℕ} (c : V → Fin p) (i : Fin p) : Finset V :=
  Finset.univ.filter fun v ↦ c v = i

@[simp] lemma mem_colorFiber {p : ℕ} (c : V → Fin p) (i : Fin p) (v : V) :
    v ∈ colorFiber c i ↔ c v = i := by
  classical simp [colorFiber]

lemma sum_card_colorFiber {p : ℕ} (c : V → Fin p) :
    ∑ i, #(colorFiber c i) = Fintype.card V := by
  classical
  symm
  simpa [colorFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset (Fin p)))
      (f := c) (by simp))

/-- The complete multipartite graph associated to `c`. -/
def completeCrossGraph {p : ℕ} (c : V → Fin p) : SimpleGraph V :=
  partiteCore (⊤ : SimpleGraph V) c

noncomputable instance completeCrossGraph.instDecidableRelAdj
    {p : ℕ} (c : V → Fin p) : DecidableRel (completeCrossGraph c).Adj :=
  Classical.decRel _

@[simp] lemma completeCrossGraph_adj {p : ℕ} (c : V → Fin p) {v w : V} :
    (completeCrossGraph c).Adj v w ↔ c v ≠ c w := by
  change (v ≠ w ∧ c v ≠ c w) ↔ c v ≠ c w
  exact ⟨And.right, fun h ↦ ⟨fun hvw ↦ h (congrArg c hvw), h⟩⟩

/-- The graph of missing cross edges of `G` relative to `c`. -/
def crossNonedgeGraph (G : SimpleGraph V) {p : ℕ} (c : V → Fin p) : SimpleGraph V :=
  { Adj := fun v w ↦ c v ≠ c w ∧ ¬ G.Adj v w
    symm := by
      constructor
      rintro v w ⟨hc, hG⟩
      exact ⟨hc.symm, fun hwv ↦ hG hwv.symm⟩
    loopless := ⟨fun v h ↦ h.1 rfl⟩ }

@[simp] lemma crossNonedgeGraph_adj (G : SimpleGraph V) {p : ℕ}
    (c : V → Fin p) {v w : V} :
    (crossNonedgeGraph G c).Adj v w ↔ c v ≠ c w ∧ ¬ G.Adj v w := by
  rfl

noncomputable instance crossNonedgeGraph.instDecidableRelAdj
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (c : V → Fin p) :
    DecidableRel (crossNonedgeGraph G c).Adj := Classical.decRel _

lemma partiteCore_le_completeCrossGraph (G : SimpleGraph V) {p : ℕ}
    (c : V → Fin p) : partiteCore G c ≤ completeCrossGraph c := by
  intro v w h
  exact (completeCrossGraph_adj c).2 h.2

/-- Exact accounting: all potential cross edges are either present or missing. -/
lemma card_completeCrossGraph_eq_card_partiteCore_add_card_crossNonedge
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (c : V → Fin p) :
    #(completeCrossGraph c).edgeFinset =
      #(partiteCore G c).edgeFinset + #(crossNonedgeGraph G c).edgeFinset := by
  classical
  have hedge : (crossNonedgeGraph G c).edgeFinset =
      (completeCrossGraph c).edgeFinset \ (partiteCore G c).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ v w =>
        simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, crossNonedgeGraph_adj,
          completeCrossGraph_adj, partiteCore_adj]
        tauto
  have hcard : #(partiteCore G c).edgeFinset ≤ #(completeCrossGraph c).edgeFinset :=
    Finset.card_le_card (edgeFinset_mono (partiteCore_le_completeCrossGraph G c))
  rw [hedge,
    card_sdiff_of_subset (edgeFinset_mono (partiteCore_le_completeCrossGraph G c))]
  omega

lemma degree_completeCrossGraph {p : ℕ} (c : V → Fin p) (v : V) :
    (completeCrossGraph c).degree v = Fintype.card V - #(colorFiber c (c v)) := by
  classical
  rw [degree, neighborFinset_eq_filter]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (p := fun w ↦ c w = c v)
  simp only [completeCrossGraph_adj]
  have heq : #{w : V | c v ≠ c w} =
      #{w : V | ¬ c w = c v} := by
    congr 1
    ext w
    simp [ne_comm]
  rw [heq]
  simp only [Finset.card_univ] at hsplit ⊢
  have hfiber : #{w : V | c w = c v} = #(colorFiber c (c v)) := by
    simp [colorFiber]
  rw [hfiber] at hsplit
  omega

lemma sum_colorFiber_card_comp {p : ℕ} (c : V → Fin p) :
    (∑ v, (#(colorFiber c (c v)) : ℝ)) =
      ∑ i, (#(colorFiber c i) : ℝ) ^ 2 := by
  classical
  have h := Finset.sum_fiberwise'
    (s := (Finset.univ : Finset V)) c
    (fun i ↦ (#(colorFiber c i) : ℝ))
  simpa [colorFiber, pow_two] using h.symm

/-- The standard identity `2e = n² - sum_i |V_i|²` for a complete
multipartite graph. -/
lemma two_mul_card_completeCrossGraph {p : ℕ} (c : V → Fin p) :
    2 * (#(completeCrossGraph c).edgeFinset : ℝ) =
      (Fintype.card V : ℝ) ^ 2 - ∑ i, (#(colorFiber c i) : ℝ) ^ 2 := by
  classical
  have hdegree := (completeCrossGraph c).sum_degrees_eq_twice_card_edges
  have hdegreeR :
      (∑ v, ((completeCrossGraph c).degree v : ℝ)) =
        2 * (#(completeCrossGraph c).edgeFinset : ℝ) := by
    exact_mod_cast hdegree
  have hdeg (v : V) : ((completeCrossGraph c).degree v : ℝ) =
      (Fintype.card V : ℝ) - #(colorFiber c (c v)) := by
    rw [degree_completeCrossGraph]
    exact_mod_cast Nat.cast_sub (Finset.card_le_univ (colorFiber c (c v)))
  rw [show (∑ v, ((completeCrossGraph c).degree v : ℝ)) =
      ∑ v, ((Fintype.card V : ℝ) - #(colorFiber c (c v))) by
        exact Finset.sum_congr rfl fun v _ ↦ hdeg v] at hdegreeR
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Fintype.card, sum_colorFiber_card_comp] at hdegreeR
  simp only [Finset.card_univ] at hdegreeR
  nlinarith

/-- Every complete `p`-partite graph is bounded by the continuous Turan
coefficient. -/
lemma card_completeCrossGraph_le_turanCoefficient {p : ℕ} (hp : 0 < p)
    (c : V → Fin p) :
    (#(completeCrossGraph c).edgeFinset : ℝ) ≤
      ((p : ℝ) - 1) / (2 * p) * (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hsum : (∑ i, (#(colorFiber c i) : ℝ)) = (Fintype.card V : ℝ) := by
    exact_mod_cast sum_card_colorFiber c
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin p)))
    (f := fun i ↦ (#(colorFiber c i) : ℝ))
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  rw [hsum] at hcs
  have hid := two_mul_card_completeCrossGraph c
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * p)).2
  nlinarith

/-- The sum of squared deviations from the average fiber size. -/
lemma sum_sq_colorFiber_sub_average {p : ℕ} (hp : 0 < p)
    (c : V → Fin p) :
    (∑ i, ((#(colorFiber c i) : ℝ) - (Fintype.card V : ℝ) / p) ^ 2) =
      (∑ i, (#(colorFiber c i) : ℝ) ^ 2) -
        (Fintype.card V : ℝ) ^ 2 / p := by
  classical
  have hsum : (∑ i, (#(colorFiber c i) : ℝ)) = (Fintype.card V : ℝ) := by
    exact_mod_cast sum_card_colorFiber c
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlin : (∑ x, 2 * (#(colorFiber c x) : ℝ) *
      ((Fintype.card V : ℝ) / p)) =
      2 * (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) / p) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
  rw [hlin]
  field_simp
  ring

/-- Few monochromatic edges and near-Turan total edge count force few
missing cross edges. -/
lemma card_crossNonedgeGraph_le
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (hp : 0 < p)
    (c : V → Fin p) {eta : ℝ}
    (hmono : (#(monochromaticEdges G c) : ℝ) ≤
      eta * (Fintype.card V : ℝ) ^ 2)
    (htotal : (((p : ℝ) - 1) / (2 * p) - eta) *
        (Fintype.card V : ℝ) ^ 2 ≤ (#G.edgeFinset : ℝ)) :
    (#(crossNonedgeGraph G c).edgeFinset : ℝ) ≤
      2 * eta * (Fintype.card V : ℝ) ^ 2 := by
  have hG := card_edgeFinset_eq_card_partiteCore_add_card_monochromatic
    (G := G) c
  have hGR : (#G.edgeFinset : ℝ) =
      #(partiteCore G c).edgeFinset + #(monochromaticEdges G c) := by
    exact_mod_cast hG
  have hcross := card_completeCrossGraph_eq_card_partiteCore_add_card_crossNonedge G c
  have hcrossR : (#(completeCrossGraph c).edgeFinset : ℝ) =
      #(partiteCore G c).edgeFinset + #(crossNonedgeGraph G c).edgeFinset := by
    exact_mod_cast hcross
  have hupper := card_completeCrossGraph_le_turanCoefficient hp c
  nlinarith

/-- Quantitative balance of every full color fiber.  The loose constant
`16 * eta < epsilon²` is chosen to dovetail with the exceptional-vertex
deletion below. -/
lemma abs_card_colorFiber_sub_average_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (hp : 0 < p)
    (c : V → Fin p) {eta epsilon : ℝ}
    (hn : 0 < Fintype.card V) (hepsilon : 0 < epsilon)
    (heta : 16 * eta < epsilon ^ 2)
    (hmono : (#(monochromaticEdges G c) : ℝ) ≤
      eta * (Fintype.card V : ℝ) ^ 2)
    (htotal : (((p : ℝ) - 1) / (2 * p) - eta) *
        (Fintype.card V : ℝ) ^ 2 ≤ (#G.edgeFinset : ℝ))
    (i : Fin p) :
    |(#(colorFiber c i) : ℝ) - (Fintype.card V : ℝ) / p| <
      epsilon / 2 * (Fintype.card V : ℝ) := by
  have hG := card_edgeFinset_eq_card_partiteCore_add_card_monochromatic
    (G := G) c
  have hGR : (#G.edgeFinset : ℝ) =
      #(partiteCore G c).edgeFinset + #(monochromaticEdges G c) := by
    exact_mod_cast hG
  have hcoreleNat : #(partiteCore G c).edgeFinset ≤
      #(completeCrossGraph c).edgeFinset :=
    Finset.card_le_card (edgeFinset_mono (partiteCore_le_completeCrossGraph G c))
  have hcorele : (#(partiteCore G c).edgeFinset : ℝ) ≤
      #(completeCrossGraph c).edgeFinset := by exact_mod_cast hcoreleNat
  have hid := two_mul_card_completeCrossGraph c
  have hdev := sum_sq_colorFiber_sub_average hp c
  have hsumsq :
      (∑ j, ((#(colorFiber c j) : ℝ) - (Fintype.card V : ℝ) / p) ^ 2) ≤
        4 * eta * (Fintype.card V : ℝ) ^ 2 := by
    have hcoeff : ((p : ℝ) - 1) / (2 * p) =
        (1 - 1 / (p : ℝ)) / 2 := by
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      field_simp
    rw [hcoeff] at htotal
    rw [hdev]
    ring_nf at htotal ⊢
    nlinarith
  have hi : ((#(colorFiber c i) : ℝ) - (Fintype.card V : ℝ) / p) ^ 2 ≤
      ∑ j, ((#(colorFiber c j) : ℝ) - (Fintype.card V : ℝ) / p) ^ 2 := by
    exact Finset.single_le_sum
      (f := fun j ↦ ((#(colorFiber c j) : ℝ) - (Fintype.card V : ℝ) / p) ^ 2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
  have hisq := hi.trans hsumsq
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  by_contra hnot
  have habs : epsilon / 2 * (Fintype.card V : ℝ) ≤
      |(#(colorFiber c i) : ℝ) - (Fintype.card V : ℝ) / p| :=
    le_of_not_gt hnot
  have hsquarelower :
      (epsilon / 2 * (Fintype.card V : ℝ)) ^ 2 ≤
        |(#(colorFiber c i) : ℝ) - (Fintype.card V : ℝ) / p| ^ 2 :=
    (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 habs
  rw [sq_abs] at hsquarelower
  have hetaN : 16 * eta * (Fintype.card V : ℝ) ^ 2 <
      epsilon ^ 2 * (Fintype.card V : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right heta (sq_pos_of_pos hnR)
  nlinarith

/-- Vertices incident to at least `epsilon * n` missing cross edges. -/
noncomputable def exceptionalVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} (c : V → Fin p) (epsilon : ℝ) : Finset V :=
  Finset.univ.filter fun v ↦
    epsilon * (Fintype.card V : ℝ) ≤ (crossNonedgeGraph G c).degree v

@[simp] lemma mem_exceptionalVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} (c : V → Fin p) (epsilon : ℝ) (v : V) :
    v ∈ exceptionalVertices G c epsilon ↔
      epsilon * (Fintype.card V : ℝ) ≤ (crossNonedgeGraph G c).degree v := by
  classical simp [exceptionalVertices]

/-- Delete `S0` from one color fiber. -/
noncomputable def retainedFiber {p : ℕ} (c : V → Fin p)
    (S0 : Finset V) (i : Fin p) : Finset V :=
  by
    classical
    exact colorFiber c i \ S0

@[simp] lemma mem_retainedFiber {p : ℕ} (c : V → Fin p)
    (S0 : Finset V) (i : Fin p) (v : V) :
    v ∈ retainedFiber c S0 i ↔ c v = i ∧ v ∉ S0 := by
  classical simp [retainedFiber]

/-- Missing cross neighbors of `v` that survive deletion of `S0`.  This is
exactly the set of nonneighbors of `v` in the union of the other retained
fibers. -/
noncomputable def retainedCrossNonneighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (c : V → Fin p)
    (S0 : Finset V) (v : V) : Finset V :=
  by
    classical
    exact (crossNonedgeGraph G c).neighborFinset v \ S0

@[simp] lemma mem_retainedCrossNonneighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (c : V → Fin p)
    (S0 : Finset V) (v w : V) :
    w ∈ retainedCrossNonneighbors G c S0 v ↔
      w ∉ S0 ∧ c v ≠ c w ∧ ¬ G.Adj v w := by
  classical
  simp only [retainedCrossNonneighbors, Finset.mem_sdiff,
    SimpleGraph.mem_neighborFinset, crossNonedgeGraph_adj]
  tauto

/-- Markov's inequality for the exceptional vertices, with the handshaking
identity supplying the factor two. -/
lemma card_exceptionalVertices_mul_le
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (c : V → Fin p)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (#(exceptionalVertices G c epsilon) : ℝ) *
        (epsilon * (Fintype.card V : ℝ)) ≤
      2 * (#(crossNonedgeGraph G c).edgeFinset : ℝ) := by
  classical
  let M := crossNonedgeGraph G c
  let S0 := exceptionalVertices G c epsilon
  calc
    (#S0 : ℝ) * (epsilon * (Fintype.card V : ℝ)) =
        ∑ v ∈ S0, epsilon * (Fintype.card V : ℝ) := by simp
    _ ≤ ∑ v ∈ S0, (M.degree v : ℝ) := by
      gcongr with v hv
      exact (mem_exceptionalVertices G c epsilon v).1 hv
    _ ≤ ∑ v ∈ (Finset.univ : Finset V), (M.degree v : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ by positivity)
    _ = 2 * (#M.edgeFinset : ℝ) := by
      exact_mod_cast M.sum_degrees_eq_twice_card_edges

/-- Under `16 eta < epsilon²`, the high-defect exceptional set has size
less than `(epsilon/2) n`. -/
lemma card_exceptionalVertices_lt_half
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (hp : 0 < p)
    (c : V → Fin p) {eta epsilon : ℝ}
    (hn : 0 < Fintype.card V) (hepsilon : 0 < epsilon)
    (heta : 16 * eta < epsilon ^ 2)
    (hmono : (#(monochromaticEdges G c) : ℝ) ≤
      eta * (Fintype.card V : ℝ) ^ 2)
    (htotal : (((p : ℝ) - 1) / (2 * p) - eta) *
        (Fintype.card V : ℝ) ^ 2 ≤ (#G.edgeFinset : ℝ)) :
    (#(exceptionalVertices G c epsilon) : ℝ) <
      epsilon / 2 * (Fintype.card V : ℝ) := by
  have hmarkov := card_exceptionalVertices_mul_le G c hepsilon.le
  have hmissing := card_crossNonedgeGraph_le G hp c hmono htotal
  have hsum : (#(exceptionalVertices G c epsilon) : ℝ) *
      (epsilon * (Fintype.card V : ℝ)) ≤
        4 * eta * (Fintype.card V : ℝ) ^ 2 := by
    nlinarith
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  by_contra hnot
  have hcard : epsilon / 2 * (Fintype.card V : ℝ) ≤
      (#(exceptionalVertices G c epsilon) : ℝ) := le_of_not_gt hnot
  have hprod : (epsilon / 2 * (Fintype.card V : ℝ)) *
      (epsilon * (Fintype.card V : ℝ)) ≤
      (#(exceptionalVertices G c epsilon) : ℝ) *
        (epsilon * (Fintype.card V : ℝ)) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  have hetaN : 16 * eta * (Fintype.card V : ℝ) ^ 2 <
      epsilon ^ 2 * (Fintype.card V : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right heta (sq_pos_of_pos hnR)
  nlinarith

/-- Removing fewer than `(epsilon/2)n` vertices preserves the balance
obtained for a full fiber, with final error `epsilon*n`. -/
lemma abs_card_retainedFiber_sub_average_lt
    {p : ℕ} (c : V → Fin p) (S0 : Finset V) {epsilon : ℝ}
    (hS0 : (#S0 : ℝ) < epsilon / 2 * (Fintype.card V : ℝ))
    (hfull : ∀ i : Fin p,
      |(#(colorFiber c i) : ℝ) - (Fintype.card V : ℝ) / p| <
        epsilon / 2 * (Fintype.card V : ℝ))
    (i : Fin p) :
    |(#(retainedFiber c S0 i) : ℝ) - (Fintype.card V : ℝ) / p| <
      epsilon * (Fintype.card V : ℝ) := by
  classical
  have hsub : retainedFiber c S0 i ⊆ colorFiber c i := by
    exact Finset.sdiff_subset
  have hleNat : #(retainedFiber c S0 i) ≤ #(colorFiber c i) :=
    Finset.card_le_card hsub
  have hinter : #((colorFiber c i) ∩ S0) ≤ #S0 :=
    Finset.card_le_card (Finset.inter_subset_right : colorFiber c i ∩ S0 ⊆ S0)
  have hsplit := Finset.card_sdiff_add_card_inter (colorFiber c i) S0
  have hgapNat : #(colorFiber c i) ≤ #(retainedFiber c S0 i) + #S0 := by
    unfold retainedFiber
    omega
  have hle : (#(retainedFiber c S0 i) : ℝ) ≤ #(colorFiber c i) := by
    exact_mod_cast hleNat
  have hgap : (#(colorFiber c i) : ℝ) ≤
      #(retainedFiber c S0 i) + #S0 := by exact_mod_cast hgapNat
  rw [abs_lt]
  have hf := (abs_lt.mp (hfull i))
  constructor <;> nlinarith [hfull i]

/-- Every nonexceptional vertex has fewer than `epsilon*n` missing cross
neighbors even before, hence also after, deleting `S0`. -/
lemma card_retainedCrossNonneighbors_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (c : V → Fin p)
    {epsilon : ℝ} {S0 : Finset V} {v : V}
    (hS0 : exceptionalVertices G c epsilon ⊆ S0) (hv : v ∉ S0) :
    (#(retainedCrossNonneighbors G c S0 v) : ℝ) <
      epsilon * (Fintype.card V : ℝ) := by
  classical
  have hvnot : v ∉ exceptionalVertices G c epsilon := fun hvbad ↦ hv (hS0 hvbad)
  have hdeg : ((crossNonedgeGraph G c).degree v : ℝ) <
      epsilon * (Fintype.card V : ℝ) := by
    simpa only [mem_exceptionalVertices, not_le] using hvnot
  have hcardNat : #(retainedCrossNonneighbors G c S0 v) ≤
      (crossNonedgeGraph G c).degree v := by
    rw [← card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro w hw
    exact (Finset.mem_sdiff.mp (by simpa [retainedCrossNonneighbors] using hw)).1
  exact (by exact_mod_cast hcardNat :
    (#(retainedCrossNonneighbors G c S0 v) : ℝ) ≤
      (crossNonedgeGraph G c).degree v) |>.trans_lt hdeg

/-- The full bookkeeping conclusion needed before the geometric carrier
upgrade: a small exceptional set, balanced retained fibers, and few missing
cross adjacencies at every retained vertex. -/
theorem exists_exceptional_partition
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (hp : 0 < p)
    (c : V → Fin p) {eta epsilon : ℝ}
    (hn : 0 < Fintype.card V) (hepsilon : 0 < epsilon)
    (heta : 16 * eta < epsilon ^ 2)
    (hmono : (#(monochromaticEdges G c) : ℝ) ≤
      eta * (Fintype.card V : ℝ) ^ 2)
    (htotal : (((p : ℝ) - 1) / (2 * p) - eta) *
        (Fintype.card V : ℝ) ^ 2 ≤ (#G.edgeFinset : ℝ)) :
    ∃ S0 : Finset V,
      (#S0 : ℝ) < epsilon * (Fintype.card V : ℝ) ∧
      (∀ i : Fin p,
        |(#(retainedFiber c S0 i) : ℝ) - (Fintype.card V : ℝ) / p| <
          epsilon * (Fintype.card V : ℝ)) ∧
      (∀ (i : Fin p) (v : V), v ∈ retainedFiber c S0 i →
        (#(retainedCrossNonneighbors G c S0 v) : ℝ) <
          epsilon * (Fintype.card V : ℝ)) := by
  let S0 := exceptionalVertices G c epsilon
  have hS0half := card_exceptionalVertices_lt_half
    G hp c hn hepsilon heta hmono htotal
  have hfull : ∀ i : Fin p,
      |(#(colorFiber c i) : ℝ) - (Fintype.card V : ℝ) / p| <
        epsilon / 2 * (Fintype.card V : ℝ) :=
    abs_card_colorFiber_sub_average_lt
      G hp c hn hepsilon heta hmono htotal
  refine ⟨S0, ?_, ?_, ?_⟩
  · have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    nlinarith
  · exact fun i ↦ abs_card_retainedFiber_sub_average_lt c S0 hS0half hfull i
  · intro i v hv
    exact card_retainedCrossNonneighbors_lt G c (S0 := S0) (by simp [S0])
      (mem_retainedFiber c S0 i v |>.1 hv).2

/-- The quantitative partition supplied by Erdős--Simonovits stability,
packaged in the form used by the geometric carrier argument. -/
structure StablePartition (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℕ) (epsilon : ℝ) where
  color : V → Fin p
  exceptional : Finset V
  exceptional_small :
    (#exceptional : ℝ) < epsilon * (Fintype.card V : ℝ)
  balanced : ∀ i : Fin p,
    |(#(retainedFiber color exceptional i) : ℝ) -
        (Fintype.card V : ℝ) / p| < epsilon * (Fintype.card V : ℝ)
  crossNonneighbors_small : ∀ (i : Fin p) (v : V),
    v ∈ retainedFiber color exceptional i →
      (#(retainedCrossNonneighbors G color exceptional v) : ℝ) <
        epsilon * (Fintype.card V : ℝ)

/-- Package the preceding bookkeeping theorem as a `StablePartition`. -/
theorem stablePartition_of_coloring
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (hp : 0 < p)
    (c : V → Fin p) {eta epsilon : ℝ}
    (hn : 0 < Fintype.card V) (hepsilon : 0 < epsilon)
    (heta : 16 * eta < epsilon ^ 2)
    (hmono : (#(monochromaticEdges G c) : ℝ) ≤
      eta * (Fintype.card V : ℝ) ^ 2)
    (htotal : (((p : ℝ) - 1) / (2 * p) - eta) *
        (Fintype.card V : ℝ) ^ 2 ≤ (#G.edgeFinset : ℝ)) :
    Nonempty (StablePartition G p epsilon) := by
  obtain ⟨S0, hS0, hbalanced, hcross⟩ :=
    exists_exceptional_partition G hp c hn hepsilon heta hmono htotal
  exact ⟨⟨c, S0, hS0, hbalanced, hcross⟩⟩

end Stability
end Erdos223
open Finset Fintype
open scoped BigOperators SimpleGraph

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! A local version of the usual ``few atypical vertices'' consequence of
uniformity.  It is deliberately stated for candidate subsets of the original
uniform pair, as required by the greedy embedding argument below. -/

lemma card_lowDegreeVertices_le
    {rho : ℝ} {C D S T : Finset V}
    (hunif : G.IsUniform rho C D)
    (hSC : S ⊆ C) (hTD : T ⊆ D)
    (_hS : rho * #C ≤ #S) (hT : rho * #D ≤ #T) :
    (({x ∈ S | (#({y ∈ T | G.Adj x y}) : ℝ) <
        (G.edgeDensity C D - rho) * #T} : Finset V).card : ℝ) ≤ rho * #C := by
  classical
  let B : Finset V := {x ∈ S | (#({y ∈ T | G.Adj x y}) : ℝ) <
    (G.edgeDensity C D - rho) * #T}
  change (#B : ℝ) ≤ rho * #C
  by_contra! hB
  have hBlarge : (#C : ℝ) * rho ≤ #B := by
    rw [mul_comm]
    exact hB.le
  have hBsub : B ⊆ C := (filter_subset _ _).trans hSC
  have hTlarge : (#D : ℝ) * rho ≤ #T := by simpa [mul_comm] using hT
  have hunifBT : |(G.edgeDensity B T : ℝ) - G.edgeDensity C D| < rho :=
    hunif hBsub hTD hBlarge hTlarge
  have hBne : B.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hB
    have hrho : 0 < rho := hunif.pos
    have hC0 : 0 ≤ (#C : ℝ) := by positivity
    norm_num at hB
    nlinarith [mul_nonneg hrho.le hC0]
  have hbound_pos : 0 < (G.edgeDensity C D - rho) * (#T : ℝ) := by
    obtain ⟨x, hxB⟩ := hBne
    have hx := (mem_filter.1 hxB).2
    exact (Nat.cast_nonneg _).trans_lt hx
  have hTpos : 0 < (#T : ℝ) := by
    by_contra h
    have : (#T : ℝ) = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    rw [this, mul_zero] at hbound_pos
    exact lt_irrefl 0 hbound_pos
  have hthreshold : 0 ≤ (G.edgeDensity C D : ℝ) - rho :=
    nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hbound_pos.le) hTpos
  have hinteredges :
      (#(Rel.interedges G.Adj B T) : ℝ) ≤
        (#B : ℝ) * #T * (G.edgeDensity C D - rho) := by
    refine (Nat.cast_le.2 <| (card_le_card <| subset_of_eq
      (Rel.interedges_eq_biUnion _)).trans card_biUnion_le).trans ?_
    simp_rw [Nat.cast_sum, card_map, ← nsmul_eq_mul, smul_mul_assoc,
      mul_comm (#T : ℝ)]
    exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2.le
  have hdensity : (G.edgeDensity B T : ℝ) ≤ G.edgeDensity C D - rho := by
    rw [edgeDensity_def]
    push_cast
    refine div_le_of_le_mul₀ (by positivity) hthreshold ?_
    rw [mul_comm]
    exact hinteredges
  rw [abs_sub_lt_iff] at hunifBT
  linarith

/-! We enumerate the vertices of `K_r(3)` by the natural numbers
`0,...,3*r-1`.  The quotient by three is their part. -/

private def greedyPart (r : ℕ) (a : Fin (3 * r)) : Fin r :=
  ⟨a.1 / 3, (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).2 (by
    simpa [mul_comm] using a.2)⟩

private def greedyCandidates {r k : ℕ} (hk : k ≤ 3 * r)
    (C : Fin r → Finset V) (f : Fin k → V) (j : Fin r) : Finset V :=
  (C j).filter fun y ↦ ∀ a : Fin k,
    (greedyPart r ⟨a, lt_of_lt_of_le a.2 hk⟩ : Fin r).1 < j.1 → G.Adj (f a) y

private lemma greedyCandidates_subset {r k : ℕ} {hk : k ≤ 3 * r}
    {C : Fin r → Finset V} {f : Fin k → V} {j : Fin r} :
    G.greedyCandidates hk C f j ⊆ C j :=
  filter_subset _ _

private lemma pow_mono_down {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    {k n : ℕ} (hkn : k ≤ n) : alpha ^ n ≤ alpha ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [pow_add]
  have hd : alpha ^ d ≤ 1 := pow_le_one₀ ha0 ha1
  have hk0 : 0 ≤ alpha ^ k := by positivity
  nlinarith

private lemma card_greedyCandidates_start {r : ℕ} (C : Fin r → Finset V) (j : Fin r) :
    G.greedyCandidates (Nat.zero_le _) C (fun a : Fin 0 ↦ nomatch a) j = C j := by
  ext x
  simp [greedyCandidates]

private lemma greedyCandidates_snoc {r k : ℕ} (hk : k ≤ 3 * r)
    (hks : k + 1 ≤ 3 * r) (C : Fin r → Finset V) (f : Fin k → V) (x : V)
    (j : Fin r) :
    G.greedyCandidates hks C (Fin.snoc f x) j =
      if (greedyPart r ⟨k, by omega⟩).1 < j.1 then
        (G.greedyCandidates hk C f j).filter (G.Adj x)
      else G.greedyCandidates hk C f j := by
  classical
  ext y
  simp only [greedyCandidates, mem_filter]
  by_cases hj : (greedyPart r ⟨k, by omega⟩).1 < j.1
  · rw [if_pos hj]
    simp only [mem_filter]
    constructor
    · rintro ⟨hy, hall⟩
      refine ⟨⟨hy, ?_⟩, ?_⟩
      · intro a ha
        simpa only [Fin.snoc_castSucc] using hall a.castSucc ha
      · simpa only [Fin.snoc_last] using hall (Fin.last k) hj
    · rintro ⟨⟨hy, hall⟩, hx⟩
      refine ⟨hy, fun a ↦ Fin.lastCases ?_ (fun b ↦ ?_) a⟩
      · intro _
        simpa only [Fin.snoc_last] using hx
      · intro hb
        simpa only [Fin.snoc_castSucc] using hall b hb
  · rw [if_neg hj]
    simp only [mem_filter]
    constructor
    · rintro ⟨hy, hall⟩
      refine ⟨hy, fun a ha ↦ ?_⟩
      simpa only [Fin.snoc_castSucc] using hall a.castSucc ha
    · rintro ⟨hy, hall⟩
      refine ⟨hy, fun a ↦ Fin.lastCases ?_ (fun b ↦ ?_) a⟩
      · intro ha
        exact (hj ha).elim
      · intro hb
        simpa only [Fin.snoc_castSucc] using hall b hb

/-! The induction invariant used by the greedy construction. -/

private def GreedyState (r k : ℕ) (alpha : ℝ)
    (C : Fin r → Finset V) (hk : k ≤ 3 * r) : Prop :=
  ∃ f : Fin k ↪ V,
    (∀ (a : Fin k), f a ∈ C (greedyPart r ⟨a, lt_of_lt_of_le a.2 hk⟩)) ∧
    (∀ (a b : Fin k), greedyPart r ⟨a, lt_of_lt_of_le a.2 hk⟩ ≠
        greedyPart r ⟨b, lt_of_lt_of_le b.2 hk⟩ →
      G.Adj (f a) (f b)) ∧
    ∀ (j : Fin r),
      k / 3 ≤ j.1 →
      alpha ^ k * #(C j) ≤ #(G.greedyCandidates hk C f j)

private lemma greedyState_zero (r : ℕ) (alpha : ℝ) (C : Fin r → Finset V) :
    G.GreedyState r 0 alpha C (Nat.zero_le _) := by
  let f : Fin 0 ↪ V := ⟨Fin.elim0, fun a _ ↦ Fin.elim0 a⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a
    exact Fin.elim0 a
  · intro a
    exact Fin.elim0 a
  · intro j _
    simpa [f, greedyCandidates]

private lemma greedyState_succ
    {r k : ℕ} {rho delta alpha beta : ℝ} {C : Fin r → Finset V}
    (hk : k ≤ 3 * r) (hks : k + 1 ≤ 3 * r)
    (hstate : G.GreedyState r k alpha C hk)
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 2)
    (halpha : alpha = delta / 2) (hbeta : beta = alpha ^ (3 * r))
    (hrho0 : 0 ≤ rho) (hrho : 2 * rho ≤ delta)
    (hunif : ∀ i j, i ≠ j → G.IsUniform rho (C i) (C j))
    (hdense : ∀ i j, i ≠ j → delta ≤ G.edgeDensity (C i) (C j))
    (hbad : 2 * (r : ℝ) * rho < beta)
    (hsize : ∀ i, 2 * (3 * r : ℕ) < beta * #(C i)) :
    G.GreedyState r (k + 1) alpha C hks := by
  classical
  obtain ⟨f, hfmem, hfadj, hfcard⟩ := hstate
  have hrpos : 0 < r := by omega
  have ha0 : 0 < alpha := by rw [halpha]; linarith
  have ha1 : alpha ≤ 1 := by rw [halpha]; linarith
  have hb0 : 0 < beta := by rw [hbeta]; positivity
  let i : Fin r := greedyPart r ⟨k, by omega⟩
  let S : Finset V := G.greedyCandidates hk C f i
  let J : Finset (Fin r) := univ.filter fun j ↦ i.1 < j.1
  let badAt (j : Fin r) : Finset V :=
    {x ∈ S | (#({y ∈ G.greedyCandidates hk C f j | G.Adj x y}) : ℝ) <
      (G.edgeDensity (C i) (C j) - rho) * #(G.greedyCandidates hk C f j)}
  let B : Finset V := J.biUnion badAt
  let R : Finset V := univ.map f
  have hi : k / 3 = i.1 := rfl
  have hSk : alpha ^ k * #(C i) ≤ #S := by
    exact hfcard i (by rw [← hi])
  have hpow : beta ≤ alpha ^ k := by
    rw [hbeta]
    exact pow_mono_down ha0.le ha1 hk
  have hbadAt (j : Fin r) (hj : j ∈ J) :
      (#(badAt j) : ℝ) ≤ rho * #(C i) := by
    have hij : i ≠ j := by
      intro h
      subst j
      simpa [J] using hj
    have hji : i.1 < j.1 := (mem_filter.1 hj).2
    have hu := hunif i j hij
    have hr0 : 0 < rho := hu.pos
    have hrbeta : rho ≤ beta := by
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
      nlinarith
    have hrak : rho ≤ alpha ^ k := hrbeta.trans hpow
    have hSlarge : rho * #(C i) ≤ #S :=
      (mul_le_mul_of_nonneg_right hrak (by positivity)).trans hSk
    have hjactive : k / 3 ≤ j.1 := by omega
    have hTlarge : rho * #(C j) ≤ #(G.greedyCandidates hk C f j) :=
      (mul_le_mul_of_nonneg_right hrak (by positivity)).trans (hfcard j hjactive)
    exact G.card_lowDegreeVertices_le hu
      (G.greedyCandidates_subset) (G.greedyCandidates_subset) hSlarge hTlarge
  have hBcard : (#B : ℝ) ≤ (r : ℝ) * rho * #(C i) := by
    calc
      (#B : ℝ) ≤ ∑ j ∈ J, (#(badAt j) : ℝ) := by
        exact_mod_cast (card_biUnion_le : #B ≤ ∑ j ∈ J, #(badAt j))
      _ ≤ ∑ _j ∈ J, rho * #(C i) :=
        sum_le_sum fun j hj ↦ hbadAt j hj
      _ = (#J : ℝ) * (rho * #(C i)) := by simp
      _ ≤ (r : ℝ) * rho * #(C i) := by
        have hJ : (#J : ℝ) ≤ r := by
          exact_mod_cast (by simpa using card_le_univ J)
        have hCi : 0 ≤ (#(C i) : ℝ) := by positivity
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_right hJ (mul_nonneg hrho0 hCi))
  have hRcard : #R = k := by simp [R]
  have hCi0 : 0 < (#(C i) : ℝ) := by
    have := hsize i
    have hleft : (0 : ℝ) < 2 * (3 * r : ℕ) := by positivity
    nlinarith
  have hBhalf : (#B : ℝ) < beta * #(C i) / 2 := by
    apply hBcard.trans_lt
    have := hbad
    nlinarith
  have hRhalf : (#R : ℝ) < beta * #(C i) / 2 := by
    rw [hRcard]
    have hk3 : (k : ℝ) ≤ 3 * r := by exact_mod_cast hk
    have hs := hsize i
    norm_num at hs ⊢
    nlinarith
  have hUnion : (#(B ∪ R) : ℝ) < beta * #(C i) := by
    have hc : (#(B ∪ R) : ℝ) ≤ #B + #R := by exact_mod_cast card_union_le B R
    nlinarith
  have hUnionS : (#(B ∪ R) : ℝ) < #S := by
    have hbpow : beta * #(C i) ≤ alpha ^ k * #(C i) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    linarith
  have hnsub : ¬ S ⊆ B ∪ R := by
    intro hsub
    have hc : (#S : ℝ) ≤ #(B ∪ R) := by exact_mod_cast card_le_card hsub
    linarith
  obtain ⟨x, hxS, hxnot⟩ := Finset.not_subset.mp hnsub
  have hxB : x ∉ B := fun hx ↦ hxnot (mem_union_left R hx)
  have hxR : x ∉ R := fun hx ↦ hxnot (mem_union_right B hx)
  have hxrange : x ∉ Set.range f := by
    rintro ⟨a, rfl⟩
    apply hxR
    simp [R]
  let f' : Fin (k + 1) ↪ V :=
    ⟨Fin.snoc f x, Fin.snoc_injective_of_injective f.injective hxrange⟩
  refine ⟨f', ?_, ?_, ?_⟩
  · intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · have hxi : x ∈ C i := G.greedyCandidates_subset hxS
      simpa [f', i] using hxi
    · simpa [f'] using hfmem b
  · intro a b
    refine Fin.lastCases ?_ (fun a' ↦ ?_) a <;>
      refine Fin.lastCases ?_ (fun b' ↦ ?_) b <;> intro hab
    · exact (hab rfl).elim
    ·
      have hle : (greedyPart r ⟨b', by omega⟩).1 ≤ i.1 := by
        dsimp [i, greedyPart]
        exact Nat.div_le_div_right (Nat.le_of_lt b'.2)
      have hne : (greedyPart r ⟨b', by omega⟩).1 ≠ i.1 := by
        intro h
        apply hab
        simpa [i] using Fin.ext h.symm
      have hlt : (greedyPart r ⟨b', by omega⟩).1 < i.1 :=
        lt_of_le_of_ne hle hne
      have hadj := (mem_filter.1 hxS).2 b' hlt
      simpa [f'] using hadj.symm
    ·
      have hle : (greedyPart r ⟨a', by omega⟩).1 ≤ i.1 := by
        dsimp [i, greedyPart]
        exact Nat.div_le_div_right (Nat.le_of_lt a'.2)
      have hne : (greedyPart r ⟨a', by omega⟩).1 ≠ i.1 := by
        intro h
        apply hab
        simpa [i] using Fin.ext h
      have hlt : (greedyPart r ⟨a', by omega⟩).1 < i.1 :=
        lt_of_le_of_ne hle hne
      have hadj := (mem_filter.1 hxS).2 a' hlt
      simpa [f'] using hadj
    · simpa [f'] using hfadj a' b' (by simpa using hab)
  · intro j hjactive
    have hijle : i.1 ≤ j.1 := by
      dsimp [i, greedyPart] at ⊢
      omega
    have hjold : k / 3 ≤ j.1 := by omega
    change alpha ^ (k + 1) * #(C j) ≤
      #(G.greedyCandidates hks C (Fin.snoc f x) j)
    rw [G.greedyCandidates_snoc hk hks C f x j]
    by_cases hij : i.1 < j.1
    · rw [if_pos (by simpa [i] using hij)]
      have hjJ : j ∈ J := by
        exact mem_filter.2 ⟨mem_univ _, hij⟩
      have hxgood :
          (G.edgeDensity (C i) (C j) - rho) * #(G.greedyCandidates hk C f j) ≤
            (#({y ∈ G.greedyCandidates hk C f j | G.Adj x y}) : ℝ) := by
        have hxnotbad : x ∉ badAt j := by
          intro hx
          exact hxB (mem_biUnion.2 ⟨j, hjJ, hx⟩)
        simpa [badAt, hxS, not_lt] using hxnotbad
      have hijne : i ≠ j := by omega
      have hcoef : alpha ≤ (G.edgeDensity (C i) (C j) : ℝ) - rho := by
        have := hdense i j hijne
        rw [halpha]
        linarith
      have hold := hfcard j hjold
      have hT0 : 0 ≤ (#(G.greedyCandidates hk C f j) : ℝ) := by positivity
      have hstep : alpha * #(G.greedyCandidates hk C f j) ≤
          (#({y ∈ G.greedyCandidates hk C f j | G.Adj x y}) : ℝ) :=
        (mul_le_mul_of_nonneg_right hcoef hT0).trans hxgood
      rw [pow_succ]
      nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr hold)]
    · rw [if_neg (by simpa [i] using hij)]
      have hold := hfcard j hjold
      rw [pow_succ]
      have hp : alpha * alpha ^ k ≤ alpha ^ k := by
        nlinarith [pow_nonneg ha0.le k]
      simpa [mul_comm alpha (alpha ^ k)] using
        ((mul_le_mul_of_nonneg_right hp (by positivity)).trans hold)

private def greedySlot (r : ℕ) : Fin r × Fin 3 ↪ Fin (3 * r) where
  toFun p := ⟨p.2.1 + 3 * p.1.1, by omega⟩
  inj' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have hv : b.1 + 3 * a.1 = d.1 + 3 * c.1 := congrArg Fin.val h
    have ha : a.1 = c.1 := by omega
    have hb : b.1 = d.1 := by omega
    exact Prod.ext (Fin.ext ha) (Fin.ext hb)

private lemma greedyPart_greedySlot {r : ℕ} (a : Fin r) (b : Fin 3) :
    greedyPart r (greedySlot r (a, b)) = a := by
  apply Fin.ext
  change (b.1 + 3 * a.1) / 3 = a.1
  omega

/-- Greedy embedding lemma for dense uniform pairs.  The deliberately strong
numerical hypotheses make every one of the `3*r` greedy choices possible. -/
theorem completeEquipartiteGraph_three_isContained_of_uniform
    {r : ℕ} {rho delta : ℝ} (C : Fin r → Finset V)
    (_hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 2)
    (hrho0 : 0 ≤ rho) (hrho : 2 * rho ≤ delta)
    (hunif : ∀ i j, i ≠ j → G.IsUniform rho (C i) (C j))
    (hdense : ∀ i j, i ≠ j → delta ≤ G.edgeDensity (C i) (C j))
    (hbad : 2 * (r : ℝ) * rho < (delta / 2) ^ (3 * r))
    (hsize : ∀ i, 2 * (3 * r : ℕ) < (delta / 2) ^ (3 * r) * #(C i)) :
    completeEquipartiteGraph r 3 ⊑ G := by
  let alpha : ℝ := delta / 2
  let beta : ℝ := alpha ^ (3 * r)
  have states : ∀ (k : ℕ) (hk : k ≤ 3 * r), G.GreedyState r k alpha C hk := by
    intro k
    induction k with
    | zero =>
        intro _
        exact G.greedyState_zero r alpha C
    | succ k ih =>
        intro hks
        have hk : k ≤ 3 * r := Nat.le_trans (Nat.le_succ k) hks
        exact G.greedyState_succ hk hks (ih hk) hdelta hdelta2 rfl rfl hrho0 hrho
          hunif hdense (by simpa [alpha, beta] using hbad)
          (by simpa [alpha, beta] using hsize)
  obtain ⟨f, _hfmem, hfadj, _hfcard⟩ := states (3 * r) le_rfl
  let e : Fin r × Fin 3 ↪ V :=
    ⟨fun p ↦ f (greedySlot r p), f.injective.comp (greedySlot r).injective⟩
  let hom : completeEquipartiteGraph r 3 →g G :=
    ⟨e, fun {p q} hpq ↦ by
      apply hfadj (greedySlot r p) (greedySlot r q)
      intro hparts
      apply (completeEquipartiteGraph_adj.mp hpq)
      apply Fin.ext
      have hv := congrArg Fin.val hparts
      change (p.2.1 + 3 * p.1.1) / 3 = (q.2.1 + 3 * q.1.1) / 3 at hv
      omega⟩
  exact ⟨⟨hom, e.injective⟩⟩

/-- Equal-cardinality version, convenient for applications to equitable
regularity partitions. -/
theorem completeEquipartiteGraph_three_isContained_of_uniform_equipartition
    {r m : ℕ} {rho delta : ℝ} (C : Fin r → Finset V)
    (hcard : ∀ i, #(C i) = m)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 2)
    (hrho0 : 0 ≤ rho) (hrho : 2 * rho ≤ delta)
    (hunif : ∀ i j, i ≠ j → G.IsUniform rho (C i) (C j))
    (hdense : ∀ i j, i ≠ j → delta ≤ G.edgeDensity (C i) (C j))
    (hbad : 2 * (r : ℝ) * rho < (delta / 2) ^ (3 * r))
    (hsize : 2 * (3 * r : ℕ) < (delta / 2) ^ (3 * r) * m) :
    completeEquipartiteGraph r 3 ⊑ G := by
  apply G.completeEquipartiteGraph_three_isContained_of_uniform C hdisj hdelta hdelta2
    hrho0 hrho hunif hdense hbad
  intro i
  simpa [hcard i] using hsize

end SimpleGraph
open Filter Finset Fintype SimpleGraph
open scoped SimpleGraph BigOperators

namespace Erdos223.Stability

/-- Unconditional Erdős--Simonovits stability for the forbidden graph used
in Erdős 223. -/
theorem eventually_exists_partition_completeEquipartite_free
    (p : ℕ) (hp : 2 ≤ p) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ n in atTop, ∀ (V : Type*) [Fintype V], Fintype.card V = n →
        ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
          (completeEquipartiteGraph (p + 1) 3).Free G →
          ((((p : ℝ) - 1) / (2 * p) - delta) * (n : ℝ) ^ 2 ≤
            (#G.edgeFinset : ℝ)) →
          ∃ c : V → Fin p,
            (#(monochromaticEdges G c) : ℝ) ≤ epsilon * (n : ℝ) ^ 2 := by
  classical
  let zeta : ℝ := min epsilon 1
  let d : ℝ := zeta / 32
  let r : ℕ := p + 1
  let beta : ℝ := (d / 2) ^ (3 * r)
  let rho : ℝ := min (d / 2) (beta / (4 * r))
  let xi : ℝ := zeta / 8
  let M : ℕ := ⌈((2 * (3 * r) : ℕ) + 1 : ℝ) / beta⌉₊
  let l : ℕ := ⌈4 / xi⌉₊
  let N : ℕ := max 1 (max l (M * SzemerediRegularity.bound rho l))
  have hzeta0 : 0 < zeta := by simp [zeta, hepsilon]
  have hzetale : zeta ≤ epsilon := min_le_left _ _
  have hzetale1 : zeta ≤ 1 := min_le_right _ _
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hd2 : d ≤ 2 := by dsimp [d]; linarith
  have hr0 : 0 < r := by dsimp [r]; omega
  have hbeta0 : 0 < beta := by dsimp [beta]; positivity
  have hrho0 : 0 < rho := by
    dsimp [rho]
    exact lt_min (by positivity) (div_pos hbeta0 (by positivity))
  have hrho_d : 2 * rho ≤ d := by
    have h := min_le_left (d / 2) (beta / (4 * (r : ℝ)))
    change rho ≤ d / 2 at h
    linarith
  have hbad : 2 * (r : ℝ) * rho < beta := by
    have h4r : (0 : ℝ) < 4 * r := by positivity
    have h := min_le_right (d / 2) (beta / (4 * (r : ℝ)))
    change rho ≤ beta / (4 * (r : ℝ)) at h
    have hmul := (le_div_iff₀ h4r).mp h
    nlinarith
  have hlossCoeff : 2 * rho + xi / 4 + 2 * d ≤ zeta / 8 := by
    have hrho_d' := hrho_d
    dsimp [d] at hrho_d'
    dsimp [xi, d]
    nlinarith
  refine ⟨zeta / 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  intro V instV hcard G instAdj hfree hnear
  have hn1 : 1 ≤ n := (le_max_left 1 (max l (M * SzemerediRegularity.bound rho l))).trans hn
  have hnpos : 0 < n := by omega
  have hVpos : 0 < Fintype.card V := by simpa [hcard] using hnpos
  letI : Nonempty V := Fintype.card_pos_iff.mp hVpos
  have hl : l ≤ Fintype.card V := by
    rw [hcard]
    exact (le_max_of_le_right (le_max_left l (M * SzemerediRegularity.bound rho l))).trans hn
  have hlarge : M * SzemerediRegularity.bound rho l ≤ Fintype.card V := by
    rw [hcard]
    exact (le_max_of_le_right (le_max_right l (M * SzemerediRegularity.bound rho l))).trans hn
  have hMsize : 2 * ((3 * r : ℕ) : ℝ) < beta * M := by
    have hceil : (((2 * (3 * r) : ℕ) + 1 : ℝ) / beta) ≤ (M : ℝ) := by
      exact Nat.le_ceil _
    calc
      2 * ((3 * r : ℕ) : ℝ) < ((2 * (3 * r) : ℕ) : ℝ) + 1 := by norm_num
      _ = beta * (((2 * (3 * r) : ℕ) + 1 : ℝ) / beta) := by field_simp
      _ ≤ beta * M := by gcongr
  have hembed : ∀ (P : Finpartition (univ : Finset V)),
      P.IsEquipartition → P.IsUniform G rho →
      ∀ s, (G.regularityReduced P rho d).IsNClique r s →
        (∀ x ∈ s, M ≤ #(P.part x)) →
        completeEquipartiteGraph r 3 ⊑ G := by
    intro P hPeq hPreg s hs hparts
    let C : Fin r → Finset V := reducedCliqueParts hs
    apply G.completeEquipartiteGraph_three_isContained_of_uniform C
    · exact fun i j hij ↦ reducedCliqueParts_disjoint hs hij
    · exact hd0
    · exact hd2
    · exact hrho0.le
    · exact hrho_d
    · exact fun i j hij ↦ (reducedCliqueParts_uniform_dense hs hij).1
    · exact fun i j hij ↦ (reducedCliqueParts_uniform_dense hs hij).2
    · simpa [beta] using hbad
    · intro i
      let e := (Finset.equivFinOfCardEq hs.card_eq).symm
      have hMi : M ≤ #(P.part (e i).1) := hparts (e i).1 (e i).2
      have hMiR : (M : ℝ) ≤ #(C i) := by
        exact_mod_cast (by simpa [C, reducedCliqueParts, e] using hMi)
      calc
        2 * ((3 * r : ℕ) : ℝ) < beta * M := hMsize
        _ ≤ beta * #(C i) := by gcongr
        _ = (d / 2) ^ (3 * r) * #(C i) := by rfl
  obtain ⟨P, _hPeq, _hPreg, hclique, hHG, hloss⟩ :=
    exists_cliqueFree_regularityReduced_of_large_clusters
      (G := G) (r := r) (M := M) (ρ := rho) (d := d) (ξ := xi)
      hrho0 hd0.le (show 0 < xi by dsimp [xi]; positivity) (by simpa [l] using hl)
      (by simpa [l] using hlarge) (by simpa [r] using hfree) hembed
  let H : SimpleGraph V := G.regularityReduced P rho d
  obtain ⟨c, hmajor⟩ := cliqueFree_majorization p (by omega) H (by simpa [H, r] using hclique)
  let J : SimpleGraph V := partiteCore H c
  have hJle : J ≤ G := (partiteCore_le H c).trans hHG
  have hJcolor : J.Colorable p := partiteCore_colorable H c
  have hcount := card_edgeFinset_eq_card_partiteCore_add_card_monochromatic (G := H) c
  have hcountR : (#H.edgeFinset : ℝ) = #J.edgeFinset + #(monochromaticEdges H c) := by
    exact_mod_cast hcount
  have hloss' : (#G.edgeFinset - #H.edgeFinset : ℝ) <
      zeta / 8 * (n : ℝ) ^ 2 := by
    have hsquare : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := sq_nonneg _
    have := lt_of_lt_of_le hloss (mul_le_mul_of_nonneg_right hlossCoeff hsquare)
    simpa [H, hcard] using this
  have hdelete : (#G.edgeFinset : ℝ) ≤ #J.edgeFinset + epsilon * (n : ℝ) ^ 2 := by
    have hsquare : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have hzetanonneg : 0 ≤ zeta := hzeta0.le
    rw [hcard] at hmajor
    nlinarith
  obtain ⟨cG, hcG⟩ := exists_partition_of_colorable_subgraph_real hJle hJcolor hdelete
  exact ⟨cG, by simpa [hcard] using hcG⟩

end Erdos223.Stability
open Filter Finset Fintype SimpleGraph
open scoped SimpleGraph BigOperators

namespace Erdos223.Stability

/-- Swanepoel's strong graph-stability output: almost balanced classes,
a small exceptional set, and few retained cross nonneighbors at every
nonexceptional vertex. -/
theorem eventually_exists_stablePartition_completeEquipartite_free
    (p : ℕ) (hp : 2 ≤ p) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ n in atTop, ∀ (V : Type*) [Fintype V], Fintype.card V = n →
        ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
          (completeEquipartiteGraph (p + 1) 3).Free G →
          ((((p : ℝ) - 1) / (2 * p) - delta) * (n : ℝ) ^ 2 ≤
            (#G.edgeFinset : ℝ)) →
          Nonempty (StablePartition G p epsilon) := by
  let zeta : ℝ := min epsilon 1
  let eta : ℝ := zeta ^ 2 / 32
  have hzeta0 : 0 < zeta := by simp [zeta, hepsilon]
  have hzetale : zeta ≤ epsilon := min_le_left _ _
  have heta0 : 0 < eta := by dsimp [eta]; positivity
  have hetaSmall : 16 * eta < epsilon ^ 2 := by
    have hsq : zeta ^ 2 ≤ epsilon ^ 2 :=
      (sq_le_sq₀ hzeta0.le hepsilon.le).2 hzetale
    dsimp [eta]
    nlinarith
  obtain ⟨delta0, hdelta0, hmono⟩ :=
    eventually_exists_partition_completeEquipartite_free p hp heta0
  refine ⟨min delta0 eta, lt_min hdelta0 heta0, ?_⟩
  filter_upwards [hmono, eventually_ge_atTop 1] with n hnmono hn
  intro V instV hcard G instAdj hfree hnear
  have hnear0 : (((p : ℝ) - 1) / (2 * p) - delta0) * (n : ℝ) ^ 2 ≤
      (#G.edgeFinset : ℝ) := by
    have hmin : min delta0 eta ≤ delta0 := min_le_left _ _
    nlinarith [sq_nonneg (n : ℝ)]
  obtain ⟨c, hc⟩ := hnmono V hcard G hfree hnear0
  have hnearEta : (((p : ℝ) - 1) / (2 * p) - eta) *
      (Fintype.card V : ℝ) ^ 2 ≤ (#G.edgeFinset : ℝ) := by
    have hmin : min delta0 eta ≤ eta := min_le_right _ _
    rw [hcard]
    nlinarith [sq_nonneg (n : ℝ)]
  have hnpos : 0 < Fintype.card V := by rw [hcard]; omega
  apply stablePartition_of_coloring G (by omega) c hnpos hepsilon hetaSmall
  · simpa [hcard] using hc
  · exact hnearEta

end Erdos223.Stability
