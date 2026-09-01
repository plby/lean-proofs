/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1078.
https://www.erdosproblems.com/forum/thread/1078

Informal authors:
- Penny Haxell
- Tibor Szabó

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1078.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

/-!
# Erdős Problem 1078

Haxell's independent-transversal theorem implies that a balanced `r`-partite
graph whose minimum degree is at the `r - 3/2 - o(1)` threshold contains a
transversal `K_r`.  The proof below formalizes the edge-minimal domination
certificate and applies it to the multipartite complement.

The accompanying mathematical reconstruction is `tex/1078.tex`.
-/

open Finset
open SimpleGraph

namespace Erdos1078

universe u v

/-- A coloring witnesses a multipartite graph when adjacent vertices always
have distinct colors. -/
def IsPartite {I : Type u} {V : Type v} (G : SimpleGraph V) (color : V → I) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → color x ≠ color y

/-- A choice of one vertex of each color which is independent in `G`. -/
def IsIndependentTransversal {I : Type u} {V : Type v} (G : SimpleGraph V)
    (color : V → I) (f : I → V) : Prop :=
  (∀ i, color (f i) = i) ∧ ∀ i j, i ≠ j → ¬G.Adj (f i) (f j)

/-- Existence of an independent transversal for a colored graph. -/
def HasIndependentTransversal {I : Type u} {V : Type v} (G : SimpleGraph V)
    (color : V → I) : Prop :=
  ∃ f : I → V, IsIndependentTransversal G color f

/-- A partial independent transversal meeting every color except `root`. -/
def IsPartialTransversalExcept {I : Type u} {V : Type v} (G : SimpleGraph V)
    (color : V → I) (root : I) (f : {i : I // i ≠ root} → V) : Prop :=
  (∀ i, color (f i) = i) ∧ ∀ i j, i ≠ j → ¬G.Adj (f i) (f j)

/-- The vertices in `D` totally dominate every vertex whose color lies in `S`. -/
def DominatesColors {I : Type u} {V : Type v} (G : SimpleGraph V)
    (color : V → I) (D : Finset V) (S : Finset I) : Prop :=
  ∀ x, color x ∈ S → ∃ d ∈ D, G.Adj d x

/-- The neighbor set as a finset, with its finite construction fixed once
and for all so subsequent cardinalities do not depend on typeclass choices. -/
noncomputable def neighbors {V : Type v} [Fintype V]
    (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun y ↦ G.Adj x y

@[simp] lemma mem_neighbors {V : Type v} [Fintype V]
    (G : SimpleGraph V) (x y : V) : y ∈ neighbors G x ↔ G.Adj x y := by
  classical
  simp [neighbors]

/-- Degree in a finite graph, defined using the canonical filtered universe. -/
noncomputable def graphDegree {V : Type v} [Fintype V]
    (G : SimpleGraph V) (x : V) : ℕ := (neighbors G x).card

/-- The edge set as a canonically constructed finset. -/
noncomputable def graphEdges {V : Type v} [Fintype V]
    (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e ↦ e ∈ G.edgeSet

@[simp] lemma mem_graphEdges {V : Type v} [Fintype V]
    (G : SimpleGraph V) (e : Sym2 V) : e ∈ graphEdges G ↔ e ∈ G.edgeSet := by
  classical
  simp [graphEdges]

lemma IsIndependentTransversal.mono {I : Type u} {V : Type v}
    {G H : SimpleGraph V} {color : V → I} {f : I → V}
    (hf : IsIndependentTransversal G color f) (hHG : H ≤ G) :
    IsIndependentTransversal H color f := by
  refine ⟨hf.1, ?_⟩
  intro i j hij hadj
  exact hf.2 i j hij (hHG hadj)

lemma IsPartialTransversalExcept.mono {I : Type u} {V : Type v}
    {G H : SimpleGraph V} {color : V → I} {root : I}
    {f : {i : I // i ≠ root} → V}
    (hf : IsPartialTransversalExcept G color root f) (hHG : H ≤ G) :
    IsPartialTransversalExcept H color root f := by
  refine ⟨hf.1, ?_⟩
  intro i j hij hadj
  exact hf.2 i j hij (hHG hadj)

/-- Edge-minimal failure of the independent-transversal property. -/
def EdgeMinimalWithoutTransversal {I : Type u} {V : Type v} (G : SimpleGraph V)
    (color : V → I) : Prop :=
  ¬HasIndependentTransversal G color ∧
    ∀ ⦃x y⦄, G.Adj x y →
      HasIndependentTransversal (G.deleteEdges {s(x, y)}) color

/-- Every finite counterexample has an edge-minimal spanning counterexample. -/
lemma exists_edgeMinimal_le {I : Type u} {V : Type v}
    [Finite V] (G : SimpleGraph V) (color : V → I)
    (hG : ¬HasIndependentTransversal G color) :
    ∃ H : SimpleGraph V, H ≤ G ∧ EdgeMinimalWithoutTransversal H color := by
  classical
  let _ := Fintype.ofFinite V
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H ↦ H ≤ G ∧ ¬HasIndependentTransversal H color
  have hcandidates : candidates.Nonempty := by
    refine ⟨G, ?_⟩
    simp [candidates, hG]
  obtain ⟨H, hHmem, hHmin⟩ :=
    candidates.exists_min_image (fun H ↦ (graphEdges H).card) hcandidates
  have hH : H ≤ G ∧ ¬HasIndependentTransversal H color := by
    simpa [candidates] using hHmem
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro x y hxy
  by_contra hdelete
  have hsub : H.deleteEdges {s(x, y)} ≤ G :=
    (H.deleteEdges_le _).trans hH.1
  have hdelmem : H.deleteEdges {s(x, y)} ∈ candidates := by
    simp only [candidates, mem_filter, mem_univ, true_and]
    exact ⟨hsub, hdelete⟩
  have hcard := hHmin _ hdelmem
  have hedge : s(x, y) ∈ graphEdges H := by simpa using hxy
  have hstrict : (graphEdges (H.deleteEdges {s(x, y)})).card <
      (graphEdges H).card := by
    have heq : graphEdges (H.deleteEdges ({s(x, y)} : Set (Sym2 V))) =
        graphEdges H \ {s(x, y)} := by
      ext e
      simp [graphEdges]
    have hsing : ({s(x, y)} : Finset (Sym2 V)) ⊆ graphEdges H := by
      simpa using hedge
    have hpos : 0 < (graphEdges H).card := card_pos.mpr ⟨s(x, y), hedge⟩
    rw [heq, card_sdiff_of_subset hsing]
    simp only [card_singleton]
    omega
  omega

/-- Extend a transversal missing `root` by the vertex `x`. -/
noncomputable def extendPartial {I : Type u} {V : Type v} [DecidableEq I]
    (root : I) (x : V) (f : {i : I // i ≠ root} → V) : I → V :=
  fun i ↦ if hi : i = root then x else f ⟨i, hi⟩

lemma isIndependentTransversal_extendPartial {I : Type u} {V : Type v}
    [DecidableEq I] {G : SimpleGraph V} {color : V → I} {root : I} {x : V}
    {f : {i : I // i ≠ root} → V}
    (hf : IsPartialTransversalExcept G color root f)
    (hxcolor : color x = root) (hx : ∀ i, ¬G.Adj x (f i)) :
    IsIndependentTransversal G color (extendPartial root x f) := by
  constructor
  · intro i
    by_cases hi : i = root
    · simp [extendPartial, hi, hxcolor]
    · simp [extendPartial, hi, hf.1]
  · intro i j hij
    by_cases hi : i = root
    · subst i
      have hj : j ≠ root := by exact fun h ↦ hij h.symm
      simpa [extendPartial, hj] using hx ⟨j, hj⟩
    · by_cases hj : j = root
      · subst j
        simpa [extendPartial, hi, G.adj_comm] using hx ⟨i, hi⟩
      · simpa [extendPartial, hi, hj] using
          hf.2 ⟨i, hi⟩ ⟨j, hj⟩ (by simpa using hij)

/-- In a graph with no full transversal, a vertex in the missing color must
meet the fixed partial transversal. -/
lemma exists_adj_partial {I : Type u} {V : Type v}
    {G : SimpleGraph V} {color : V → I} {root : I} {x : V}
    {f : {i : I // i ≠ root} → V}
    (hf : IsPartialTransversalExcept G color root f)
    (hxcolor : color x = root) (hno : ¬HasIndependentTransversal G color) :
    ∃ i, G.Adj x (f i) := by
  classical
  by_contra h
  push Not at h
  exact hno ⟨extendPartial root x f,
    isIndependentTransversal_extendPartial hf hxcolor h⟩

/-- A transversal created by deleting one edge from a counterexample has to
contain both endpoints of that edge. -/
lemma deletedEdge_endpoints {I : Type u} {V : Type v}
    {G : SimpleGraph V} {color : V → I} {x y : V}
    (hno : ¬HasIndependentTransversal G color)
    {g : I → V}
    (hg : IsIndependentTransversal (G.deleteEdges {s(x, y)}) color g) :
    g (color x) = x ∧ g (color y) = y := by
  classical
  have hpair : ∃ i j, i ≠ j ∧ G.Adj (g i) (g j) := by
    by_contra h
    apply hno
    refine ⟨g, hg.1, ?_⟩
    intro i j hij hadj
    exact h ⟨i, j, hij, hadj⟩
  obtain ⟨i, j, hij, hadj⟩ := hpair
  have hedge : s(g i, g j) = s(x, y) := by
    by_contra hne
    have hdel : (G.deleteEdges {s(x, y)}).Adj (g i) (g j) := by
      rw [deleteEdges_adj]
      exact ⟨hadj, by simpa using hne⟩
    exact hg.2 i j hij hdel
  rcases Sym2.eq_iff.mp hedge with hdir | hswap
  · have hi' : i = color x := by
      have hc := hg.1 i
      rw [hdir.1] at hc
      exact hc.symm
    have hj' : j = color y := by
      have hc := hg.1 j
      rw [hdir.2] at hc
      exact hc.symm
    simpa [← hi', ← hj'] using hdir
  · have hi' : i = color y := by
      have hc := hg.1 i
      rw [hswap.1] at hc
      exact hc.symm
    have hj' : j = color x := by
      have hc := hg.1 j
      rw [hswap.2] at hc
      exact hc.symm
    constructor
    · simpa [← hj'] using hswap.2
    · simpa [← hi'] using hswap.1

/-- Every other vertex of a transversal in `G - xy` avoids both endpoints
already in `G`. -/
lemma deletedTransversal_avoids_endpoints {I : Type u} {V : Type v}
    {G : SimpleGraph V} {color : V → I} {x y : V}
    (hxy : G.Adj x y) {g : I → V}
    (hg : IsIndependentTransversal (G.deleteEdges {s(x, y)}) color g)
    (hend : g (color x) = x ∧ g (color y) = y)
    {i : I} (hix : i ≠ color x) (hiy : i ≠ color y) :
    ¬G.Adj x (g i) ∧ ¬G.Adj y (g i) := by
  classical
  have hxyne : x ≠ y := hxy.ne
  constructor
  · intro hadj
    have hmem : s(x, g i) ∈ ({s(x, y)} : Set (Sym2 V)) := by
      by_contra hnot
      apply hg.2 (color x) i hix.symm
      rw [deleteEdges_adj]
      simpa [hend.1] using And.intro hadj hnot
    have heq : s(x, g i) = s(x, y) := by simpa using hmem
    rcases Sym2.eq_iff.mp heq with hdir | hswap
    · have : i = color y := by
        have hc := hg.1 i
        rw [hdir.2] at hc
        exact hc.symm
      exact hiy this
    · exact hxyne hswap.1
  · intro hadj
    have hmem : s(y, g i) ∈ ({s(x, y)} : Set (Sym2 V)) := by
      by_contra hnot
      apply hg.2 (color y) i hiy.symm
      rw [deleteEdges_adj]
      simpa [hend.2] using And.intro hadj hnot
    have heq : s(y, g i) = s(x, y) := by simpa using hmem
    rcases Sym2.eq_iff.mp heq with hdir | hswap
    · exact hxyne hdir.1.symm
    · have : i = color x := by
        have hc := hg.1 i
        rw [hswap.2] at hc
        exact hc.symm
      exact hix this

/-- Two selected vertices whose colors are different from both endpoint
colors are already nonadjacent before the edge deletion. -/
lemma deletedTransversal_other_pair {I : Type u} {V : Type v}
    {G : SimpleGraph V} {color : V → I} {x y : V}
    {g : I → V}
    (hg : IsIndependentTransversal (G.deleteEdges {s(x, y)}) color g)
    {i j : I} (hij : i ≠ j)
    (hix : i ≠ color x) (hiy : i ≠ color y) :
    ¬G.Adj (g i) (g j) := by
  classical
  intro hadj
  have hne : s(g i, g j) ≠ s(x, y) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with hdir | hswap
    · have hi : i = color x := by
        have hc := hg.1 i
        rw [hdir.1] at hc
        exact hc.symm
      exact hix hi
    · have hi : i = color y := by
        have hc := hg.1 i
        rw [hswap.1] at hc
        exact hc.symm
      exact hiy hi
  apply hg.2 i j hij
  rw [deleteEdges_adj]
  exact ⟨hadj, by simpa using hne⟩

/-- The color type obtained by merging color `b` into another color. -/
abbrev ReducedColor (I : Type u) (b : I) := {i : I // i ≠ b}

/-- Vertices surviving after the neighborhoods of two adjacent vertices are
removed. -/
abbrev SurvivingVertices {V : Type v} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) :=
  {z : V // z ∉ (neighbors G) x ∪ (neighbors G) y}

/-- Recolor old color `b` as `root`, leaving every other color unchanged. -/
def mergedColor {I : Type u} {V : Type v} [DecidableEq I]
    (color : V → I) (root b : I) (hrootb : root ≠ b) (z : V) : ReducedColor I b :=
  if hz : color z = b then ⟨root, hrootb⟩ else ⟨color z, hz⟩

@[simp] lemma mergedColor_of_eq {I : Type u} {V : Type v} [DecidableEq I]
    (color : V → I) (root b : I) (hrootb : root ≠ b) (z : V)
    (hz : color z = b) :
    mergedColor color root b hrootb z = ⟨root, hrootb⟩ := by
  simp [mergedColor, hz]

@[simp] lemma mergedColor_of_ne {I : Type u} {V : Type v} [DecidableEq I]
    (color : V → I) (root b : I) (hrootb : root ≠ b) (z : V)
    (hz : color z ≠ b) :
    mergedColor color root b hrootb z = ⟨color z, hz⟩ := by
  simp [mergedColor, hz]

lemma color_eq_root_or_eq_of_mergedColor_eq_root
    {I : Type u} {V : Type v} [DecidableEq I]
    (color : V → I) (root b : I) (hrootb : root ≠ b) (z : V)
    (h : mergedColor color root b hrootb z = ⟨root, hrootb⟩) :
    color z = root ∨ color z = b := by
  by_cases hz : color z = b
  · exact Or.inr hz
  · left
    rw [mergedColor_of_ne color root b hrootb z hz] at h
    exact congr_arg Subtype.val h

lemma color_eq_of_mergedColor_eq_of_ne_root
    {I : Type u} {V : Type v} [DecidableEq I]
    (color : V → I) (root b : I) (hrootb : root ≠ b) (z : V)
    (i : ReducedColor I b) (hi : i.1 ≠ root)
    (h : mergedColor color root b hrootb z = i) :
    color z = i.1 := by
  by_cases hz : color z = b
  · rw [mergedColor_of_eq color root b hrootb z hz] at h
    exact False.elim (hi (congr_arg Subtype.val h).symm)
  · rw [mergedColor_of_ne color root b hrootb z hz] at h
    exact congr_arg Subtype.val h

/-- The reduced graph deletes the two endpoint neighborhoods and then removes
all edges which have become internal to the merged color. -/
def reducedGraph {I : Type u} {V : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq I] (G : SimpleGraph V) (color : V → I)
    (root b : I) (hrootb : root ≠ b) (x y : V) :
    SimpleGraph (SurvivingVertices G x y) where
  Adj z w := G.Adj z.1 w.1 ∧
    mergedColor color root b hrootb z.1 ≠ mergedColor color root b hrootb w.1
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := G.loopless.irrefl _ h.1

lemma reducedGraph_isPartite {I : Type u} {V : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (color : V → I) (root b : I)
    (hrootb : root ≠ b) (x y : V) :
    IsPartite (reducedGraph G color root b hrootb x y)
      (fun z ↦ mergedColor color root b hrootb z.1) := by
  intro z w hzw
  exact hzw.2

/-- An independent transversal of the reduced graph lifts by restoring the
appropriate one of the two deleted endpoint colors. -/
lemma hasIndependentTransversal_of_reduced {I : Type u} {V : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (color : V → I) (root b : I)
    (hrootb : root ≠ b) (x y : V)
    (hxcolor : color x = root) (hycolor : color y = b)
    (hred : HasIndependentTransversal
      (reducedGraph G color root b hrootb x y)
      (fun z ↦ mergedColor color root b hrootb z.1)) :
    HasIndependentTransversal G color := by
  classical
  let root' : ReducedColor I b := ⟨root, hrootb⟩
  obtain ⟨q, hq⟩ := hred
  have hqroot := hq.1 root'
  have hrootCases : color (q root').1 = root ∨ color (q root').1 = b :=
    color_eq_root_or_eq_of_mergedColor_eq_root color root b hrootb _ hqroot
  rcases hrootCases with hqoldroot | hqoldb
  · let lift : I → V := fun i ↦ if hi : i = b then y else (q ⟨i, hi⟩).1
    refine ⟨lift, ?_, ?_⟩
    · intro i
      by_cases hi : i = b
      · subst i
        simp [lift, hycolor]
      · by_cases hir : i = root
        · subst i
          have hqeq : q (⟨root, hrootb⟩ : ReducedColor I b) = q root' := rfl
          simp [lift, hrootb, root', hqoldroot, hqeq]
        · have hc := color_eq_of_mergedColor_eq_of_ne_root
            color root b hrootb (q ⟨i, hi⟩).1 ⟨i, hi⟩ hir (hq.1 ⟨i, hi⟩)
          simp [lift, hi, hc]
    · intro i j hij
      by_cases hi : i = b
      · subst i
        have hj : j ≠ b := by exact fun h ↦ hij h.symm
        intro hadj
        have hsurv := (q ⟨j, hj⟩).2
        have : G.Adj y (q ⟨j, hj⟩).1 := by simpa [lift, hj] using hadj
        exact hsurv (by simp [mem_neighbors, this])
      · by_cases hj : j = b
        · subst j
          intro hadj
          have hsurv := (q ⟨i, hi⟩).2
          have : G.Adj y (q ⟨i, hi⟩).1 := by
            simpa [lift, hi, G.adj_comm] using hadj
          exact hsurv (by simp [mem_neighbors, this])
        · intro hadj
          apply hq.2 ⟨i, hi⟩ ⟨j, hj⟩
          · intro heq
            exact hij (congr_arg (fun z : ReducedColor I b ↦ z.1) heq)
          · refine ⟨?_, ?_⟩
            · simpa [lift, hi, hj] using hadj
            · intro heq
              have hcolors : (⟨i, hi⟩ : ReducedColor I b) = ⟨j, hj⟩ :=
                (hq.1 ⟨i, hi⟩).symm.trans (heq.trans (hq.1 ⟨j, hj⟩))
              exact hij (congr_arg Subtype.val hcolors)
  · let phi : {i : I // i ≠ root} → ReducedColor I b := fun i ↦
      if hi : i.1 = b then root' else ⟨i.1, hi⟩
    let lift : I → V := fun i ↦
      if hi : i = root then x else (q (phi ⟨i, hi⟩)).1
    have hphi_color : ∀ i : {i : I // i ≠ root},
        color (q (phi i)).1 = i.1 := by
      intro i
      by_cases hi : i.1 = b
      · have hphi : phi i = root' := by simp [phi, hi]
        rw [hphi]
        exact hqoldb.trans hi.symm
      · have hphine : (phi i).1 ≠ root := by
          simp [phi, hi, i.2]
        have hc := color_eq_of_mergedColor_eq_of_ne_root
          color root b hrootb (q (phi i)).1 (phi i) hphine (hq.1 (phi i))
        exact hc.trans (by simp [phi, hi])
    refine ⟨lift, ?_, ?_⟩
    · intro i
      by_cases hi : i = root
      · subst i
        simp [lift, hxcolor]
      · simp [lift, hi, hphi_color ⟨i, hi⟩]
    · intro i j hij
      by_cases hi : i = root
      · subst i
        have hj : j ≠ root := by exact fun h ↦ hij h.symm
        intro hadj
        have hsurv := (q (phi ⟨j, hj⟩)).2
        have : G.Adj x (q (phi ⟨j, hj⟩)).1 := by
          simpa [lift, hj] using hadj
        exact hsurv (by simp [mem_neighbors, this])
      · by_cases hj : j = root
        · subst j
          intro hadj
          have hsurv := (q (phi ⟨i, hi⟩)).2
          have : G.Adj x (q (phi ⟨i, hi⟩)).1 := by
            simpa [lift, hi, G.adj_comm] using hadj
          exact hsurv (by simp [mem_neighbors, this])
        · have hphine : phi ⟨i, hi⟩ ≠ phi ⟨j, hj⟩ := by
            intro heq
            have hc := congr_arg (fun z ↦ color z.1)
              (congr_arg q heq)
            rw [hphi_color ⟨i, hi⟩, hphi_color ⟨j, hj⟩] at hc
            exact hij hc
          intro hadj
          apply hq.2 (phi ⟨i, hi⟩) (phi ⟨j, hj⟩) hphine
          refine ⟨?_, ?_⟩
          · simpa [lift, hi, hj] using hadj
          · intro heq
            apply hphine
            exact (hq.1 (phi ⟨i, hi⟩)).symm.trans
              (heq.trans (hq.1 (phi ⟨j, hj⟩)))

/-- Rooted form of Haxell's domination certificate.  The supplied partial
transversal meets every color except `root`. -/
theorem rooted_domination_certificate {I : Type u} {V : Type v}
    [Finite I] [Finite V]
    (G : SimpleGraph V) (color : V → I) (root : I)
    (hpart : IsPartite G color) (hroot : ∃ x, color x = root)
    (f : {i : I // i ≠ root} → V)
    (hf : IsPartialTransversalExcept G color root f)
    (hno : ¬HasIndependentTransversal G color) :
    ∃ (S : Finset I) (D : Finset V),
      root ∈ S ∧ D.card ≤ 2 * (S.card - 1) ∧ DominatesColors G color D S := by
  classical
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite V
  obtain ⟨F, hFG, hFmin⟩ := exists_edgeMinimal_le G color hno
  have hFpart : IsPartite F color := fun _ _ h ↦ hpart (hFG h)
  have hfF : IsPartialTransversalExcept F color root f := hf.mono hFG
  obtain ⟨x, hxcolor⟩ := hroot
  obtain ⟨j, hxj⟩ := exists_adj_partial hfF hxcolor hFmin.1
  let y : V := f j
  have hycolor : color y = j.1 := hfF.1 j
  have hrootb : root ≠ color y := by
    rw [hycolor]
    exact j.2.symm
  have hxy : F.Adj x y := by simpa [y] using hxj
  obtain ⟨g, hg⟩ := hFmin.2 hxy
  have hend := deletedEdge_endpoints hFmin.1 hg
  have hend' : g root = x ∧ g (color y) = y := by
    simpa [hxcolor] using hend
  let root' : ReducedColor I (color y) := ⟨root, hrootb⟩
  let c' : SurvivingVertices F x y → ReducedColor I (color y) :=
    fun z ↦ mergedColor color root (color y) hrootb z.1
  let K : SimpleGraph (SurvivingVertices F x y) :=
    reducedGraph F color root (color y) hrootb x y
  by_cases hY : ∃ z : SurvivingVertices F x y, c' z = root'
  · let f' : {i : ReducedColor I (color y) // i ≠ root'} →
        SurvivingVertices F x y := fun i ↦ by
        have hiroot : i.1.1 ≠ root := by
          intro hi
          apply i.2
          apply Subtype.ext
          simpa [root'] using hi
        have hix : i.1.1 ≠ color x := by simpa [hxcolor] using hiroot
        have hiy : i.1.1 ≠ color y := i.1.2
        have hav := deletedTransversal_avoids_endpoints hxy hg hend
          hix hiy
        exact ⟨g i.1.1, by
          simp only [mem_union, mem_neighbors]
          exact not_or_intro hav.1 hav.2⟩
    have hf' : IsPartialTransversalExcept K c' root' f' := by
      constructor
      · intro i
        apply Subtype.ext
        have hc := hg.1 i.1.1
        simp [c', f', mergedColor, hc, i.1.2]
      · intro i k hik
        have hiroot : i.1.1 ≠ root := by
          intro hi
          apply i.2
          apply Subtype.ext
          simpa [root'] using hi
        have hkroot : k.1.1 ≠ root := by
          intro hk
          apply k.2
          apply Subtype.ext
          simpa [root'] using hk
        have hikold : i.1.1 ≠ k.1.1 := by
          intro heq
          apply hik
          apply Subtype.ext
          apply Subtype.ext
          exact heq
        intro hadj
        exact deletedTransversal_other_pair hg hikold
          (by simpa [hxcolor] using hiroot) i.1.2 hadj.1
    have hKpart : IsPartite K c' := by
      exact reducedGraph_isPartite F color root (color y) hrootb x y
    have hKno : ¬HasIndependentTransversal K c' := by
      intro hK
      exact hFmin.1 (hasIndependentTransversal_of_reduced
        F color root (color y) hrootb x y hxcolor rfl hK)
    obtain ⟨S', D', hrootS', hDcard', hdom'⟩ :=
      rooted_domination_certificate K c' root' hKpart hY f' hf' hKno
    let S : Finset I := S'.image Subtype.val ∪ {color y}
    let emb : SurvivingVertices F x y ↪ V := Function.Embedding.subtype _
    let D : Finset V := D'.map emb ∪ {x, y}
    have hScard : S.card = S'.card + 1 := by
      have hdis : Disjoint (S'.image Subtype.val) ({color y} : Finset I) := by
        rw [Finset.disjoint_singleton_right]
        intro hmem
        simp only [mem_image] at hmem
        obtain ⟨i, hi, hieq⟩ := hmem
        exact i.2 hieq
      rw [show S = S'.image Subtype.val ∪ {color y} by rfl,
        card_union_of_disjoint hdis,
        Finset.card_image_of_injective S' Subtype.val_injective]
      simp
    have hDle : D.card ≤ D'.card + 2 := by
      calc
        D.card ≤ (D'.map emb).card + ({x, y} : Finset V).card := by
          simpa [D] using Finset.card_union_le (D'.map emb) {x, y}
        _ ≤ D'.card + 2 := by
          simpa using Nat.add_le_add_left (Finset.card_le_two (a := x) (b := y)) D'.card
    refine ⟨S, D, ?_, ?_, ?_⟩
    · have : root ∈ S'.image Subtype.val := by
        refine mem_image.mpr ⟨root', hrootS', ?_⟩
        rfl
      exact mem_union_left _ this
    · have hSpos : 1 ≤ S'.card := card_pos.mpr ⟨root', hrootS'⟩
      omega
    · intro z hzS
      by_cases hzW : z ∈ (neighbors F) x ∪ (neighbors F) y
      · rcases mem_union.mp hzW with hzx | hzy
        · refine ⟨x, ?_, hFG ?_⟩
          · simp [D]
          · exact (mem_neighbors F x z).mp hzx
        · refine ⟨y, ?_, hFG ?_⟩
          · simp [D]
          · exact (mem_neighbors F y z).mp hzy
      · let z' : SurvivingVertices F x y := ⟨z, hzW⟩
        have hzS' : c' z' ∈ S' := by
          have hzCases : color z ∈ S'.image Subtype.val ∨ color z = color y := by
            simpa [S] using mem_union.mp hzS
          rcases hzCases with hzimg | hzy
          · obtain ⟨i, hiS, hi⟩ := mem_image.mp hzimg
            have hzney : color z ≠ color y := by
              intro heq
              exact i.2 (hi.trans heq)
            have hc : c' z' = i := by
              apply Subtype.ext
              simpa [c', z', mergedColor, hzney] using hi.symm
            simpa [hc] using hiS
          · have hc : c' z' = root' := by
              apply Subtype.ext
              simp [c', z', mergedColor, hzy, root']
            simpa [hc] using hrootS'
        obtain ⟨d, hdD, hdz⟩ := hdom' z' hzS'
        refine ⟨d.1, ?_, hFG hdz.1⟩
        exact mem_union_left _ (mem_map.mpr ⟨d, hdD, rfl⟩)
  · refine ⟨{root, color y}, {x, y}, by simp, ?_, ?_⟩
    · simp [hrootb, hxy.ne]
    · intro z hz
      have hzColors : color z = root ∨ color z = color y := by
        simpa [eq_comm] using hz
      have hzW : z ∈ (neighbors F) x ∪ (neighbors F) y := by
        by_contra hnW
        let z' : SurvivingVertices F x y := ⟨z, hnW⟩
        have hc : c' z' = root' := by
          rcases hzColors with hzr | hzy
          · apply Subtype.ext
            simp [c', z', mergedColor, hzr, hrootb, root']
          · apply Subtype.ext
            simp [c', z', mergedColor, hzy, root']
        exact hY ⟨z', hc⟩
      rcases mem_union.mp hzW with hzx | hzy
      · refine ⟨x, by simp, hFG ?_⟩
        exact (mem_neighbors F x z).mp hzx
      · refine ⟨y, by simp, hFG ?_⟩
        exact (mem_neighbors F y z).mp hzy
termination_by Nat.card I
decreasing_by
  classical
  let _ := Fintype.ofFinite I
  have hcardpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨root⟩
  simpa [Nat.card_eq_fintype_card, ReducedColor] using
    Nat.sub_lt hcardpos (by omega : 0 < 1)

/-- Haxell's domination certificate: if a finite vertex-partitioned graph has
no independent transversal, some nonempty collection of colors is totally
dominated by at most twice one less than its number of colors. -/
theorem domination_certificate {I : Type u} {V : Type v}
    [Finite I] [Finite V]
    (G : SimpleGraph V) (color : V → I)
    (hpart : IsPartite G color) (hsurj : ∀ i, ∃ x, color x = i)
    (hno : ¬HasIndependentTransversal G color) :
    ∃ (S : Finset I) (D : Finset V),
      S.Nonempty ∧ D.card ≤ 2 * (S.card - 1) ∧ DominatesColors G color D S := by
  classical
  obtain ⟨F, hFG, hFmin⟩ := exists_edgeMinimal_le G color hno
  have hFpart : IsPartite F color := fun _ _ h ↦ hpart (hFG h)
  have hedge : ∃ x y, F.Adj x y := by
    by_contra h
    push Not at h
    choose q hq using hsurj
    apply hFmin.1
    refine ⟨q, hq, ?_⟩
    intro i j hij
    exact h (q i) (q j)
  obtain ⟨x, y, hxy⟩ := hedge
  obtain ⟨g, hg⟩ := hFmin.2 hxy
  have hend := deletedEdge_endpoints hFmin.1 hg
  let root := color x
  let f : {i : I // i ≠ root} → V := fun i ↦ g i.1
  have hf : IsPartialTransversalExcept F color root f := by
    constructor
    · intro i
      exact hg.1 i.1
    · intro i j hij
      have hijold : i.1 ≠ j.1 := by
        intro heq
        exact hij (Subtype.ext heq)
      by_cases hiy : i.1 = color y
      · have hjy : j.1 ≠ color y := by
          intro hj
          exact hijold (hiy.trans hj.symm)
        have hav := deletedTransversal_avoids_endpoints hxy hg hend
          j.2 hjy
        simpa [f, hiy, hend.2, F.adj_comm] using hav.2
      · by_cases hjy : j.1 = color y
        · have hav := deletedTransversal_avoids_endpoints hxy hg hend
            i.2 hiy
          simpa [f, hjy, hend.2, F.adj_comm] using hav.2
        · simpa [f] using deletedTransversal_other_pair hg hijold i.2 hiy
  obtain ⟨S, D, hrootS, hDcard, hdom⟩ :=
    rooted_domination_certificate F color root hFpart
      ⟨x, rfl⟩ f hf hFmin.1
  refine ⟨S, D, ⟨root, hrootS⟩, hDcard, ?_⟩
  intro z hz
  obtain ⟨d, hdD, hdz⟩ := hdom z hz
  exact ⟨d, hdD, hFG hdz⟩

/-- Counting the vertices in dominated color classes by the neighborhoods of
their dominators. -/
lemma card_colors_mul_le_sum_degree {I : Type u} {V : Type v}
    [DecidableEq I] [Fintype V]
    (G : SimpleGraph V) (color : V → I) (n : ℕ)
    (hsize : ∀ i, (Finset.univ.filter fun x ↦ color x = i).card = n)
    {S : Finset I} {D : Finset V} (hdom : DominatesColors G color D S) :
    S.card * n ≤ ∑ d ∈ D, graphDegree G d := by
  classical
  let fiber : I → Finset V := fun i ↦ Finset.univ.filter fun x ↦ color x = i
  let U : Finset V := S.biUnion fiber
  have hpair : (S : Set I).PairwiseDisjoint fiber := by
    intro i hi j hj hij
    change Disjoint (fiber i) (fiber j)
    rw [Finset.disjoint_left]
    intro z hzi hzj
    have hci : color z = i := by simpa [fiber] using hzi
    have hcj : color z = j := by simpa [fiber] using hzj
    exact hij (hci.symm.trans hcj)
  have hUcard : U.card = S.card * n := by
    rw [show U = S.biUnion fiber by rfl, Finset.card_biUnion hpair]
    simp [fiber, hsize]
  have hsubset : U ⊆ D.biUnion (neighbors G) := by
    intro z hzU
    obtain ⟨i, hiS, hzi⟩ := mem_biUnion.mp hzU
    have hzcolor : color z = i := by simpa [fiber] using hzi
    obtain ⟨d, hdD, hdz⟩ := hdom z (by simpa [hzcolor] using hiS)
    exact mem_biUnion.mpr ⟨d, hdD, by simpa [mem_neighbors] using hdz⟩
  calc
    S.card * n = U.card := hUcard.symm
    _ ≤ (D.biUnion (neighbors G)).card := card_le_card hsubset
    _ ≤ ∑ d ∈ D, ((neighbors G) d).card := Finset.card_biUnion_le
    _ = ∑ d ∈ D, graphDegree G d := by simp [graphDegree]

/-- Haxell's finite coefficient: balanced color classes of size `n` have an
independent transversal below the `r / (2(r-1))` maximum-degree threshold. -/
theorem hasIndependentTransversal_of_degree_bound
    {I : Type u} {V : Type v}
    [Fintype I] [DecidableEq I] [Fintype V]
    (G : SimpleGraph V) (color : V → I) (n : ℕ)
    (_hI : 2 ≤ Fintype.card I) (hn : 0 < n)
    (hpart : IsPartite G color)
    (hsize : ∀ i, (Finset.univ.filter fun x ↦ color x = i).card = n)
    (hdegree : ∀ x, 2 * (Fintype.card I - 1) * graphDegree G x < Fintype.card I * n) :
    HasIndependentTransversal G color := by
  classical
  by_contra hno
  have hsurj : ∀ i, ∃ x, color x = i := by
    intro i
    have hpos : 0 < (Finset.univ.filter fun x ↦ color x = i).card := by
      rw [hsize i]
      exact hn
    obtain ⟨x, hx⟩ := card_pos.mp hpos
    exact ⟨x, by simpa using hx⟩
  obtain ⟨S, D, hSne, hDcard, hdom⟩ :=
    domination_certificate G color hpart hsurj hno
  have hcount := card_colors_mul_le_sum_degree G color n hsize hdom
  have hDne : D.Nonempty := by
    obtain ⟨i, hiS⟩ := hSne
    obtain ⟨x, hx⟩ := hsurj i
    obtain ⟨d, hdD, _⟩ := hdom x (by simpa [hx] using hiS)
    exact ⟨d, hdD⟩
  have hsumlt :
      2 * (Fintype.card I - 1) * (∑ d ∈ D, graphDegree G d) <
        D.card * (Fintype.card I * n) := by
    calc
      2 * (Fintype.card I - 1) * (∑ d ∈ D, graphDegree G d) =
          ∑ d ∈ D, 2 * (Fintype.card I - 1) * graphDegree G d := by
            simp [Finset.mul_sum]
      _ < ∑ _d ∈ D, Fintype.card I * n := by
        exact Finset.sum_lt_sum_of_nonempty hDne fun d _ ↦ hdegree d
      _ = D.card * (Fintype.card I * n) := by simp
  have hSle : S.card ≤ Fintype.card I := by
    simpa using card_le_univ S
  have hscaled :
      2 * (Fintype.card I - 1) * (S.card * n) ≤
        2 * (Fintype.card I - 1) * (∑ d ∈ D, graphDegree G d) := by
    exact Nat.mul_le_mul_left _ hcount
  have hSpos : 1 ≤ S.card := card_pos.mpr hSne
  have hkey0 : (S.card - 1) * Fintype.card I ≤
      (Fintype.card I - 1) * S.card := by
    rw [Nat.sub_mul, Nat.sub_mul]
    simp only [one_mul]
    rw [Nat.mul_comm (Fintype.card I) S.card]
    exact Nat.sub_le_sub_left hSle (S.card * Fintype.card I)
  have hkey : 2 * (S.card - 1) * Fintype.card I ≤
      2 * (Fintype.card I - 1) * S.card := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hkey0
  have hupper : D.card * (Fintype.card I * n) ≤
      2 * (Fintype.card I - 1) * (S.card * n) := by
    calc
      D.card * (Fintype.card I * n) ≤
          (2 * (S.card - 1)) * (Fintype.card I * n) :=
        Nat.mul_le_mul_right _ hDcard
      _ = (2 * (S.card - 1) * Fintype.card I) * n := by
        simp [Nat.mul_assoc]
      _ ≤ (2 * (Fintype.card I - 1) * S.card) * n :=
        Nat.mul_le_mul_right n hkey
      _ = 2 * (Fintype.card I - 1) * (S.card * n) := by
        simp [Nat.mul_assoc]
  have hbad := lt_of_lt_of_le hsumlt hupper
  exact (not_lt_of_ge hscaled) hbad

/-! ## Multipartite complements and Erdős Problem 1078 -/

/-- The multipartite complement: only pairs in different parts are eligible,
and such a pair is an edge exactly when it is absent from `G`. -/
def multipartiteComplement {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) :
    SimpleGraph (Fin r × Fin n) where
  Adj x y := x.1 ≠ y.1 ∧ ¬G.Adj x y
  symm.symm _ _ h := ⟨h.1.symm, fun hyx ↦ h.2 hyx.symm⟩
  loopless.irrefl _ h := h.1 rfl

lemma multipartiteComplement_isPartite {r n : ℕ}
    (G : SimpleGraph (Fin r × Fin n)) :
    IsPartite (multipartiteComplement G) Prod.fst := by
  intro x y hxy
  exact hxy.1

/-- A transversal clique, represented by its color-respecting choice
function. -/
def IsCliqueTransversal {r n : ℕ} (G : SimpleGraph (Fin r × Fin n))
    (f : Fin r → Fin r × Fin n) : Prop :=
  (∀ i, (f i).1 = i) ∧ ∀ i j, i ≠ j → G.Adj (f i) (f j)

/-- The graph contains a copy of `K_r` with one vertex in each specified
part. -/
def HasTransversalKr {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∃ f : Fin r → Fin r × Fin n, IsCliqueTransversal G f

lemma hasTransversalKr_of_complement_independent {r n : ℕ}
    {G : SimpleGraph (Fin r × Fin n)}
    (h : HasIndependentTransversal (multipartiteComplement G) Prod.fst) :
    HasTransversalKr G := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, hf.1, ?_⟩
  intro i j hij
  by_contra hG
  exact hf.2 i j hij ⟨by simpa [hf.1 i, hf.1 j] using hij, hG⟩

lemma colorFiber_card (r n : ℕ) (i : Fin r) :
    (Finset.univ.filter fun x : Fin r × Fin n ↦ x.1 = i).card = n := by
  classical
  have heq :
      (Finset.univ.filter fun x : Fin r × Fin n ↦ x.1 = i) =
        ({i} : Finset (Fin r)) ×ˢ (Finset.univ : Finset (Fin n)) := by
    ext x
    rcases x with ⟨j, a⟩
    simp only [mem_filter, mem_univ, true_and, singleton_product, mem_map,
      Function.Embedding.coeFn_mk, Prod.mk.injEq, exists_eq_right]
    exact eq_comm
  rw [heq, card_product]
  simp

/-- The degree in the multipartite complement is the number of vertices in
the other parts minus the original degree. -/
lemma degree_multipartiteComplement {r n : ℕ}
    (G : SimpleGraph (Fin r × Fin n))
    (hpart : IsPartite G Prod.fst) (x : Fin r × Fin n) :
    graphDegree (multipartiteComplement G) x = (r - 1) * n - graphDegree G x := by
  classical
  let outside : Finset (Fin r × Fin n) :=
    Finset.univ.filter fun y ↦ x.1 ≠ y.1
  have hneigh :
      neighbors (multipartiteComplement G) x =
        outside \ neighbors G x := by
    ext y
    simp only [mem_sdiff, mem_neighbors]
    change (x.1 ≠ y.1 ∧ ¬G.Adj x y) ↔ (y ∈ outside ∧ ¬G.Adj x y)
    simp [outside]
  have hsub : neighbors G x ⊆ outside := by
    intro y hy
    have hxy : G.Adj x y := (mem_neighbors G x y).mp hy
    simpa [outside] using hpart hxy
  have houtside : outside.card = (r - 1) * n := by
    let fiber : Finset (Fin r × Fin n) :=
      Finset.univ.filter fun y ↦ y.1 = x.1
    have hout : outside = Finset.univ \ fiber := by
      ext y
      simp [outside, fiber, ne_comm]
    rw [hout, card_sdiff_of_subset (subset_univ fiber), card_univ,
      show fiber.card = n by simpa [fiber] using colorFiber_card r n x.1]
    simpa [Fintype.card_prod] using (Nat.sub_mul r 1 n).symm
  simp only [graphDegree]
  rw [hneigh, card_sdiff_of_subset hsub, houtside]

/-- **Erdős Problem 1078 (Haxell).**  The natural-number inequality is the
division-free form of
`deg(v) > (r - 3/2 - 1/(2(r-1))) n`; its error term tends to zero as the
number of parts tends to infinity. -/
theorem erdos_1078 {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (G : SimpleGraph (Fin r × Fin n))
    (hpart : IsPartite G Prod.fst)
    (hdegree : ∀ x,
      2 * (r - 1) * ((r - 1) * n - graphDegree G x) < r * n) :
    HasTransversalKr G := by
  let H := multipartiteComplement G
  have hHdegree : ∀ x, 2 * (Fintype.card (Fin r) - 1) * graphDegree H x <
      Fintype.card (Fin r) * n := by
    intro x
    simpa [H, degree_multipartiteComplement G hpart x] using hdegree x
  apply hasTransversalKr_of_complement_independent
  exact hasIndependentTransversal_of_degree_bound H Prod.fst n
    (by simpa using hr) hn (multipartiteComplement_isPartite G)
    (colorFiber_card r n) hHdegree

end Erdos1078

#print axioms Erdos1078.erdos_1078

alias _root_.Erdos1078.erdos1078 := _root_.Erdos1078.erdos_1078
