import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Erdős Problem 581: exact extremal definitions

This file fixes the literal finite-graph meaning of the function in Problem 581
and records the equivalence between bipartite subgraphs and cuts.
-/

open Finset Set
open scoped Classical ENNReal

namespace Erdos581

/-- `Guarantees m k` says that every finite triangle-free simple graph with
exactly `m` edges contains a bipartite subgraph with at least `k` edges. -/
def Guarantees (m k : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.CliqueFree 3 → G.edgeSet.ncard = m →
      ∃ H : SimpleGraph V,
        H ≤ G ∧ H.IsBipartite ∧ k ≤ H.edgeSet.ncard

/-- The exact extremal function in Erdős Problem 581. -/
noncomputable def f (m : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (Guarantees m) m

lemma ncard_edgeSet_completeBipartiteGraph (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).edgeSet.ncard = a * b := by
  rw [← Nat.cast_inj (R := ℕ∞)]
  rw [Set.Finite.cast_ncard_eq (Set.toFinite _)]
  simp [SimpleGraph.encard_edgeSet_completeBipartiteGraph]

lemma isBipartite_cliqueFree_three {V : Type*} {G : SimpleGraph V}
    (hG : G.IsBipartite) : G.CliqueFree 3 :=
  hG.cliqueFree (by omega)

lemma completeBipartiteGraph_isBipartite (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)) ?_⟩
  rintro (u | u) (v | v) huv <;> simp_all

lemma guarantees_le_edges {m k : ℕ} (h : Guarantees m k) : k ≤ m := by
  let G := completeBipartiteGraph (Fin 1) (Fin m)
  have hbip : G.IsBipartite := by
    simpa [G] using completeBipartiteGraph_isBipartite 1 m
  obtain ⟨H, hHG, -, hk⟩ := h (Fin 1 ⊕ Fin m) G (isBipartite_cliqueFree_three hbip) (by
    simpa [G] using ncard_edgeSet_completeBipartiteGraph 1 m)
  have hsub : H.edgeSet ⊆ G.edgeSet := SimpleGraph.edgeSet_mono hHG
  have hcard : H.edgeSet.ncard ≤ m := by
    simpa [G, ncard_edgeSet_completeBipartiteGraph] using Set.ncard_le_ncard hsub
  exact hk.trans hcard

lemma guarantees_zero (m : ℕ) : Guarantees m 0 := by
  intro V _ G _ _
  refine ⟨⊥, bot_le, ?_, by simp⟩
  exact ⟨SimpleGraph.Coloring.mk (fun _ ↦ 0) (by simp)⟩

lemma le_f_of_guarantees {m k : ℕ} (h : Guarantees m k) : k ≤ f m := by
  classical
  unfold f
  exact Nat.le_findGreatest (guarantees_le_edges h) h

lemma f_spec (m : ℕ) : Guarantees m (f m) := by
  classical
  unfold f
  exact Nat.findGreatest_spec (Nat.zero_le m) (guarantees_zero m)

lemma f_le (m : ℕ) : f m ≤ m := by
  exact guarantees_le_edges (f_spec m)

/-- The spanning subgraph of `G` consisting of the edges crossing `s`. -/
def cutGraph {V : Type*} (G : SimpleGraph V) (s : Set V) : SimpleGraph V :=
  G.between s sᶜ

lemma cutGraph_le {V : Type*} (G : SimpleGraph V) (s : Set V) :
    cutGraph G s ≤ G :=
  SimpleGraph.between_le

lemma cutGraph_isBipartite {V : Type*} (G : SimpleGraph V) (s : Set V) :
    (cutGraph G s).IsBipartite := by
  exact G.between_isBipartite disjoint_compl_right

@[simp] lemma cutGraph_adj {V : Type*} (G : SimpleGraph V) (s : Set V) (u v : V) :
    (cutGraph G s).Adj u v ↔ G.Adj u v ∧ ((u ∈ s) ≠ (v ∈ s)) := by
  rw [cutGraph, SimpleGraph.between_adj]
  simp only [Set.mem_compl_iff]
  tauto

/-- Every bipartite subgraph of `G` is contained in one of the spanning cut
graphs of `G`. -/
lemma bipartite_le_cutGraph {V : Type*} {G H : SimpleGraph V}
    (hHG : H ≤ G) (hH : H.IsBipartite) :
    ∃ s : Set V, H ≤ cutGraph G s := by
  obtain ⟨s, t, hst⟩ := hH.exists_isBipartiteWith
  refine ⟨s, fun u v huv ↦ ?_⟩
  rw [cutGraph_adj]
  refine ⟨hHG huv, ?_⟩
  obtain huv' | huv' := hst.mem_of_adj huv
  · exact fun heq ↦ (hst.disjoint.subset_compl_left huv'.2) (heq.mp huv'.1)
  · exact fun heq ↦ (hst.disjoint.subset_compl_left huv'.1) (heq.mpr huv'.2)

/-- Cardinal form of `bipartite_le_cutGraph`. -/
lemma ncard_le_cutGraph_of_bipartite {V : Type*} [Finite V]
    {G H : SimpleGraph V} (hHG : H ≤ G) (hH : H.IsBipartite) :
    ∃ s : Set V, H.edgeSet.ncard ≤ (cutGraph G s).edgeSet.ncard := by
  obtain ⟨s, hs⟩ := bipartite_le_cutGraph hHG hH
  exact ⟨s, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hs)⟩

/-- A real lower bound for the size of a cut gives the same lower bound for a
bipartite subgraph. -/
lemma exists_bipartite_of_exists_cut {V : Type*} [Finite V]
    (G : SimpleGraph V) (x : ℝ)
    (h : ∃ s : Set V, x ≤ ((cutGraph G s).edgeSet.ncard : ℝ)) :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ H.IsBipartite ∧ x ≤ (H.edgeSet.ncard : ℝ) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨cutGraph G s, cutGraph_le G s, cutGraph_isBipartite G s, hs⟩

end Erdos581
