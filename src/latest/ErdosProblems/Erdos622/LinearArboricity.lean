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
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Linear forests and the asymptotic linear-arboricity interface

This file fixes the exact finite statement of the asymptotic
linear-arboricity theorem used in the almost-bipartite case of Erdős 622.
It also proves the bookkeeping facts which turn an edge coloring by linear
forests into an honest edge decomposition and extract a color class at least
as large as the average.

The central external mathematical input has the following quantifier order:
for every positive real `epsilon`, there is a degree threshold `D₀`, uniform
over the finite vertex type and the graph, such that a graph of maximum
degree at most `D ≥ D₀` is the union of at most
`(1 + epsilon) * D / 2` linear forests.
-/

open Finset
open scoped BigOperators

namespace Erdos622

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V]

/-- A linear forest is an acyclic graph of maximum degree at most two. -/
def IsLinearForest (F : SimpleGraph V) : Prop :=
  F.IsAcyclic ∧ ∀ v, F.degree v ≤ 2

lemma IsLinearForest.isAcyclic {F : SimpleGraph V} (hF : IsLinearForest F) :
    F.IsAcyclic :=
  hF.1

lemma IsLinearForest.degree_le_two {F : SimpleGraph V} (hF : IsLinearForest F)
    (v : V) : F.degree v ≤ 2 :=
  hF.2 v

lemma isLinearForest_bot : IsLinearForest (⊥ : SimpleGraph V) := by
  refine ⟨_root_.SimpleGraph.isAcyclic_bot, ?_⟩
  intro v
  simp [_root_.SimpleGraph.degree]

/-- A graph of maximum degree at most one cannot contain a cycle. -/
lemma isAcyclic_of_degree_le_one {F : SimpleGraph V}
    (hdegree : ∀ v, F.degree v ≤ 1) : F.IsAcyclic := by
  intro v c hc
  have htwo : (c.toSubgraph.neighborSet v).ncard = 2 :=
    hc.ncard_neighborSet_toSubgraph_eq_two c.start_mem_support
  have hsub : c.toSubgraph.spanningCoe ≤ F :=
    _root_.SimpleGraph.Subgraph.spanningCoe_le c.toSubgraph
  have hle : (c.toSubgraph.neighborSet v).ncard ≤
      (F.neighborSet v).ncard :=
    Set.ncard_le_ncard (_root_.SimpleGraph.neighborSet_mono hsub v)
  have hright : (F.neighborSet v).ncard = F.degree v := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  rw [htwo, hright] at hle
  have hone := hdegree v
  omega

lemma isLinearForest_of_degree_le_one {F : SimpleGraph V}
    (hdegree : ∀ v, F.degree v ≤ 1) : IsLinearForest F :=
  ⟨isAcyclic_of_degree_le_one hdegree,
    fun v ↦ (hdegree v).trans (by omega)⟩

lemma IsLinearForest.anti {F H : SimpleGraph V} (hFH : F ≤ H)
    (hH : IsLinearForest H) : IsLinearForest F := by
  refine ⟨(IsLinearForest.isAcyclic hH).anti hFH, ?_⟩
  intro v
  exact (card_le_card (by
    simpa only [_root_.SimpleGraph.neighborFinset_def,
      Set.toFinset_subset_toFinset] using
      _root_.SimpleGraph.neighborSet_mono hFH v)).trans
        (IsLinearForest.degree_le_two hH v)

end SimpleGraph

namespace LinearArboricity

variable {V : Type u} [Fintype V]

/-- An edge color, with no properness requirement.  Its fibers are intended
to be the linear forests in a decomposition. -/
abbrev EdgePartition (G : SimpleGraph V) (k : ℕ) := G.edgeSet → Fin k

/-- The finite fiber of one color in an edge partition. -/
def colorClass {G : SimpleGraph V} {k : ℕ} (c : EdgePartition G k)
    (i : Fin k) : Finset G.edgeSet :=
  (univ : Finset G.edgeSet).filter fun e ↦ c e = i

@[simp] lemma mem_colorClass {G : SimpleGraph V} {k : ℕ}
    (c : EdgePartition G k) (i : Fin k) (e : G.edgeSet) :
    e ∈ colorClass c i ↔ c e = i := by
  simp [colorClass]

/-- The spanning subgraph consisting of one fiber of an edge partition. -/
def colorGraph {G : SimpleGraph V} {k : ℕ} (c : EdgePartition G k)
    (i : Fin k) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ he : e ∈ G.edgeSet, c ⟨e, he⟩ = i}

lemma colorGraph_le {G : SimpleGraph V} {k : ℕ} (c : EdgePartition G k)
    (i : Fin k) : colorGraph c i ≤ G := by
  change SimpleGraph.fromEdgeSet
    {e | ∃ he : e ∈ G.edgeSet, c ⟨e, he⟩ = i} ≤ G
  rw [SimpleGraph.fromEdgeSet_le]
  intro e he
  exact he.1.choose

lemma mem_colorGraph_edgeSet_iff {G : SimpleGraph V} {k : ℕ}
    (c : EdgePartition G k) (i : Fin k) (e : Sym2 V) :
    e ∈ (colorGraph c i).edgeSet ↔
      ∃ he : e ∈ G.edgeSet, c ⟨e, he⟩ = i := by
  constructor
  · intro he
    change e ∈ (SimpleGraph.fromEdgeSet
      {e : Sym2 V | ∃ he : e ∈ G.edgeSet, c ⟨e, he⟩ = i}).edgeSet at he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at he
    exact he.1
  · rintro ⟨heG, hc⟩
    change e ∈ (SimpleGraph.fromEdgeSet
      {e : Sym2 V | ∃ he : e ∈ G.edgeSet, c ⟨e, he⟩ = i}).edgeSet
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨heG, hc⟩, ?_⟩
    exact G.not_isDiag_of_mem_edgeSet heG

lemma mem_colorGraph_edgeSet {G : SimpleGraph V} {k : ℕ}
    (c : EdgePartition G k) (e : G.edgeSet) :
    e.1 ∈ (colorGraph c (c e)).edgeSet :=
  (mem_colorGraph_edgeSet_iff c (c e) e.1).2 ⟨e.2, rfl⟩

/-- The abstract edge fiber and the ordinary edge finset of its color graph
have the same cardinality. -/
lemma map_colorClass_eq_edgeFinset [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} (c : EdgePartition G k) (i : Fin k) :
    (colorClass c i).map (Function.Embedding.subtype G.edgeSet) =
      (colorGraph c i).edgeFinset := by
  ext e
  simp only [Finset.mem_map, SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_colorGraph_edgeSet_iff c i a.1).2
      ⟨a.2, (mem_colorClass c i a).1 ha⟩
  · intro heColor
    obtain ⟨heG, hc⟩ := (mem_colorGraph_edgeSet_iff c i e).1 heColor
    exact ⟨⟨e, heG⟩, (mem_colorClass c i ⟨e, heG⟩).2 hc, rfl⟩

lemma card_edgeFinset_colorGraph [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} (c : EdgePartition G k) (i : Fin k) :
    (colorGraph c i).edgeFinset.card = (colorClass c i).card := by
  rw [← map_colorClass_eq_edgeFinset c i, Finset.card_map]

/-- The color graphs cover the original graph.  This remains true for zero
colors: in that case the edge subtype of `G` is empty. -/
lemma iSup_colorGraph {G : SimpleGraph V} {k : ℕ} (c : EdgePartition G k) :
    (⨆ i, colorGraph c i) = G := by
  apply le_antisymm
  · exact iSup_le fun i ↦ colorGraph_le c i
  · intro v w hvw
    let e : G.edgeSet := ⟨s(v, w), hvw⟩
    have hcolor : (colorGraph c (c e)).Adj v w := by
      rw [← SimpleGraph.mem_edgeSet]
      exact mem_colorGraph_edgeSet c e
    exact (le_iSup (fun i ↦ colorGraph c i) (c e)) hcolor

/-- Distinct color graphs have disjoint edge sets. -/
lemma colorGraph_disjoint {G : SimpleGraph V} {k : ℕ} (c : EdgePartition G k)
    {i j : Fin k} (hij : i ≠ j) : Disjoint (colorGraph c i) (colorGraph c j) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e hei hej
  obtain ⟨heG, hci⟩ := (mem_colorGraph_edgeSet_iff c i e).1 hei
  obtain ⟨_heG, hcj⟩ := (mem_colorGraph_edgeSet_iff c j e).1 hej
  exact hij (hci.symm.trans hcj)

/-- The color fibers partition the whole edge subtype in cardinality form. -/
lemma sum_card_colorClass {G : SimpleGraph V} {k : ℕ}
    (c : EdgePartition G k) :
    ∑ i : Fin k, (colorClass c i).card = Fintype.card G.edgeSet := by
  rw [← Finset.card_univ]
  symm
  simpa only [colorClass] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (univ : Finset G.edgeSet))
      (t := (univ : Finset (Fin k)))
      (f := fun e ↦ c e) (by simp))

/-- Some fiber has at least the average size, in an integral form avoiding
division. -/
lemma exists_card_le_mul_colorClass {G : SimpleGraph V} {k : ℕ}
    (c : EdgePartition G k) (hk : 0 < k) :
    ∃ i : Fin k, Fintype.card G.edgeSet ≤ k * (colorClass c i).card := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image
    (univ : Finset (Fin k)) (fun i ↦ (colorClass c i).card)
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  rw [← sum_card_colorClass c]
  calc
    ∑ j : Fin k, (colorClass c j).card ≤
        ∑ _j : Fin k, (colorClass c i).card := by
          exact Finset.sum_le_sum fun j _hj ↦ hi j (by simp)
    _ = k * (colorClass c i).card := by simp [Nat.mul_comm]

/-- A linear-forest edge decomposition, represented by its total edge-color
function.  Exact coverage and pairwise edge-disjointness follow from the
representation and are proved above. -/
structure Decomposition (G : SimpleGraph V) (k : ℕ) where
  color : EdgePartition G k
  linear : ∀ i, Erdos622.SimpleGraph.IsLinearForest (colorGraph color i)

namespace Decomposition

variable {G : SimpleGraph V} {k : ℕ}

lemma cover (d : Decomposition G k) :
    (⨆ i, colorGraph d.color i) = G :=
  iSup_colorGraph d.color

lemma pairwise_disjoint (d : Decomposition G k) :
    Pairwise fun i j ↦ Disjoint (colorGraph d.color i) (colorGraph d.color j) := by
  intro i j hij
  exact colorGraph_disjoint d.color hij

lemma exists_large_class (d : Decomposition G k) (hk : 0 < k) :
    ∃ i : Fin k,
      Fintype.card G.edgeSet ≤ k * (colorClass d.color i).card ∧
      Erdos622.SimpleGraph.IsLinearForest (colorGraph d.color i) := by
  obtain ⟨i, hi⟩ := exists_card_le_mul_colorClass d.color hk
  exact ⟨i, hi, d.linear i⟩

/-- Real-valued averaging form used in the induced-edge estimates of the
DKM argument. -/
lemma exists_large_linearForest [DecidableEq V] (d : Decomposition G k)
    (hk : 0 < k) :
    ∃ F : SimpleGraph V,
      F ≤ G ∧ Erdos622.SimpleGraph.IsLinearForest F ∧
      (Fintype.card G.edgeSet : ℝ) / (k : ℝ) ≤
        (Fintype.card F.edgeSet : ℝ) := by
  obtain ⟨i, hi, hlinear⟩ := d.exists_large_class hk
  refine ⟨colorGraph d.color i, colorGraph_le d.color i, hlinear, ?_⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_iff₀ hkR]
  have hcard : Fintype.card (colorGraph d.color i).edgeSet =
      (colorClass d.color i).card := by
    rw [SimpleGraph.card_edgeSet, card_edgeFinset_colorGraph d.color i]
  rw [hcard]
  exact_mod_cast (by simpa [Nat.mul_comm] using hi)

end Decomposition

/-- Exact quantifier-level statement of Alon's asymptotic linear-arboricity
theorem.  The degree parameter is an upper bound rather than definitionally
the graph's maximum degree; this is the form needed after random induction in
the Erdős 622 argument. -/
def AsymptoticLinearArboricity : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ D₀ : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (D : ℕ),
        D₀ ≤ D →
        (∀ v, G.degree v ≤ D) →
        ∃ k : ℕ, 0 < k ∧
          (k : ℝ) ≤ (1 + epsilon) * (D : ℝ) / 2 ∧
          Nonempty (Decomposition G k)

end LinearArboricity

end

end Erdos622
