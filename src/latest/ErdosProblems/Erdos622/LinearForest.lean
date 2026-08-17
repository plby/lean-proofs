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
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Linear forests for Erdos Problem 622

This file contains the finite graph lemmas used in the almost-bipartite case of the
Draganić--Keevash--Müyesser argument.  We represent a linear forest by its standard
characterization: it is acyclic and has maximum degree at most two.

The main constructions are:

* exact truncation to any prescribed smaller number of edges;
* breaking all cyclic components of the union of two matchings while retaining the
  same connected components;
* uniqueness of paths inside a linear forest;
* safe insertion and splicing of paths.
-/

open scoped SimpleGraph

namespace Erdos622

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite graph is a linear forest if it is acyclic and every vertex has degree at most two. -/
def LinearForest (F : SimpleGraph V) : Prop :=
  F.IsAcyclic ∧ ∀ v, F.degree v ≤ 2

/-- A graph-level matching: an acyclic graph in which every vertex has degree at most one.

The acyclicity field is redundant mathematically, but keeping it in the interface avoids
re-proving that fact each time a matching is converted from one of Mathlib's subgraph-level
matching structures. -/
def MatchingGraph (M : SimpleGraph V) : Prop :=
  M.IsAcyclic ∧ ∀ v, M.degree v ≤ 1

/-- An edge set meets every simple cycle of `G`. -/
def CycleTransversal (G : SimpleGraph V) (D : Set (Sym2 V)) : Prop :=
  ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → ∃ e ∈ p.edges, e ∈ D

namespace CycleTransversal

variable {G : SimpleGraph V} {D : Set (Sym2 V)}

/-- If deleting `D` leaves an acyclic graph, then `D` meets every cycle of the original graph. -/
theorem of_isAcyclic_deleteEdges (hD : (G.deleteEdges D).IsAcyclic) :
    CycleTransversal G D := by
  intro u p hp
  by_contra! havoid
  have hnotmem : ∀ e, e ∈ p.edges → e ∉ D := by
    intro e he hed
    exact havoid e he hed
  let q : (G.deleteEdges D).Walk u u := p.toDeleteEdges D hnotmem
  have hmap : q.map (.ofLE (G.deleteEdges_le D)) = p := by
    exact p.map_toDeleteEdges_eq D hnotmem
  have hq : q.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.of_map (f := .ofLE (G.deleteEdges_le D))
      (hmap.symm ▸ hp)
  exact hD q hq

end CycleTransversal

namespace LinearForest

variable {F H K : SimpleGraph V}

/-- The empty graph is a linear forest. -/
@[simp]
theorem bot : LinearForest (⊥ : SimpleGraph V) := by
  refine ⟨SimpleGraph.isAcyclic_bot, ?_⟩
  intro v
  simp

/-- A spanning subgraph of a linear forest is again a linear forest. -/
theorem anti (hF : LinearForest F) (hHF : H ≤ F) : LinearForest H := by
  refine ⟨hF.1.anti hHF, ?_⟩
  intro v
  exact (H.degree_le_of_le hHF).trans (hF.2 v)

/-- A linear forest with at least `r` edges has a spanning subforest with exactly `r` edges. -/
theorem exists_subforest_card_eq (hF : LinearForest F) {r : ℕ}
    (hr : r ≤ F.edgeFinset.card) :
    ∃ H : SimpleGraph V, H ≤ F ∧ LinearForest H ∧ H.edgeFinset.card = r := by
  obtain ⟨s, hsF, hscard⟩ := Finset.exists_subset_card_eq hr
  refine ⟨F.deleteEdges (↑(F.edgeFinset \ s) : Set (Sym2 V)), SimpleGraph.deleteEdges_le _,
    hF.anti (SimpleGraph.deleteEdges_le _), ?_⟩
  rw [SimpleGraph.edgeFinset_deleteEdges,
    Finset.sdiff_sdiff_eq_self hsF, hscard]

/-- Exact truncation, with the subgraph relation and cardinality ordered for convenient use. -/
theorem exists_subforest_card_eq_and_le (hF : LinearForest F) {r : ℕ}
    (hr : r ≤ F.edgeFinset.card) :
    ∃ H : SimpleGraph V, H ≤ F ∧ H.edgeFinset.card = r ∧ LinearForest H := by
  obtain ⟨H, hHF, hlin, hcard⟩ := hF.exists_subforest_card_eq hr
  exact ⟨H, hHF, hcard, hlin⟩

/-- Reachable vertices in a linear forest are joined by a unique simple path. -/
theorem existsUnique_path (hF : LinearForest F) {u v : V} (huv : F.Reachable u v) :
    ∃! p : F.Walk u v, p.IsPath := by
  let p : F.Path u v := huv.some.toPath
  refine ⟨p, p.property, ?_⟩
  intro q hq
  exact Subtype.mk.inj (hF.1.subsingleton_path u v |>.elim ⟨q, hq⟩ p)

/-- Add an edge between two different components at vertices of degree at most one.
The result is again a linear forest. -/
theorem sup_edge_of_not_reachable (hF : LinearForest F) {u v : V}
    (huv : ¬F.Reachable u v) (hu : F.degree u ≤ 1) (hv : F.degree v ≤ 1) :
    LinearForest (F ⊔ SimpleGraph.edge u v) := by
  refine ⟨hF.1.sup_edge_of_not_reachable huv, ?_⟩
  intro w
  by_cases hwu : w = u
  · subst w
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_sup]
    calc
      (F.neighborFinset u ∪ (SimpleGraph.edge u v).neighborFinset u).card
          ≤ (F.neighborFinset u).card +
              ((SimpleGraph.edge u v).neighborFinset u).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add hu (by
        apply Finset.card_le_one_iff.mpr
        intro x y hx hy
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj] at hx hy
        grind)
      _ = 2 := rfl
  · by_cases hwv : w = v
    · subst w
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.neighborFinset_sup]
      calc
        (F.neighborFinset v ∪ (SimpleGraph.edge u v).neighborFinset v).card
            ≤ (F.neighborFinset v).card +
                ((SimpleGraph.edge u v).neighborFinset v).card := Finset.card_union_le _ _
        _ ≤ 1 + 1 := Nat.add_le_add hv (by
          apply Finset.card_le_one_iff.mpr
          intro x y hx hy
          simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj] at hx hy
          grind)
        _ = 2 := rfl
    · have hedge : (SimpleGraph.edge u v).neighborFinset w = ∅ := by
        ext x
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj,
          Finset.notMem_empty, iff_false]
        grind
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.neighborFinset_sup, hedge, Finset.union_empty]
      exact hF.2 w

/-- Two paths that meet only at their common endpoint splice to a simple path.

The paths may initially lie in different spanning subgraphs of a common ambient graph. -/
theorem append_path_of_disjoint {G H : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : H.Walk v w) (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ x, x ∈ p.support → x ∈ q.support.tail → False) :
    ((p.mapLe le_sup_left).append (q.mapLe le_sup_right)).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_mapLe_eq_support,
    SimpleGraph.Walk.support_mapLe_eq_support]
  rw [List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_iff_ne]
  intro x hx y hy hxy
  subst y
  exact hdisj x hx hy

end LinearForest

namespace MatchingGraph

variable {M M₁ M₂ : SimpleGraph V}

/-- The usual degree-at-most-one definition produces a graph-level matching. -/
theorem of_degree_le_one (hM : ∀ v, M.degree v ≤ 1) : MatchingGraph M := by
  refine ⟨?_, hM⟩
  intro u p hp
  have htwo := hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support
  have hle : (p.toSubgraph.neighborSet u).ncard ≤ (M.neighborSet u).ncard :=
    Set.ncard_le_ncard (p.toSubgraph.neighborSet_subset u)
  have hdegree : (M.neighborSet u).ncard = M.degree u := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  have hone := hM u
  rw [htwo, hdegree] at hle
  omega

/-- Graph-level matchings are exactly graphs of maximum degree at most one. -/
theorem iff_degree_le_one : MatchingGraph M ↔ ∀ v, M.degree v ≤ 1 := by
  exact ⟨fun h ↦ h.2, of_degree_le_one⟩

/-- Every graph-level matching is a linear forest. -/
theorem linearForest (hM : MatchingGraph M) : LinearForest M := by
  exact ⟨hM.1, fun v ↦ (hM.2 v).trans (by omega)⟩

/-- The union of two graph-level matchings has maximum degree at most two. -/
theorem degree_sup_le_two (hM₁ : MatchingGraph M₁) (hM₂ : MatchingGraph M₂) (v : V) :
    (M₁ ⊔ M₂).degree v ≤ 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_sup]
  calc
    (M₁.neighborFinset v ∪ M₂.neighborFinset v).card
        ≤ (M₁.neighborFinset v).card + (M₂.neighborFinset v).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add (hM₁.2 v) (hM₂.2 v)
    _ = 2 := rfl

/-- The union of two matchings has a cycle-breaking spanning linear forest.

The retained forest has exactly the same reachability relation as the union.  Thus on each cyclic
component the construction deletes enough edges to open the cycle, while it does not split any
component.  For a maximum-degree-two graph this is precisely the graph-theoretic operation of
removing one edge from every cyclic component. -/
theorem exists_spanning_linearForest (hM₁ : MatchingGraph M₁) (hM₂ : MatchingGraph M₂) :
    ∃ F : SimpleGraph V,
      F ≤ M₁ ⊔ M₂ ∧ LinearForest F ∧ F.Reachable = (M₁ ⊔ M₂).Reachable := by
  obtain ⟨F, hFU, hFac, hreach⟩ :=
    (M₁ ⊔ M₂).exists_isAcyclic_reachable_eq_le
  refine ⟨F, hFU, ⟨hFac, ?_⟩, hreach⟩
  intro v
  exact (F.degree_le_of_le hFU).trans (degree_sup_le_two hM₁ hM₂ v)

/-- Edge-set form of `exists_spanning_linearForest`: all cycles can be opened by deleting a set
of edges without changing connected components. -/
theorem exists_cycleBreakingSet (hM₁ : MatchingGraph M₁) (hM₂ : MatchingGraph M₂) :
    ∃ D : Set (Sym2 V),
      D ⊆ (M₁ ⊔ M₂).edgeSet ∧
      LinearForest ((M₁ ⊔ M₂).deleteEdges D) ∧
      ((M₁ ⊔ M₂).deleteEdges D).Reachable = (M₁ ⊔ M₂).Reachable := by
  obtain ⟨F, hFU, hlin, hreach⟩ := exists_spanning_linearForest hM₁ hM₂
  refine ⟨(M₁ ⊔ M₂).edgeSet \ F.edgeSet, Set.sdiff_subset, ?_, ?_⟩
  · simpa only [SimpleGraph.deleteEdges_sdiff_eq_of_le hFU] using hlin
  · simpa only [SimpleGraph.deleteEdges_sdiff_eq_of_le hFU] using hreach

/-- The cycle-breaking set can be chosen to meet every cycle while retaining all connected
components.  In the maximum-degree-two union of two matchings, this is the formal cycle-opening
property used when one edge is removed from every cyclic component. -/
theorem exists_cycleTransversal (hM₁ : MatchingGraph M₁) (hM₂ : MatchingGraph M₂) :
    ∃ D : Set (Sym2 V),
      D ⊆ (M₁ ⊔ M₂).edgeSet ∧
      CycleTransversal (M₁ ⊔ M₂) D ∧
      LinearForest ((M₁ ⊔ M₂).deleteEdges D) ∧
      ((M₁ ⊔ M₂).deleteEdges D).Reachable = (M₁ ⊔ M₂).Reachable := by
  obtain ⟨D, hDsub, hlin, hreach⟩ := exists_cycleBreakingSet hM₁ hM₂
  exact ⟨D, hDsub, CycleTransversal.of_isAcyclic_deleteEdges hlin.1, hlin, hreach⟩

end MatchingGraph

/-- `G[X]` contains a linear forest with at least `r` edges.

The witness is a spanning subgraph of `G`; the support condition ensures that all its edges have
both endpoints in `X`. -/
def ContainsLinearForestWith (G : SimpleGraph V) (X : Finset V) (r : ℕ) : Prop :=
  ∃ F : SimpleGraph V,
    F ≤ G ∧ LinearForest F ∧ F.support ⊆ (X : Set V) ∧ r ≤ F.edgeFinset.card

namespace ContainsLinearForestWith

variable {G G' : SimpleGraph V} {X Y : Finset V} {r s : ℕ}

/-- A witness supported in `X` is also supported in any larger vertex set. -/
theorem mono_vertexSet (h : ContainsLinearForestWith G X r) (hXY : X ⊆ Y) :
    ContainsLinearForestWith G Y r := by
  obtain ⟨F, hFG, hlin, hsupp, hcard⟩ := h
  exact ⟨F, hFG, hlin, hsupp.trans (by simpa using hXY), hcard⟩

/-- Lowering the requested edge count preserves the property. -/
theorem mono_requirement (h : ContainsLinearForestWith G X r) (hsr : s ≤ r) :
    ContainsLinearForestWith G X s := by
  obtain ⟨F, hFG, hlin, hsupp, hcard⟩ := h
  exact ⟨F, hFG, hlin, hsupp, hsr.trans hcard⟩

/-- Enlarging the ambient graph preserves the property. -/
theorem mono_graph (h : ContainsLinearForestWith G X r) (hGG' : G ≤ G') :
    ContainsLinearForestWith G' X r := by
  obtain ⟨F, hFG, hlin, hsupp, hcard⟩ := h
  exact ⟨F, hFG.trans hGG', hlin, hsupp, hcard⟩

/-- The empty forest witnesses the zero-edge requirement. -/
@[simp]
theorem zero (G : SimpleGraph V) (X : Finset V) : ContainsLinearForestWith G X 0 := by
  refine ⟨⊥, bot_le, LinearForest.bot, ?_, by simp⟩
  simp

/-- Replace a lower-bound witness by one with exactly the requested number of edges. -/
theorem exists_exact (h : ContainsLinearForestWith G X r) :
    ∃ F : SimpleGraph V,
      F ≤ G ∧ LinearForest F ∧ F.support ⊆ (X : Set V) ∧ F.edgeFinset.card = r := by
  obtain ⟨F, hFG, hlin, hsupp, hcard⟩ := h
  obtain ⟨H, hHF, hHlin, hHcard⟩ := hlin.exists_subforest_card_eq hcard
  exact ⟨H, hHF.trans hFG, hHlin,
    (SimpleGraph.support_mono hHF).trans hsupp, hHcard⟩

/-- An exact witness is a lower-bound witness. -/
theorem of_exact {F : SimpleGraph V} (hFG : F ≤ G) (hlin : LinearForest F)
    (hsupp : F.support ⊆ (X : Set V)) (hcard : F.edgeFinset.card = r) :
    ContainsLinearForestWith G X r :=
  ⟨F, hFG, hlin, hsupp, hcard.ge⟩

end ContainsLinearForestWith

end Erdos622
