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
import ErdosProblems.Erdos622.LinearArboricity
import ErdosProblems.Erdos622.PippengerSchedule
import ErdosProblems.Erdos622.PetersenFactor
import ErdosProblems.Erdos622.AlonOriginal
import ErdosProblems.Erdos622.RegularCompletion
import ErdosProblems.Erdos76.HypergraphGreedyColoring
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# The deterministic assembly in Alon's high-girth argument

Alon's proof for an even regular graph first partitions the edge set into
two-factors.  A local-lemma transversal then supplies a matching meeting every
cycle in every factor.  Removing this matching opens every cycle, and the
removed edges themselves form one further linear forest.

This file proves the last assertion in its exact edge-partition form.  The
input is not an asymptotic principle: it is a concrete decomposition `d` and a
concrete subgraph `M`.  The theorem constructs an honest edge-coloring with
one additional color and proves that all its color graphs are linear forests.

Primary source: N. Alon, *The linear arboricity of graphs*, Israel J. Math.
62 (1988), 311--325, proof of Theorem 2.1.
-/

open scoped SimpleGraph

namespace Erdos622
namespace HighGirthLinear

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open LinearArboricity

variable {V : Type u} [Fintype V]

/-! ## Passing from a factor family to an edge partition -/

/-- A pairwise edge-disjoint family covering `G` canonically determines an
edge partition whose color graphs are exactly the members of the family. -/
theorem exists_edgePartition_colorGraph_eq
    {G : SimpleGraph V} {k : ℕ} (F : Fin k → SimpleGraph V)
    (hdisjoint : Pairwise fun i j ↦ Disjoint (F i) (F j))
    (hcover : (⨆ i, F i) = G) :
    ∃ c : EdgePartition G k, ∀ i, colorGraph c i = F i := by
  have hexists (e : G.edgeSet) : ∃ i, e.1 ∈ (F i).edgeSet := by
    have he : e.1 ∈ (⨆ i, F i).edgeSet := by
      rw [hcover]
      exact e.2
    rw [SimpleGraph.edgeSet_iSup] at he
    simpa only [Set.mem_iUnion] using he
  let c : EdgePartition G k := fun e ↦ Classical.choose (hexists e)
  have hc_mem (e : G.edgeSet) : e.1 ∈ (F (c e)).edgeSet :=
    Classical.choose_spec (hexists e)
  refine ⟨c, fun i ↦ ?_⟩
  apply SimpleGraph.edgeSet_inj.mp
  ext e
  rw [mem_colorGraph_edgeSet_iff]
  constructor
  · rintro ⟨heG, hci⟩
    simpa [hci] using hc_mem ⟨e, heG⟩
  · intro hei
    have heG : e ∈ G.edgeSet := by
      rw [← hcover, SimpleGraph.edgeSet_iSup]
      exact Set.mem_iUnion.2 ⟨i, hei⟩
    refine ⟨heG, ?_⟩
    by_contra hne
    have hd : Disjoint (F (c ⟨e, heG⟩)) (F i) := hdisjoint hne
    rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left] at hd
    exact hd (hc_mem ⟨e, heG⟩) hei

/-- Completing to an even regular graph, applying Petersen factorization,
and restricting back gives an edge partition into maximum-degree-two
subgraphs.  The completion itself need not preserve girth; all later cycle
arguments take place after this restriction. -/
theorem exists_degreeTwo_edgePartition_of_maxDegree
    (G : SimpleGraph V) (k : ℕ)
    (hdegree : ∀ v, G.degree v ≤ 2 * k) :
    ∃ c : EdgePartition G k,
      ∀ i v, (colorGraph c i).degree v ≤ 2 := by
  let C := GraphRegularCompletion.completion G (2 * k) hdegree
  let f : G ↪g C :=
    GraphRegularCompletion.originalGraphEmbedding G (2 * k) hdegree
  let _ : DecidableRel C.Adj := Classical.decRel _
  have hreg : C.IsRegularOfDegree (2 * k) := by
    exact GraphRegularCompletion.isRegularOfDegree_completion G (2 * k) hdegree
  obtain ⟨T⟩ := PetersenFactor.exists_twoFactorization C k hreg
  obtain ⟨cC, hcC⟩ :=
    exists_edgePartition_colorGraph_eq T.factor T.disjoint T.iSup_eq
  let c : EdgePartition G k := GraphRegularCompletion.pullbackColor f cC
  refine ⟨c, ?_⟩
  intro i v
  have hcolor : colorGraph c i = (T.factor i).comap f := by
    rw [show c = GraphRegularCompletion.pullbackColor f cC by rfl,
      GraphRegularCompletion.colorGraph_pullback, hcC]
  rw [hcolor]
  let e : (T.factor i).comap f ↪g T.factor i :=
    SimpleGraph.Embedding.comap f.toEmbedding (T.factor i)
  exact (e.toCopy.degree_le v).trans_eq (T.regular i (f v))

/-! ## Flattening fixed-size decompositions of color fibers -/

/-- Regard an edge as an edge of its own outer color graph. -/
def toOwnColorEdge {G : SimpleGraph V} {s : ℕ}
    (c : EdgePartition G s) (e : G.edgeSet) :
    (colorGraph c (c e)).edgeSet :=
  ⟨e.1, (mem_colorGraph_edgeSet_iff c (c e) e.1).mpr ⟨e.2, rfl⟩⟩

/-- Combine an outer color with an inner color on each outer fiber. -/
def flattenColor {G : SimpleGraph V} {s t : ℕ}
    (outer : EdgePartition G s)
    (inner : ∀ j, EdgePartition (colorGraph outer j) t) :
    EdgePartition G (s * t) := fun e ↦
  finProdFinEquiv (outer e, inner (outer e) (toOwnColorEdge outer e))

/-- A flattened color graph is exactly the corresponding inner color graph. -/
lemma colorGraph_flattenColor {G : SimpleGraph V} {s t : ℕ}
    (outer : EdgePartition G s)
    (inner : ∀ j, EdgePartition (colorGraph outer j) t)
    (j : Fin s) (l : Fin t) :
    colorGraph (flattenColor outer inner) (finProdFinEquiv (j, l)) =
      colorGraph (inner j) l := by
  ext v w
  rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeSet,
    mem_colorGraph_edgeSet_iff, mem_colorGraph_edgeSet_iff]
  constructor
  · rintro ⟨hG, hc⟩
    have hp :
        (outer ⟨s(v, w), hG⟩,
          inner (outer ⟨s(v, w), hG⟩)
            (toOwnColorEdge outer ⟨s(v, w), hG⟩)) = (j, l) :=
      finProdFinEquiv.injective hc
    have hj : outer ⟨s(v, w), hG⟩ = j := congrArg Prod.fst hp
    have houter : s(v, w) ∈ (colorGraph outer j).edgeSet :=
      (mem_colorGraph_edgeSet_iff outer j s(v, w)).mpr ⟨hG, hj⟩
    refine ⟨houter, ?_⟩
    have hl := congrArg Prod.snd hp
    subst j
    simpa [toOwnColorEdge] using hl
  · rintro ⟨houter, hl⟩
    rw [mem_colorGraph_edgeSet_iff] at houter
    obtain ⟨hG, hj⟩ := houter
    refine ⟨hG, ?_⟩
    change finProdFinEquiv
      (outer ⟨s(v, w), hG⟩,
        inner (outer ⟨s(v, w), hG⟩)
          (toOwnColorEdge outer ⟨s(v, w), hG⟩)) = finProdFinEquiv (j, l)
    apply congrArg finProdFinEquiv
    apply Prod.ext
    · exact hj
    · subst j
      simpa [toOwnColorEdge] using hl

/-- If every outer fiber has a `t`-color decomposition, their flattened
colors give an `s*t`-color decomposition of the whole graph. -/
def flattenDecompositions {G : SimpleGraph V} {s t : ℕ}
    (outer : EdgePartition G s)
    (inner : ∀ j, Decomposition (colorGraph outer j) t) :
    Decomposition G (s * t) where
  color := flattenColor outer (fun j ↦ (inner j).color)
  linear i := by
    let p := finProdFinEquiv.symm i
    rw [show i = finProdFinEquiv (p.1, p.2) by
      exact (finProdFinEquiv.apply_symm_apply i).symm]
    rw [colorGraph_flattenColor]
    exact (inner p.1).linear p.2

/-! ## Cycle blocks of maximum-degree-two factor families -/

/-- The edges of a walk, viewed as edges of a containing graph. -/
def cycleEdgeBlock (G : SimpleGraph V) {H : SimpleGraph V} {v : V}
    (p : H.Walk v v) : Finset G.edgeSet :=
  Finset.univ.filter fun e : G.edgeSet => e.1 ∈ p.edges

@[simp] lemma mem_cycleEdgeBlock (G : SimpleGraph V) {H : SimpleGraph V} {v : V}
    (p : H.Walk v v) (e : G.edgeSet) :
    e ∈ cycleEdgeBlock G p ↔ e.1 ∈ p.edges := by
  simp [cycleEdgeBlock]

lemma map_cycleEdgeBlock {G H : SimpleGraph V} (hHG : H ≤ G) {v : V}
    (p : H.Walk v v) :
    (cycleEdgeBlock G p).map ⟨Subtype.val, Subtype.val_injective⟩ =
      p.edges.toFinset := by
  ext e
  constructor
  · intro he
    obtain ⟨eG, heG, rfl⟩ := Finset.mem_map.mp he
    exact Multiset.mem_toFinset.mpr ((mem_cycleEdgeBlock G p eG).mp heG)
  · intro he
    have hep : e ∈ p.edges := Multiset.mem_toFinset.mp he
    have heH : e ∈ H.edgeSet := p.edges_subset_edgeSet hep
    let eG : G.edgeSet := ⟨e, SimpleGraph.edgeSet_mono hHG heH⟩
    exact Finset.mem_map.mpr ⟨eG, (mem_cycleEdgeBlock G p eG).mpr hep, rfl⟩

lemma card_cycleEdgeBlock {G H : SimpleGraph V} (hHG : H ≤ G) {v : V}
    {p : H.Walk v v} (hp : p.IsCycle) :
    (cycleEdgeBlock G p).card = p.length := by
  calc
    (cycleEdgeBlock G p).card =
        ((cycleEdgeBlock G p).map
          ⟨Subtype.val, Subtype.val_injective⟩).card :=
      (Finset.card_map _).symm
    _ = p.edges.toFinset.card := congrArg Finset.card (map_cycleEdgeBlock hHG p)
    _ = p.edges.length := List.toFinset_card_of_nodup hp.edges_nodup
    _ = p.length := p.length_edges

/-- On a cycle in a graph of maximum degree two, the cycle subgraph contains
every ambient edge incident to one of its vertices. -/
lemma cycle_adj_toSubgraph_iff_of_degree_le_two {H : SimpleGraph V}
    (hdegree : ∀ x, H.degree x ≤ 2) {v x : V} {p : H.Walk v v}
    (hp : p.IsCycle) (hx : x ∈ p.toSubgraph.verts) (y : V) :
    p.toSubgraph.Adj x y ↔ H.Adj x y := by
  refine SimpleGraph.Subgraph.adj_iff_of_neighborSet_equiv
    (?_ : Nonempty (H.neighborSet x ≃ p.toSubgraph.neighborSet x)).some
    (Set.toFinite _)
  have hpcard : (p.toSubgraph.neighborSet x).ncard = 2 := by
    apply hp.ncard_neighborSet_toSubgraph_eq_two
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hx
  have hHcard : (H.neighborSet x).ncard ≤ 2 := by
    calc
      (H.neighborSet x).ncard = (H.neighborSet x).toFinset.card :=
        Set.ncard_eq_toFinset_card' _
      _ = H.degree x := by
        rw [← H.card_neighborFinset_eq_degree]
        rfl
      _ ≤ 2 := hdegree x
  have hsub : p.toSubgraph.neighborSet x ⊆ H.neighborSet x :=
    p.toSubgraph.neighborSet_subset x
  have htwo_le : 2 ≤ (H.neighborSet x).ncard := by
    rw [← hpcard]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcard : (H.neighborSet x).ncard = 2 := by omega
  rw [← Cardinal.eq, ← Set.cast_ncard (Set.toFinite _),
    ← Set.cast_ncard (Set.toFinite _), hcard, hpcard]

/-- A cycle in a finite graph of maximum degree two spans its whole connected component. -/
lemma cycle_verts_eq_connectedComponent {H : SimpleGraph V} {v : V}
    (hdegree : ∀ x, H.degree x ≤ 2) {p : H.Walk v v} (hp : p.IsCycle) :
    p.toSubgraph.verts = (H.connectedComponentMk v).supp := by
  obtain ⟨C, hC⟩ := p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp (by
    intro x hx y hxy
    exact (cycle_adj_toSubgraph_iff_of_degree_le_two hdegree hp hx y).mpr hxy)
  have hvp : v ∈ p.toSubgraph.verts := p.start_mem_verts_toSubgraph
  have hvC : H.connectedComponentMk v = C := by
    rw [hC] at hvp
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff C v).mp hvp
  simpa [hvC] using hC

/-- In a finite graph of maximum degree two, cycles in the same component
have the same edge finset. -/
lemma cycle_edges_toFinset_eq_of_component_eq {H : SimpleGraph V}
    (hdegree : ∀ x, H.degree x ≤ 2) {v w : V} {p : H.Walk v v} {q : H.Walk w w}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hcomp : H.connectedComponentMk v = H.connectedComponentMk w) :
    p.edges.toFinset = q.edges.toFinset := by
  have hpverts := cycle_verts_eq_connectedComponent hdegree hp
  have hqverts := cycle_verts_eq_connectedComponent hdegree hq
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      constructor
      · intro he
        have hep : s(x, y) ∈ p.edges := Multiset.mem_toFinset.mp he
        have hxy : H.Adj x y := p.adj_of_mem_edges hep
        have hxp : x ∈ p.toSubgraph.verts := by
          rw [SimpleGraph.Walk.mem_verts_toSubgraph]
          exact p.fst_mem_support_of_mem_edges hep
        have hxq : x ∈ q.toSubgraph.verts := by
          rw [hpverts, hcomp, ← hqverts] at hxp
          exact hxp
        have hqadj : q.toSubgraph.Adj x y :=
          (cycle_adj_toSubgraph_iff_of_degree_le_two hdegree hq hxq y).mpr hxy
        exact Multiset.mem_toFinset.mpr
          ((q.mem_edges_toSubgraph).mp (SimpleGraph.Subgraph.mem_edgeSet.mpr hqadj))
      · intro he
        have heq : s(x, y) ∈ q.edges := Multiset.mem_toFinset.mp he
        have hxy : H.Adj x y := q.adj_of_mem_edges heq
        have hxq : x ∈ q.toSubgraph.verts := by
          rw [SimpleGraph.Walk.mem_verts_toSubgraph]
          exact q.fst_mem_support_of_mem_edges heq
        have hxp : x ∈ p.toSubgraph.verts := by
          rw [hqverts, ← hcomp, ← hpverts] at hxq
          exact hxq
        have hpadj : p.toSubgraph.Adj x y :=
          (cycle_adj_toSubgraph_iff_of_degree_le_two hdegree hp hxp y).mpr hxy
        exact Multiset.mem_toFinset.mpr
          ((p.mem_edges_toSubgraph).mp (SimpleGraph.Subgraph.mem_edgeSet.mpr hpadj))

private lemma cycle_components_eq_of_common_edge {H : SimpleGraph V}
    (hdegree : ∀ x, H.degree x ≤ 2) {v w : V} {p : H.Walk v v} {q : H.Walk w w}
    (hp : p.IsCycle) (hq : q.IsCycle) {e : Sym2 V}
    (hep : e ∈ p.edges) (heq : e ∈ q.edges) :
    H.connectedComponentMk v = H.connectedComponentMk w := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxp : x ∈ p.toSubgraph.verts := by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact p.fst_mem_support_of_mem_edges hep
      have hxq : x ∈ q.toSubgraph.verts := by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact q.fst_mem_support_of_mem_edges heq
      rw [cycle_verts_eq_connectedComponent hdegree hp,
        SimpleGraph.ConnectedComponent.mem_supp_iff] at hxp
      rw [cycle_verts_eq_connectedComponent hdegree hq,
        SimpleGraph.ConnectedComponent.mem_supp_iff] at hxq
      exact hxp.symm.trans hxq

lemma cycleEdgeBlock_eq_of_not_disjoint {G H : SimpleGraph V}
    (hdegree : ∀ x, H.degree x ≤ 2) {v w : V} {p : H.Walk v v} {q : H.Walk w w}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hoverlap : ¬ Disjoint (cycleEdgeBlock G p) (cycleEdgeBlock G q)) :
    cycleEdgeBlock G p = cycleEdgeBlock G q := by
  obtain ⟨e, hep, heq⟩ := Finset.not_disjoint_iff.mp hoverlap
  have hep' : e.1 ∈ p.edges := (mem_cycleEdgeBlock G p e).mp hep
  have heq' : e.1 ∈ q.edges := (mem_cycleEdgeBlock G q e).mp heq
  have hcomp := cycle_components_eq_of_common_edge hdegree hp hq hep' heq'
  have hedges := cycle_edges_toFinset_eq_of_component_eq hdegree hp hq hcomp
  ext f
  rw [mem_cycleEdgeBlock, mem_cycleEdgeBlock]
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp hedges f.1

/-- The finite type of distinct cycle-edge blocks across all factors. -/
def CycleBlockIndex (G : SimpleGraph V) {k : ℕ}
    (F : Fin k → SimpleGraph V) :=
  {R : Finset G.edgeSet //
    ∃ (i : Fin k) (v : V) (p : (F i).Walk v v),
      p.IsCycle ∧ R = cycleEdgeBlock G p}

noncomputable instance CycleBlockIndex.instFintype (G : SimpleGraph V) {k : ℕ}
    (F : Fin k → SimpleGraph V) : Fintype (CycleBlockIndex G F) := by
  classical
  apply Fintype.subtype
    ((Finset.univ : Finset (Finset G.edgeSet)).filter fun R =>
      ∃ (i : Fin k) (v : V) (p : (F i).Walk v v),
        p.IsCycle ∧ R = cycleEdgeBlock G p)
  intro R
  simp [CycleBlockIndex]

def cycleBlocks (G : SimpleGraph V) {k : ℕ} (F : Fin k → SimpleGraph V) :
    CycleBlockIndex G F → Finset G.edgeSet := fun a => a.1

@[simp] lemma cycleBlocks_apply (G : SimpleGraph V) {k : ℕ}
    (F : Fin k → SimpleGraph V) (a : CycleBlockIndex G F) :
    cycleBlocks G F a = a.1 := rfl

theorem cycleBlocks_pairwise_disjoint {G : SimpleGraph V} {k : ℕ}
    {F : Fin k → SimpleGraph V}
    (hdegree : ∀ i x, (F i).degree x ≤ 2)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (F i).edgeSet (F j).edgeSet) :
    ∀ a b : CycleBlockIndex G F, a ≠ b →
      Disjoint (cycleBlocks G F a) (cycleBlocks G F b) := by
  intro a b hab
  obtain ⟨i, v, p, hp, ha⟩ := a.2
  obtain ⟨j, w, q, hq, hb⟩ := b.2
  by_cases hij : i = j
  · subst j
    by_contra hoverlap
    have hoverlap' : ¬ Disjoint (cycleEdgeBlock G p) (cycleEdgeBlock G q) := by
      simpa [cycleBlocks_apply, ha, hb] using hoverlap
    have heq := cycleEdgeBlock_eq_of_not_disjoint (hdegree i) hp hq hoverlap'
    exact hab (Subtype.ext (ha.trans (heq.trans hb.symm)))
  · rw [cycleBlocks_apply, cycleBlocks_apply, ha, hb,
      Finset.disjoint_left]
    intro e hep heq
    have hep' : e.1 ∈ p.edges := (mem_cycleEdgeBlock G p e).mp hep
    have heq' : e.1 ∈ q.edges := (mem_cycleEdgeBlock G q e).mp heq
    have heFi : e.1 ∈ (F i).edgeSet := p.edges_subset_edgeSet hep'
    have heFj : e.1 ∈ (F j).edgeSet := q.edges_subset_edgeSet heq'
    exact Set.disjoint_left.mp (hdisjoint i j hij) heFi heFj

theorem cycleBlocks_card_ge_girth {G : SimpleGraph V} {k : ℕ}
    {F : Fin k → SimpleGraph V} (hFG : ∀ i, F i ≤ G)
    (a : CycleBlockIndex G F) :
    G.girth ≤ (cycleBlocks G F a).card := by
  obtain ⟨i, v, p, hp, ha⟩ := a.2
  rw [cycleBlocks_apply, ha, card_cycleEdgeBlock (hFG i) hp]
  simpa using G.girth_le_length (hp.mapLe (hFG i))

theorem cycleBlocks_cover {G : SimpleGraph V} {k : ℕ}
    {F : Fin k → SimpleGraph V}
    (hcycles : ∀ i, (F i).IsCycles)
    (hcover : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (F i).edgeSet) :
    ∀ e : G.edgeSet, ∃ a : CycleBlockIndex G F, e ∈ cycleBlocks G F a := by
  intro e
  obtain ⟨i, hei⟩ := hcover e.1 e.2
  have hex : ∃ (u : V) (p : (F i).Walk u u), p.IsCycle ∧ e.1 ∈ p.edges := by
    induction h : e.1 using Sym2.inductionOn with
    | _ x y =>
        have hxy : (F i).Adj x y := (F i).mem_edgeSet.mp (h ▸ hei)
        obtain ⟨u, p, hp, hexy⟩ :=
          SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
            ⟨hxy, (hcycles i).reachable_deleteEdges hxy⟩
        exact ⟨u, p, hp, h.symm ▸ hexy⟩
  obtain ⟨u, p, hp, hep⟩ := hex
  let a : CycleBlockIndex G F :=
    ⟨cycleEdgeBlock G p, ⟨i, u, p, hp, rfl⟩⟩
  exact ⟨a, (mem_cycleEdgeBlock G p e).mpr hep⟩

theorem biUnion_cycleBlocks_eq_univ {G : SimpleGraph V} {k : ℕ}
    {F : Fin k → SimpleGraph V}
    (hcycles : ∀ i, (F i).IsCycles)
    (hcover : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (F i).edgeSet) :
    (Finset.univ.biUnion (cycleBlocks G F) : Finset G.edgeSet) = Finset.univ := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  exact cycleBlocks_cover hcycles hcover e

theorem cycleBlocks_card_ge {G : SimpleGraph V} {k g : ℕ}
    {F : Fin k → SimpleGraph V} (hFG : ∀ i, F i ≤ G)
    (hgirth : g ≤ G.girth) (a : CycleBlockIndex G F) :
    g ≤ (cycleBlocks G F a).card :=
  hgirth.trans (cycleBlocks_card_ge_girth hFG a)

/-- The underlying unoriented edges of a finset of subtype-valued edges. -/
def edgeValues (G : SimpleGraph V) (W : Finset G.edgeSet) : Set (Sym2 V) :=
  Subtype.val '' (W : Set G.edgeSet)

@[simp] lemma edge_mem_edgeValues (G : SimpleGraph V) (W : Finset G.edgeSet)
    (e : G.edgeSet) : e.1 ∈ edgeValues G W ↔ e ∈ W := by
  constructor
  · rintro ⟨f, hf, hfe⟩
    simpa [Subtype.ext hfe] using hf
  · intro he
    exact ⟨e, he, rfl⟩

/-- Hitting every distinct cycle block destroys all cycles in every factor. -/
theorem isAcyclic_deleteEdges_of_hits_cycleBlocks
    {G : SimpleGraph V} {k : ℕ} {F : Fin k → SimpleGraph V}
    (W : Finset G.edgeSet)
    (hhit : ∀ a : CycleBlockIndex G F,
      ¬ Disjoint W (cycleBlocks G F a)) :
    ∀ i, ((F i).deleteEdges (edgeValues G W)).IsAcyclic := by
  intro i v p hp
  let q : (F i).Walk v v := p.mapLe (SimpleGraph.deleteEdges_le _)
  have hq : q.IsCycle := hp.mapLe (SimpleGraph.deleteEdges_le _)
  let a : CycleBlockIndex G F :=
    ⟨cycleEdgeBlock G q, ⟨i, v, q, hq, rfl⟩⟩
  obtain ⟨e, heW, hea⟩ := Finset.not_disjoint_iff.mp (hhit a)
  have heq : e.1 ∈ q.edges :=
    (mem_cycleEdgeBlock G q e).mp (by simpa [a, cycleBlocks] using hea)
  have hep : e.1 ∈ p.edges := by
    simpa [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using heq
  have hedel : e.1 ∈ ((F i).deleteEdges (edgeValues G W)).edgeSet :=
    p.edges_subset_edgeSet hep
  rw [SimpleGraph.edgeSet_deleteEdges] at hedel
  exact hedel.2 ((edge_mem_edgeValues G W e).mpr heW)

/-- Choose one representative from each block. -/
def selectedCycleEdges {G : SimpleGraph V} {k : ℕ}
    {F : Fin k → SimpleGraph V}
    (pick : (a : CycleBlockIndex G F) → G.edgeSet)
    (hpick : ∀ a, pick a ∈ cycleBlocks G F a) : Finset G.edgeSet :=
  Finset.univ.image pick

theorem isAcyclic_deleteEdges_selectedCycleEdges
    {G : SimpleGraph V} {k : ℕ} {F : Fin k → SimpleGraph V}
    (pick : (a : CycleBlockIndex G F) → G.edgeSet)
    (hpick : ∀ a, pick a ∈ cycleBlocks G F a) :
    ∀ i, ((F i).deleteEdges
      (edgeValues G (selectedCycleEdges pick hpick))).IsAcyclic := by
  apply isAcyclic_deleteEdges_of_hits_cycleBlocks
  intro a
  rw [Finset.not_disjoint_iff]
  exact ⟨pick a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, hpick a⟩

lemma isCycles_of_degree_eq_two {H : SimpleGraph V}
    (htwo : ∀ v, H.degree v = 2) : H.IsCycles := by
  intro v _hv
  calc
    (H.neighborSet v).ncard = (H.neighborSet v).toFinset.card :=
      Set.ncard_eq_toFinset_card' _
    _ = H.degree v := by
      rw [← H.card_neighborFinset_eq_degree]
      rfl
    _ = 2 := htwo v

/-! ## The line-graph bound used by the transversal step -/

/-- The conflict graph of the rank-two hypergraph associated to `G` has
degree at most `2 * D` when `G` has maximum degree at most `D`.  Alon's paper
uses the sharper `2 * D - 2`; the coarser bound is exactly enough because the
cycle blocks have at least `50 * D = 25 * (2 * D)` edges. -/
theorem conflictGraph_degree_le_two_mul [DecidableEq V]
    (G : SimpleGraph V) (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D) (e : G.edgeSet) :
    ((PippengerSchedule.graphHypergraph G).conflictGraph).degree e ≤ 2 * D := by
  let H := PippengerSchedule.graphHypergraph G
  have hHdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D := by
    intro v _hv
    simpa [H, PippengerSchedule.graphHypergraph_edgeDegree] using hdegree v
  have hneighbor : H.conflictGraph.neighborFinset e =
      (Finset.univ : Finset G.edgeSet).filter (H.Conflicts e) := by
    ext f
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  rw [SimpleGraph.degree, hneighbor]
  exact H.conflictDegree_le_uniform_mul
    (PippengerSchedule.graphHypergraph_isUniform_two G) hHdegree e

/-- Disjoint large vertex blocks in a bounded-degree graph have an
independent set meeting every block.  This is the arbitrary-indexed block
form of Alon's Proposition 2.4, obtained from the published partition form
by inducing on the union of the blocks. -/
theorem exists_independent_set_hitting_disjoint_parts
    {X : Type u} {I : Type*} [Fintype X] [Fintype I]
    (L : SimpleGraph X) (parts : I → Finset X) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ x, L.degree x ≤ d)
    (hcard : ∀ i, 25 * d ≤ (parts i).card)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j)) :
    ∃ W : Finset X, L.IsIndepSet (W : Set X) ∧
      ∀ i, ¬ Disjoint W (parts i) := by
  classical
  let S : Set X := {x | ∃ i, x ∈ parts i}
  let label : S → I := fun x ↦ Classical.choose x.2
  have hlabel (x : S) : x.1 ∈ parts (label x) :=
    Classical.choose_spec x.2
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let part : S → Fin (Fintype.card I) := fun x ↦ e (label x)
  have hdegreeS : ∀ x : S, (L.induce S).degree x ≤ d := by
    intro x
    let f : L.induce S ↪g L := SimpleGraph.Embedding.induce S
    exact (f.toCopy.degree_le x).trans (hdegree (f x))
  have hfiber (i : I) :
      ((LinearArboricity.IndependentTransversal.partFiber part (e i)).map
        (Function.Embedding.subtype S)) = parts i := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      have hpart : part y = e i :=
        (LinearArboricity.IndependentTransversal.mem_partFiber part (e i) y).mp hy
      have hli : label y = i := by
        apply e.injective
        exact hpart
      change y.1 ∈ parts i
      simpa [hli] using hlabel y
    · intro hx
      let y : S := ⟨x, ⟨i, hx⟩⟩
      have hli : label y = i := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisjoint (label y) i hne)
          (hlabel y) hx
      apply Finset.mem_map.mpr
      refine ⟨y, ?_, rfl⟩
      apply (LinearArboricity.IndependentTransversal.mem_partFiber
        part (e i) y).mpr
      simp [part, hli]
  have hcardS : ∀ j, 25 * d ≤
      (LinearArboricity.IndependentTransversal.partFiber part j).card := by
    intro j
    let i : I := e.symm j
    have hj : e i = j := e.apply_symm_apply j
    rw [← hj]
    rw [← Finset.card_map (f := Function.Embedding.subtype S), hfiber]
    exact hcard i
  obtain ⟨W, hhit, hind⟩ :=
    LinearArboricity.IndependentTransversal.exists_independent_transversal
      hd (L.induce S) part hdegreeS hcardS
  let W' : Finset X := W.map (Function.Embedding.subtype S)
  refine ⟨W', ?_, ?_⟩
  · rw [L.isIndepSet_iff]
    intro x hx y hy hxy hL
    obtain ⟨x', hx'W, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'W, rfl⟩ := Finset.mem_map.mp hy
    exact hind x' hx'W y' hy'W hL
  · intro i
    rw [Finset.not_disjoint_iff]
    obtain ⟨x, hxW, hxpart⟩ := hhit (e i)
    refine ⟨x.1, Finset.mem_map.mpr ⟨x, hxW, rfl⟩, ?_⟩
    have hli : label x = i := by
      apply e.injective
      exact hxpart
    simpa [hli] using hlabel x

/-- An independent vertex set of the conflict graph is a hypergraph
matching. -/
theorem isMatching_of_conflictGraph_isIndepSet
    {E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : Erdos76.FiniteHypergraph V E) (W : Finset E)
    (hW : H.conflictGraph.IsIndepSet (W : Set E)) :
    H.IsMatching W := by
  intro e he f hf hef
  by_contra hdisj
  exact hW he hf hef ⟨hef, hdisj⟩

/-- Package an independent set in the edge-conflict graph as a spanning
matching subgraph of the original graph. -/
theorem exists_matchingSubgraph_of_conflictIndependent [DecidableEq V]
    (G : SimpleGraph V) (W : Finset G.edgeSet)
    (hW : (PippengerSchedule.graphHypergraph G).conflictGraph.IsIndepSet
      (W : Set G.edgeSet)) :
    ∃ M : SimpleGraph V,
      M ≤ G ∧ Erdos622.SimpleGraph.IsLinearForest M ∧
        M.edgeFinset.card = W.card := by
  have hmatch : (PippengerSchedule.graphHypergraph G).IsMatching W :=
    isMatching_of_conflictGraph_isIndepSet
      (PippengerSchedule.graphHypergraph G) W hW
  exact ⟨PippengerSchedule.matchingSubgraph G W,
    PippengerSchedule.matchingSubgraph_le G W,
    Erdos622.SimpleGraph.isLinearForest_of_degree_le_one
      (PippengerSchedule.matchingSubgraph_degree_le_one G W hmatch),
    PippengerSchedule.card_edgeFinset_matchingSubgraph G W⟩

/-- The matching subgraph has precisely the selected underlying edges. -/
lemma edgeSet_matchingSubgraph_eq_edgeValues (G : SimpleGraph V)
    (W : Finset G.edgeSet) :
    (PippengerSchedule.matchingSubgraph G W).edgeSet = edgeValues G W := by
  ext e
  rw [PippengerSchedule.matchingSubgraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨⟨heG, heW⟩, _⟩
    exact ⟨⟨e, heG⟩, heW, rfl⟩
  · rintro ⟨f, hfW, rfl⟩
    exact ⟨⟨f.2, hfW⟩, G.not_isDiag_of_mem_edgeSet f.2⟩

/-- Alon's cycle-breaking selection for an edge partition into
maximum-degree-two graphs.  The ambient maximum degree controls the conflict
graph, while the girth lower bound makes every cycle block large enough for
the independent-transversal theorem. -/
theorem exists_breaker_of_degreeTwo_partition
    (G : SimpleGraph V) {k D : ℕ} (c : EdgePartition G k)
    (hfactorDegree : ∀ i v, (colorGraph c i).degree v ≤ 2)
    (hdegree : ∀ v, G.degree v ≤ D) (hD : 0 < D)
    (hgirth : 50 * D ≤ G.girth) :
    ∃ M : SimpleGraph V,
      M ≤ G ∧ Erdos622.SimpleGraph.IsLinearForest M ∧
        ∀ i, ((colorGraph c i).deleteEdges M.edgeSet).IsAcyclic := by
  classical
  let F : Fin k → SimpleGraph V := fun i ↦ colorGraph c i
  let L := (PippengerSchedule.graphHypergraph G).conflictGraph
  have hLdegree : ∀ e, L.degree e ≤ 2 * D :=
    conflictGraph_degree_le_two_mul G D hdegree
  have hpartsCard : ∀ a : CycleBlockIndex G F,
      25 * (2 * D) ≤ (cycleBlocks G F a).card := by
    intro a
    have hFG : ∀ i, F i ≤ G := by
      intro i
      exact colorGraph_le c i
    exact (by omega : 25 * (2 * D) = 50 * D) ▸
      hgirth.trans (cycleBlocks_card_ge_girth hFG a)
  have hpartsDisjoint : ∀ a b : CycleBlockIndex G F, a ≠ b →
      Disjoint (cycleBlocks G F a) (cycleBlocks G F b) := by
    apply cycleBlocks_pairwise_disjoint
    · exact hfactorDegree
    · intro i j hij
      exact SimpleGraph.disjoint_edgeSet.mpr (colorGraph_disjoint c hij)
  obtain ⟨W, hWindep, hWhit⟩ :=
    exists_independent_set_hitting_disjoint_parts L (cycleBlocks G F)
      (2 * D) (by omega) hLdegree hpartsCard hpartsDisjoint
  let M := PippengerSchedule.matchingSubgraph G W
  have hmatch : (PippengerSchedule.graphHypergraph G).IsMatching W :=
    isMatching_of_conflictGraph_isIndepSet
      (PippengerSchedule.graphHypergraph G) W hWindep
  refine ⟨M, PippengerSchedule.matchingSubgraph_le G W,
    Erdos622.SimpleGraph.isLinearForest_of_degree_le_one
      (PippengerSchedule.matchingSubgraph_degree_le_one G W hmatch), ?_⟩
  have hMedge : M.edgeSet = edgeValues G W :=
    edgeSet_matchingSubgraph_eq_edgeValues G W
  rw [hMedge]
  exact isAcyclic_deleteEdges_of_hits_cycleBlocks W hWhit

/-- Add a breaker color directly to an arbitrary edge partition. -/
def withBreakerPartition {G M : SimpleGraph V} {k : ℕ}
    (c : EdgePartition G k) : EdgePartition G (k + 1) :=
  fun e ↦ if e.1 ∈ M.edgeSet then 0 else Fin.succ (c e)

/-- The breaker color is exactly the breaker graph. -/
theorem colorGraph_withBreakerPartition_zero {G M : SimpleGraph V} {k : ℕ}
    (c : EdgePartition G k) (hMG : M ≤ G) :
    colorGraph (withBreakerPartition (M := M) c) 0 = M := by
  ext v w
  rw [← SimpleGraph.mem_edgeSet, mem_colorGraph_edgeSet_iff]
  constructor
  · rintro ⟨hG, hc⟩
    have hM : s(v, w) ∈ M.edgeSet := by
      by_contra hnot
      simp [withBreakerPartition, hnot, Fin.succ_ne_zero] at hc
    exact M.mem_edgeSet.mp hM
  · intro hMAdj
    have hM : s(v, w) ∈ M.edgeSet := M.mem_edgeSet.mpr hMAdj
    refine ⟨G.mem_edgeSet.mpr (hMG hMAdj), ?_⟩
    simp [withBreakerPartition, hM]

/-- Every old color is shifted and has the breaker edges removed. -/
theorem colorGraph_withBreakerPartition_succ {G M : SimpleGraph V} {k : ℕ}
    (c : EdgePartition G k) (i : Fin k) :
    colorGraph (withBreakerPartition (M := M) c) (Fin.succ i) =
      (colorGraph c i).deleteEdges M.edgeSet := by
  ext v w
  rw [← SimpleGraph.mem_edgeSet, mem_colorGraph_edgeSet_iff,
    SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hG, hc⟩
    by_cases hM : s(v, w) ∈ M.edgeSet
    · simp only [withBreakerPartition, hM, if_true] at hc
      exact (Fin.succ_ne_zero i hc.symm).elim
    · refine ⟨?_, hM⟩
      rw [← SimpleGraph.mem_edgeSet, mem_colorGraph_edgeSet_iff]
      refine ⟨hG, ?_⟩
      simpa [withBreakerPartition, hM] using hc
  · rintro ⟨hcolor, hM⟩
    rw [← SimpleGraph.mem_edgeSet, mem_colorGraph_edgeSet_iff] at hcolor
    obtain ⟨hG, hc⟩ := hcolor
    refine ⟨hG, ?_⟩
    simpa [withBreakerPartition, hM] using hc

/-- Add one distinguished color for a cycle-breaking subgraph `M`.  An edge
of `M` receives color zero; every other edge retains its old color, shifted by
one. -/
def withBreakerColor {G M : SimpleGraph V} {k : ℕ}
    (d : Decomposition G k) : EdgePartition G (k + 1) :=
  fun e ↦ if e.1 ∈ M.edgeSet then 0 else Fin.succ (d.color e)

/-- The zero color of `withBreakerColor` is exactly the breaking subgraph. -/
theorem colorGraph_withBreakerColor_zero {G M : SimpleGraph V} {k : ℕ}
    (d : Decomposition G k) (hMG : M ≤ G) :
    colorGraph (withBreakerColor (M := M) d) 0 = M := by
  ext v w
  rw [← SimpleGraph.mem_edgeSet, mem_colorGraph_edgeSet_iff]
  constructor
  · rintro ⟨hG, hc⟩
    have hM : s(v, w) ∈ M.edgeSet := by
      by_contra hnot
      simp [withBreakerColor, hnot, Fin.succ_ne_zero] at hc
    exact M.mem_edgeSet.mp hM
  · intro hMAdj
    have hM : s(v, w) ∈ M.edgeSet := M.mem_edgeSet.mpr hMAdj
    refine ⟨G.mem_edgeSet.mpr (hMG hMAdj), ?_⟩
    simp [withBreakerColor, hM]

/-- A shifted color of `withBreakerColor` is the corresponding old color
with all breaker edges deleted. -/
theorem colorGraph_withBreakerColor_succ {G M : SimpleGraph V} {k : ℕ}
    (d : Decomposition G k) (i : Fin k) :
    colorGraph (withBreakerColor (M := M) d) (Fin.succ i) =
      (colorGraph d.color i).deleteEdges M.edgeSet := by
  ext v w
  rw [← SimpleGraph.mem_edgeSet, mem_colorGraph_edgeSet_iff,
    SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hG, hc⟩
    by_cases hM : s(v, w) ∈ M.edgeSet
    · simp only [withBreakerColor, hM, if_true] at hc
      exact (Fin.succ_ne_zero i hc.symm).elim
    · refine ⟨?_, hM⟩
      rw [← SimpleGraph.mem_edgeSet, mem_colorGraph_edgeSet_iff]
      refine ⟨hG, ?_⟩
      simpa [withBreakerColor, hM] using hc
  · rintro ⟨hcolor, hM⟩
    rw [← SimpleGraph.mem_edgeSet, mem_colorGraph_edgeSet_iff] at hcolor
    obtain ⟨hG, hc⟩ := hcolor
    refine ⟨hG, ?_⟩
    simpa [withBreakerColor, hM] using hc

/-- Deleting edges from a graph of maximum degree two and destroying all
cycles produces a linear forest. -/
theorem isLinearForest_deleteEdges_of_isAcyclic
    {F : SimpleGraph V} (hdegree : ∀ v, F.degree v ≤ 2)
    (D : Set (Sym2 V)) (hacyclic : (F.deleteEdges D).IsAcyclic) :
    Erdos622.SimpleGraph.IsLinearForest (F.deleteEdges D) := by
  let : DecidableRel (F.deleteEdges D).Adj := Classical.decRel _
  refine ⟨hacyclic, ?_⟩
  intro v
  exact ((F.deleteEdges D).degree_le_of_le (SimpleGraph.deleteEdges_le D)).trans
    (hdegree v)

/-- Cycle breaking turns a maximum-degree-two edge partition into a linear
forest decomposition, without assuming that its original color graphs were
already acyclic. -/
def decompositionWithBreakerPartition {G M : SimpleGraph V} {k : ℕ}
    (c : EdgePartition G k) (hMG : M ≤ G)
    (hMlinear : Erdos622.SimpleGraph.IsLinearForest M)
    (hdegree : ∀ i v, (colorGraph c i).degree v ≤ 2)
    (hbreak : ∀ i, ((colorGraph c i).deleteEdges M.edgeSet).IsAcyclic) :
    Decomposition G (k + 1) where
  color := withBreakerPartition (M := M) c
  linear i := Fin.cases
    (by
      rw [colorGraph_withBreakerPartition_zero c hMG]
      exact hMlinear)
    (fun j ↦ by
      rw [colorGraph_withBreakerPartition_succ c j]
      exact isLinearForest_deleteEdges_of_isAcyclic (hdegree j) M.edgeSet
        (hbreak j)) i

/-- The direct high-girth conclusion for a supplied degree-two factor
partition. -/
theorem exists_decomposition_succ_of_degreeTwo_partition
    (G : SimpleGraph V) {k D : ℕ} (c : EdgePartition G k)
    (hfactorDegree : ∀ i v, (colorGraph c i).degree v ≤ 2)
    (hdegree : ∀ v, G.degree v ≤ D) (hD : 0 < D)
    (hgirth : 50 * D ≤ G.girth) :
    Nonempty (Decomposition G (k + 1)) := by
  obtain ⟨M, hMG, hMlinear, hbreak⟩ :=
    exists_breaker_of_degreeTwo_partition G c hfactorDegree hdegree hD hgirth
  exact ⟨decompositionWithBreakerPartition c hMG hMlinear hfactorDegree hbreak⟩

/-- Alon's Theorem 2.1/Corollary 2.6 in maximum-degree form: completion and
Petersen factorization cost `k` degree-two colors, and one independent
transversal color breaks all their cycles. -/
theorem exists_highGirth_decomposition_of_maxDegree
    (G : SimpleGraph V) (k : ℕ) (hk : 0 < k)
    (hdegree : ∀ v, G.degree v ≤ 2 * k)
    (hgirth : 100 * k ≤ G.girth) :
    Nonempty (Decomposition G (k + 1)) := by
  obtain ⟨c, hcdegree⟩ :=
    exists_degreeTwo_edgePartition_of_maxDegree G k hdegree
  apply exists_decomposition_succ_of_degreeTwo_partition
    G c hcdegree hdegree (by omega)
  convert hgirth using 1 <;> omega

/-! ## Factor grouping: Alon's Corollary 2.7 -/

/-- The factor in quotient block `j` and remainder position `r`, padded by
the empty graph after the original factor list ends. -/
def groupedFactor {k q : ℕ} (F : Fin k → SimpleGraph V)
    (j : Fin (k / q + 1)) (r : Fin q) : SimpleGraph V :=
  if h : j.1 * q + r.1 < k then F ⟨j.1 * q + r.1, h⟩ else ⊥

/-- The union of one quotient block of at most `q` factors. -/
def groupedHost {k q : ℕ} (F : Fin k → SimpleGraph V)
    (j : Fin (k / q + 1)) : SimpleGraph V :=
  ⨆ r, groupedFactor F j r

lemma groupedFactor_le {G : SimpleGraph V} {k q : ℕ}
    {F : Fin k → SimpleGraph V} (hFG : ∀ i, F i ≤ G)
    (j : Fin (k / q + 1)) (r : Fin q) : groupedFactor F j r ≤ G := by
  unfold groupedFactor
  split_ifs with h
  · exact hFG _
  · exact bot_le

lemma groupedFactor_degree_le {k q : ℕ}
    {F : Fin k → SimpleGraph V} (hdegree : ∀ i v, (F i).degree v ≤ 2)
    (j : Fin (k / q + 1)) (r : Fin q) (v : V) :
    (groupedFactor F j r).degree v ≤ 2 := by
  by_cases h : j.1 * q + r.1 < k
  · rw [groupedFactor, dif_pos h]
    exact hdegree _ v
  · rw [groupedFactor, dif_neg h]
    simp

lemma groupedFactor_disjoint {k q : ℕ}
    {F : Fin k → SimpleGraph V}
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (j : Fin (k / q + 1)) {r s : Fin q} (hrs : r ≠ s) :
    Disjoint (groupedFactor F j r) (groupedFactor F j s) := by
  unfold groupedFactor
  split_ifs with hr hs
  · apply hdisjoint
    intro heq
    apply hrs
    apply Fin.ext
    have hval := congrArg Fin.val heq
    exact Nat.add_left_cancel hval
  all_goals simp

lemma groupedHost_disjoint {k q : ℕ} (hq : 0 < q)
    {F : Fin k → SimpleGraph V}
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    {a b : Fin (k / q + 1)} (hab : a ≠ b) :
    Disjoint (groupedHost F a) (groupedHost F b) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e hea heb
  rw [groupedHost, SimpleGraph.edgeSet_iSup] at hea heb
  obtain ⟨r, her⟩ := Set.mem_iUnion.mp hea
  obtain ⟨s, hes⟩ := Set.mem_iUnion.mp heb
  unfold groupedFactor at her hes
  split at her <;> split at hes
  · rename_i hr hs
    have hidx : (⟨a.1 * q + r.1, hr⟩ : Fin k) ≠
        ⟨b.1 * q + s.1, hs⟩ := by
      intro heq
      apply hab
      apply Fin.ext
      have hv := congrArg Fin.val heq
      have hd := congrArg (fun n ↦ n / q) hv
      simpa [Nat.mul_comm, Nat.mul_add_div hq,
        Nat.div_eq_of_lt r.2, Nat.div_eq_of_lt s.2] using hd
    exact Set.disjoint_left.mp (SimpleGraph.disjoint_edgeSet.mpr
      (hdisjoint _ _ hidx)) her hes
  all_goals simp at her hes

/-- Quotient blocks cover all original color classes. -/
lemma iSup_groupedHost_eq {G : SimpleGraph V} {k q : ℕ} (hq : 0 < q)
    (c : EdgePartition G k) :
    (⨆ j, groupedHost (q := q) (fun i ↦ colorGraph c i) j) = G := by
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro r
    exact groupedFactor_le (fun i ↦ colorGraph_le c i) j r
  · intro v w hvw
    let e : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.mpr hvw⟩
    let i : Fin k := c e
    let j : Fin (k / q + 1) :=
      ⟨i.1 / q, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt i.2))⟩
    let r : Fin q := ⟨i.1 % q, Nat.mod_lt _ hq⟩
    have hval : j.1 * q + r.1 = i.1 := by
      simpa [j, r, Nat.mul_comm] using (Nat.div_add_mod i.1 q)
    have hvalid : j.1 * q + r.1 < k := hval ▸ i.2
    rw [← SimpleGraph.mem_edgeSet, SimpleGraph.edgeSet_iSup]
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [groupedHost, SimpleGraph.edgeSet_iSup]
    apply Set.mem_iUnion.mpr
    refine ⟨r, ?_⟩
    rw [groupedFactor, dif_pos hvalid, mem_colorGraph_edgeSet_iff]
    refine ⟨e.2, ?_⟩
    apply Fin.ext
    exact hval.symm

/-- A graph partitioned into `q` maximum-degree-two colors has maximum
degree at most `2q`. -/
lemma degree_le_two_mul_of_degreeTwo_partition {G : SimpleGraph V} {q : ℕ}
    (c : EdgePartition G q) (hdegree : ∀ i v, (colorGraph c i).degree v ≤ 2)
    (v : V) : G.degree v ≤ 2 * q := by
  have hG : G = ⨆ i, colorGraph c i := (iSup_colorGraph c).symm
  have hnc : G.degree v = (G.neighborSet v).ncard := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  rw [hnc, hG, SimpleGraph.neighborSet_iSup]
  calc
    (⋃ i, (colorGraph c i).neighborSet v).ncard ≤
        ∑ i, ((colorGraph c i).neighborSet v).ncard :=
      Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _i : Fin q, 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [← Set.fintypeCard_eq_ncard,
        SimpleGraph.card_neighborSet_eq_degree]
      exact hdegree i v
    _ = 2 * q := by simp [Nat.mul_comm]

/-- Cycle breaking from an explicit lower bound on every cycle block.  This
is the form used inside quotient blocks, where the lower bound comes from the
girth of the original graph rather than the completion. -/
theorem exists_decomposition_of_degreeTwo_blocks
    (H : SimpleGraph V) {q D : ℕ} (c : EdgePartition H q)
    (hfactorDegree : ∀ i v, (colorGraph c i).degree v ≤ 2)
    (hdegree : ∀ v, H.degree v ≤ D) (hD : 0 < D)
    (hpartsCard : ∀ a : CycleBlockIndex H (fun i ↦ colorGraph c i),
      25 * (2 * D) ≤
        (cycleBlocks H (fun i ↦ colorGraph c i) a).card) :
    Nonempty (Decomposition H (q + 1)) := by
  let F : Fin q → SimpleGraph V := fun i ↦ colorGraph c i
  let L := (PippengerSchedule.graphHypergraph H).conflictGraph
  have hLdegree : ∀ e, L.degree e ≤ 2 * D :=
    conflictGraph_degree_le_two_mul H D hdegree
  have hpartsDisjoint : ∀ a b : CycleBlockIndex H F, a ≠ b →
      Disjoint (cycleBlocks H F a) (cycleBlocks H F b) := by
    apply cycleBlocks_pairwise_disjoint
    · exact hfactorDegree
    · intro i j hij
      exact SimpleGraph.disjoint_edgeSet.mpr (colorGraph_disjoint c hij)
  obtain ⟨W, hWindep, hWhit⟩ :=
    exists_independent_set_hitting_disjoint_parts L (cycleBlocks H F)
      (2 * D) (by omega) hLdegree hpartsCard hpartsDisjoint
  let M := PippengerSchedule.matchingSubgraph H W
  have hmatch : (PippengerSchedule.graphHypergraph H).IsMatching W :=
    isMatching_of_conflictGraph_isIndepSet
      (PippengerSchedule.graphHypergraph H) W hWindep
  have hMG : M ≤ H := PippengerSchedule.matchingSubgraph_le H W
  have hMlinear : Erdos622.SimpleGraph.IsLinearForest M :=
    Erdos622.SimpleGraph.isLinearForest_of_degree_le_one
      (PippengerSchedule.matchingSubgraph_degree_le_one H W hmatch)
  have hMedge : M.edgeSet = edgeValues H W :=
    edgeSet_matchingSubgraph_eq_edgeValues H W
  have hbreak : ∀ i, ((colorGraph c i).deleteEdges M.edgeSet).IsAcyclic := by
    rw [hMedge]
    exact isAcyclic_deleteEdges_of_hits_cycleBlocks W hWhit
  exact ⟨decompositionWithBreakerPartition c hMG hMlinear hfactorDegree hbreak⟩

/-- Alon's grouped high-girth corollary.  The `k` Petersen factors are split
into quotient blocks of at most `q` factors.  Every block costs `q+1` linear
forests, including one independent cycle-breaker, and the extended-girth
hypothesis also covers the acyclic case. -/
theorem exists_grouped_decomposition
    (G : SimpleGraph V) {k q : ℕ} (_hk : 0 < k) (hq : 0 < q)
    (hdegree : ∀ v, G.degree v ≤ 2 * k)
    (hegirth : ((100 * q : ℕ) : ℕ∞) ≤ G.egirth) :
    Nonempty (Decomposition G ((k / q + 1) * (q + 1))) := by
  obtain ⟨c, hcdegree⟩ := exists_degreeTwo_edgePartition_of_maxDegree G k hdegree
  let F : Fin k → SimpleGraph V := fun i ↦ colorGraph c i
  have hFle : ∀ i, F i ≤ G := fun i ↦ colorGraph_le c i
  have hFdisjoint : ∀ i j, i ≠ j → Disjoint (F i) (F j) :=
    fun i j hij ↦ colorGraph_disjoint c hij
  have hlocalExists : ∀ j : Fin (k / q + 1),
      ∃ cLocal : EdgePartition (groupedHost (q := q) F j) q,
        ∀ r, colorGraph cLocal r = groupedFactor F j r := by
    intro j
    apply exists_edgePartition_colorGraph_eq
    · intro r s hrs
      exact groupedFactor_disjoint hFdisjoint j hrs
    · rfl
  choose cLocal hlocal using hlocalExists
  have hlocalDegree : ∀ j r v,
      (colorGraph (cLocal j) r).degree v ≤ 2 := by
    intro j r v
    rw [hlocal j r]
    exact groupedFactor_degree_le hcdegree j r v
  have hgroupDegree : ∀ j v,
      (groupedHost (q := q) F j).degree v ≤ 2 * q := by
    intro j v
    exact degree_le_two_mul_of_degreeTwo_partition (cLocal j) (hlocalDegree j) v
  have hgroupDecomp : ∀ j : Fin (k / q + 1),
      Nonempty (Decomposition (groupedHost (q := q) F j) (q + 1)) := by
    intro j
    apply exists_decomposition_of_degreeTwo_blocks
      (groupedHost (q := q) F j) (cLocal j) (hlocalDegree j)
      (hgroupDegree j) (by omega)
    intro a
    obtain ⟨r, v, p, hp, ha⟩ := a.2
    have hhostG : groupedHost (q := q) F j ≤ G := by
      apply iSup_le
      intro s
      exact groupedFactor_le hFle j s
    have hlocalG : colorGraph (cLocal j) r ≤ G :=
      (colorGraph_le (cLocal j) r).trans hhostG
    have hlenE : ((100 * q : ℕ) : ℕ∞) ≤ p.length := by
      simpa using hegirth.trans
        (SimpleGraph.egirth_le_length (hp.mapLe hlocalG))
    have hlen : 100 * q ≤ p.length := by exact_mod_cast hlenE
    rw [cycleBlocks_apply, ha, card_cycleEdgeBlock
      (colorGraph_le (cLocal j) r) hp]
    convert hlen using 1 <;> omega
  let decomp : ∀ j : Fin (k / q + 1),
      Decomposition (groupedHost (q := q) F j) (q + 1) :=
    fun j ↦ Classical.choice (hgroupDecomp j)
  obtain ⟨outer, houter⟩ := exists_edgePartition_colorGraph_eq
    (fun j ↦ groupedHost (q := q) F j)
    (fun _ _ hab ↦ groupedHost_disjoint hq hFdisjoint hab)
    (iSup_groupedHost_eq hq c)
  let inner : ∀ j, Decomposition (colorGraph outer j) (q + 1) := fun j ↦ by
    rw [houter j]
    exact decomp j
  exact ⟨flattenDecompositions outer inner⟩

/-- The precise deterministic content of the last paragraph of Alon's
high-girth proof.

The original color classes need only have maximum degree two; they are not
required to be acyclic.  A concrete linear-forest subgraph `M` is removed
from every class, and the hypothesis says that this deletion breaks every
cycle.  The resulting `k + 1` colors form a genuine linear-forest edge
decomposition of `G`. -/
def decompositionWithBreaker {G M : SimpleGraph V} {k : ℕ}
    (d : Decomposition G k) (hMG : M ≤ G)
    (hMlinear : Erdos622.SimpleGraph.IsLinearForest M)
    (hdegree : ∀ i v, (colorGraph d.color i).degree v ≤ 2)
    (hbreak : ∀ i, ((colorGraph d.color i).deleteEdges M.edgeSet).IsAcyclic) :
    Decomposition G (k + 1) where
  color := withBreakerColor (M := M) d
  linear i := Fin.cases
    (by
      rw [colorGraph_withBreakerColor_zero d hMG]
      exact hMlinear)
    (fun j ↦ by
      rw [colorGraph_withBreakerColor_succ d j]
      exact isLinearForest_deleteEdges_of_isAcyclic (hdegree j) M.edgeSet
        (hbreak j)) i

/-- Existential packaging of `decompositionWithBreaker`, convenient when the
matching/transversal stage supplies its witness existentially. -/
theorem exists_decomposition_succ_of_breaker {G : SimpleGraph V} {k : ℕ}
    (d : Decomposition G k)
    (hdegree : ∀ i v, (colorGraph d.color i).degree v ≤ 2)
    (hbreaker : ∃ M : SimpleGraph V,
      M ≤ G ∧ Erdos622.SimpleGraph.IsLinearForest M ∧
        ∀ i, ((colorGraph d.color i).deleteEdges M.edgeSet).IsAcyclic) :
    Nonempty (Decomposition G (k + 1)) := by
  obtain ⟨M, hMG, hMlinear, hbreak⟩ := hbreaker
  exact ⟨decompositionWithBreaker d hMG hMlinear hdegree hbreak⟩

/-- When each old color class is a two-factor, the maximum-degree hypothesis
of `exists_decomposition_succ_of_breaker` is automatic. -/
theorem exists_decomposition_succ_of_twoFactors {G : SimpleGraph V} {k : ℕ}
    (d : Decomposition G k)
    (htwo : ∀ i v, (colorGraph d.color i).degree v = 2)
    (hbreaker : ∃ M : SimpleGraph V,
      M ≤ G ∧ Erdos622.SimpleGraph.IsLinearForest M ∧
        ∀ i, ((colorGraph d.color i).deleteEdges M.edgeSet).IsAcyclic) :
    Nonempty (Decomposition G (k + 1)) := by
  apply exists_decomposition_succ_of_breaker d
  · intro i v
    exact (htwo i v).le
  · exact hbreaker

end

end HighGirthLinear
end Erdos622
