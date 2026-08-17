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
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
import ErdosProblems.Erdos622.LinearArboricity
import ErdosProblems.Erdos622.PippengerSchedule

/-!
# Regular completion of a finite simple graph

Alon's reduction from edge colouring to linear arboricity starts by replacing
a graph of maximum degree at most `D` by a finite `D`-regular supergraph.  This
file gives an explicit completion, without any parity assumption and without
parallel edges.

Take one copy of the original graph for every vertex of the `D`-dimensional
Boolean cube.  Above a vertex `v`, add the first `D - degree v` cube directions.
The two kinds of neighbours are disjoint: original edges change the `V`
coordinate and preserve the cube coordinate, while completion edges preserve
the `V` coordinate and flip one cube coordinate.  Consequently every lifted
vertex has exactly

`degree v + (D - degree v) = D`

neighbours.  The all-false layer is an induced copy of the original graph.
-/

open scoped SimpleGraph

namespace Erdos622
namespace GraphRegularCompletion

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V]

/-- Flip one coordinate of a Boolean cube. -/
def flip {D : ℕ} (x : Fin D → Bool) (i : Fin D) : Fin D → Bool :=
  Function.update x i (!x i)

@[simp] theorem flip_apply_same {D : ℕ} (x : Fin D → Bool) (i : Fin D) :
    flip x i i = !x i := by
  simp [flip]

@[simp] theorem flip_apply_of_ne {D : ℕ} (x : Fin D → Bool) {i j : Fin D}
    (hij : j ≠ i) : flip x i j = x j := by
  simp [flip, hij]

theorem flip_ne {D : ℕ} (x : Fin D → Bool) (i : Fin D) : flip x i ≠ x := by
  intro h
  have := congrFun h i
  simp at this

@[simp] theorem flip_flip {D : ℕ} (x : Fin D → Bool) (i : Fin D) :
    flip (flip x i) i = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [flip_apply_of_ne _ hji]

theorem flip_injective_index {D : ℕ} (x : Fin D → Bool) :
    Function.Injective (flip x) := by
  intro i j hij
  by_contra hne
  have hcoord := congrFun hij i
  have hji : i ≠ j := hne
  simp [flip_apply_of_ne _ hji] at hcoord

/-- The vertex type of the explicit completion. -/
abbrev Vertex (D : ℕ) (V : Type u) := (Fin D → Bool) × V

/-- The `D`-regular completion of `G`.

The proof `hdegree` is stored only to specify which cube directions are used;
different proofs give definitionally equal adjacency relations by proof
irrelevance. -/
def completion (G : SimpleGraph V) (D : ℕ) (_hdegree : ∀ v, G.degree v ≤ D) :
    SimpleGraph (Vertex D V) where
  Adj a b :=
    (a.1 = b.1 ∧ G.Adj a.2 b.2) ∨
      (a.2 = b.2 ∧ ∃ i : Fin (D - G.degree a.2),
        b.1 = flip a.1 ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le D (G.degree a.2))⟩)
  symm := ⟨by
    rintro ⟨x, v⟩ ⟨y, w⟩ (hG | hcube)
    · exact Or.inl ⟨hG.1.symm, G.adj_symm hG.2⟩
    · rcases hcube with ⟨rfl, i, rfl⟩
      refine Or.inr ⟨rfl, i, ?_⟩
      exact (flip_flip x ⟨i.1, Nat.lt_of_lt_of_le i.2
        (Nat.sub_le D (G.degree v))⟩).symm⟩
  loopless := ⟨by
    rintro ⟨x, v⟩ (hG | hcube)
    · exact G.loopless.irrefl v hG.2
    · rcases hcube with ⟨_, i, hi⟩
      exact flip_ne x _ hi.symm⟩

@[simp] theorem completion_adj {G : SimpleGraph V} {D : ℕ}
    (hdegree : ∀ v, G.degree v ≤ D) (a b : Vertex D V) :
    (completion G D hdegree).Adj a b ↔
      (a.1 = b.1 ∧ G.Adj a.2 b.2) ∨
        (a.2 = b.2 ∧ ∃ i : Fin (D - G.degree a.2),
          b.1 = flip a.1 ⟨i.1, Nat.lt_of_lt_of_le i.2
            (Nat.sub_le D (G.degree a.2))⟩) :=
  Iff.rfl

/-- The neighbours of a lifted vertex split into original neighbours and its
private deficiency directions. -/
def neighborEquiv (G : SimpleGraph V) (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (a : Vertex D V) :
    (completion G D hdegree).neighborSet a ≃
      G.neighborSet a.2 ⊕ Fin (D - G.degree a.2) where
  toFun b := by
    rcases b with ⟨⟨y, w⟩, hb⟩
    by_cases hG : G.Adj a.2 w
    · exact Sum.inl ⟨w, hG⟩
    · have hcube : a.2 = w ∧ ∃ i : Fin (D - G.degree a.2),
          y = flip a.1 ⟨i.1, Nat.lt_of_lt_of_le i.2
            (Nat.sub_le D (G.degree a.2))⟩ :=
        hb.resolve_left (fun h ↦ hG h.2)
      exact Sum.inr (Classical.choose hcube.2)
  invFun z := by
    rcases a with ⟨x, v⟩
    rcases z with w | i
    · exact ⟨⟨x, w.1⟩, Or.inl ⟨rfl, w.2⟩⟩
    · exact ⟨⟨flip x ⟨i.1, Nat.lt_of_lt_of_le i.2
        (Nat.sub_le D (G.degree v))⟩, v⟩, Or.inr ⟨rfl, i, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨y, w⟩, hb⟩
    by_cases hG : G.Adj a.2 w
    · simp only [hG, dite_true]
      have hsame : a.1 = y := (hb.resolve_right (by
        rintro ⟨hvw, _i, _hi⟩
        exact hG.ne hvw)).1
      apply Subtype.ext
      exact Prod.ext hsame rfl
    · have hcube : a.2 = w ∧ ∃ i : Fin (D - G.degree a.2),
          y = flip a.1 ⟨i.1, Nat.lt_of_lt_of_le i.2
            (Nat.sub_le D (G.degree a.2))⟩ :=
        hb.resolve_left (fun h ↦ hG h.2)
      simp only [hG, dite_false]
      apply Subtype.ext
      apply Prod.ext
      · exact (Classical.choose_spec hcube.2).symm
      · exact hcube.1
  right_inv := by
    rcases a with ⟨x, v⟩
    rintro (w | i)
    · have hw : G.Adj v w.1 := w.2
      simp only [hw, dite_true]
    · have hloop : ¬G.Adj v v := G.loopless.irrefl v
      simp only [hloop, dite_false, Sum.inr.injEq]
      have hflip := Classical.choose_spec (
        show ∃ j : Fin (D - G.degree v),
          flip x ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le D (G.degree v))⟩ =
            flip x ⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.sub_le D (G.degree v))⟩
        from ⟨i, rfl⟩)
      have hfull := flip_injective_index x hflip
      apply Fin.ext
      exact (congrArg Fin.val hfull).symm

/-- Every vertex of the completion has degree exactly `D`. -/
theorem degree_completion (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (a : Vertex D V) :
    (completion G D hdegree).degree a = D := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  calc
    Fintype.card ((completion G D hdegree).neighborSet a) =
        Fintype.card (G.neighborSet a.2 ⊕ Fin (D - G.degree a.2)) :=
      Fintype.card_congr (neighborEquiv G D hdegree a)
    _ = G.degree a.2 + (D - G.degree a.2) := by
      rw [Fintype.card_sum, Fintype.card_fin,
        SimpleGraph.card_neighborSet_eq_degree]
    _ = D := Nat.add_sub_of_le (hdegree a.2)

/-- The completion is `D`-regular. -/
theorem isRegularOfDegree_completion (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) :
    (completion G D hdegree).IsRegularOfDegree D := by
  intro a
  exact degree_completion G D hdegree a

section Pullback

universe w

variable {W : Type w} [Fintype W]
variable {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}

/-- Pull an edge partition back along an induced graph embedding. -/
def pullbackColor (f : G ↪g H) (c : LinearArboricity.EdgePartition H k) :
    LinearArboricity.EdgePartition G k :=
  fun e ↦ c (f.mapEdgeSet e)

/-- Pulling back a color graph is graph comapping. -/
theorem colorGraph_pullback (f : G ↪g H)
    (c : LinearArboricity.EdgePartition H k) (i : Fin k) :
    LinearArboricity.colorGraph (pullbackColor f c) i =
      (LinearArboricity.colorGraph c i).comap f := by
  ext v w
  change (LinearArboricity.colorGraph (pullbackColor f c) i).Adj v w ↔
    (LinearArboricity.colorGraph c i).Adj (f v) (f w)
  rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeSet]
  rw [LinearArboricity.mem_colorGraph_edgeSet_iff,
    LinearArboricity.mem_colorGraph_edgeSet_iff]
  constructor
  · rintro ⟨hG, hc⟩
    let hH : s(f v, f w) ∈ H.edgeSet := by
      simpa only [Sym2.map_mk] using f.map_mem_edgeSet_iff.mpr hG
    refine ⟨hH, ?_⟩
    have hedge : f.mapEdgeSet ⟨s(v, w), hG⟩ = ⟨s(f v, f w), hH⟩ := by
      apply Subtype.ext
      rfl
    change c (f.mapEdgeSet ⟨s(v, w), hG⟩) = i at hc
    rwa [hedge] at hc
  · rintro ⟨hH, hc⟩
    have hG : s(v, w) ∈ G.edgeSet := f.map_mem_edgeSet_iff.mp (by
      simpa only [Sym2.map_mk] using hH)
    refine ⟨hG, ?_⟩
    have hedge : f.mapEdgeSet ⟨s(v, w), hG⟩ = ⟨s(f v, f w), hH⟩ := by
      apply Subtype.ext
      rfl
    change c ⟨s(f v, f w), hH⟩ = i at hc
    change c (f.mapEdgeSet ⟨s(v, w), hG⟩) = i
    rwa [hedge]

/-- Linear forests are preserved by vertex injections. -/
theorem isLinearForest_comap (f : V ↪ W) {F : SimpleGraph W}
    (hF : Erdos622.SimpleGraph.IsLinearForest F) :
    Erdos622.SimpleGraph.IsLinearForest (F.comap f) := by
  refine ⟨hF.1.of_comap f, ?_⟩
  intro v
  let e : F.comap f ↪g F := SimpleGraph.Embedding.comap f F
  exact (e.toCopy.degree_le v).trans (hF.2 (f v))

/-- A linear-forest decomposition of a host restricts, with no extra colors,
to every induced embedded subgraph. -/
def pullbackDecomposition (f : G ↪g H)
    (d : LinearArboricity.Decomposition H k) :
    LinearArboricity.Decomposition G k where
  color := pullbackColor f d.color
  linear i := by
    rw [colorGraph_pullback]
    exact isLinearForest_comap f.toEmbedding (d.linear i)

end Pullback

section Pairing

variable {G : SimpleGraph V} {p : ℕ}

/-- Pair consecutive colors, expressed through the canonical equivalence
`Fin p × Fin 2 ≃ Fin (p * 2)`. -/
def pairColor (c : LinearArboricity.EdgePartition G (p * 2)) :
    LinearArboricity.EdgePartition G p :=
  fun e ↦ (finProdFinEquiv.symm (c e)).1

/-- The graph of one paired color is exactly the union of its two original
color graphs. -/
theorem colorGraph_pairColor (c : LinearArboricity.EdgePartition G (p * 2))
    (i : Fin p) :
    LinearArboricity.colorGraph (pairColor c) i =
      LinearArboricity.colorGraph c (finProdFinEquiv (i, 0)) ⊔
        LinearArboricity.colorGraph c (finProdFinEquiv (i, 1)) := by
  ext v w
  change (LinearArboricity.colorGraph (pairColor c) i).Adj v w ↔
    (LinearArboricity.colorGraph c (finProdFinEquiv (i, 0))).Adj v w ∨
      (LinearArboricity.colorGraph c (finProdFinEquiv (i, 1))).Adj v w
  rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeSet,
    ← SimpleGraph.mem_edgeSet]
  rw [LinearArboricity.mem_colorGraph_edgeSet_iff,
    LinearArboricity.mem_colorGraph_edgeSet_iff,
    LinearArboricity.mem_colorGraph_edgeSet_iff]
  constructor
  · rintro ⟨hG, hc⟩
    change (finProdFinEquiv.symm (c ⟨s(v, w), hG⟩)).1 = i at hc
    generalize hz : finProdFinEquiv.symm (c ⟨s(v, w), hG⟩) = z at hc
    rcases z with ⟨j, b⟩
    change j = i at hc
    subst j
    fin_cases b
    · left
      refine ⟨hG, ?_⟩
      exact (finProdFinEquiv.symm_apply_eq).mp hz
    · right
      refine ⟨hG, ?_⟩
      exact (finProdFinEquiv.symm_apply_eq).mp hz
  · rintro (⟨hG, hc⟩ | ⟨hG, hc⟩)
    · refine ⟨hG, ?_⟩
      change (finProdFinEquiv.symm (c ⟨s(v, w), hG⟩)).1 = i
      rw [hc, Equiv.symm_apply_apply]
    · refine ⟨hG, ?_⟩
      change (finProdFinEquiv.symm (c ⟨s(v, w), hG⟩)).1 = i
      rw [hc, Equiv.symm_apply_apply]

/-- Two matching color classes have a union whose neighbour sets have size at
most two.  The `ncard` formulation is independent of decidability-instance
choices for the union graph. -/
theorem ncard_neighborSet_pair_le_two
    (c : LinearArboricity.EdgePartition G (p * 2))
    (hmatching : ∀ j v, (LinearArboricity.colorGraph c j).degree v ≤ 1)
    (i : Fin p) (v : V) :
    ((LinearArboricity.colorGraph c (finProdFinEquiv (i, 0)) ⊔
      LinearArboricity.colorGraph c (finProdFinEquiv (i, 1))).neighborSet v).ncard ≤ 2 := by
  have hm0 : ((LinearArboricity.colorGraph c
      (finProdFinEquiv (i, 0))).neighborSet v).ncard ≤ 1 := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    exact hmatching _ v
  have hm1 : ((LinearArboricity.colorGraph c
      (finProdFinEquiv (i, 1))).neighborSet v).ncard ≤ 1 := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    exact hmatching _ v
  rw [SimpleGraph.neighborSet_sup]
  calc
    (((LinearArboricity.colorGraph c (finProdFinEquiv (i, 0))).neighborSet v) ∪
      ((LinearArboricity.colorGraph c
        (finProdFinEquiv (i, 1))).neighborSet v)).ncard ≤
        ((LinearArboricity.colorGraph c
          (finProdFinEquiv (i, 0))).neighborSet v).ncard +
          ((LinearArboricity.colorGraph c
            (finProdFinEquiv (i, 1))).neighborSet v).ncard :=
      Set.ncard_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add hm0 hm1
    _ = 2 := rfl

/-- Exact deterministic pairing step in Alon's reduction.  If the starting
edge colors are matchings and every bichromatic paired union is acyclic, the
number of linear-forest colors is halved. -/
def pairedDecomposition
    (c : LinearArboricity.EdgePartition G (p * 2))
    (hmatching : ∀ j v, (LinearArboricity.colorGraph c j).degree v ≤ 1)
    (hacyclic : ∀ i : Fin p,
      (LinearArboricity.colorGraph c (finProdFinEquiv (i, 0)) ⊔
        LinearArboricity.colorGraph c (finProdFinEquiv (i, 1))).IsAcyclic) :
    LinearArboricity.Decomposition G p where
  color := pairColor c
  linear i := by
    refine ⟨?_, ?_⟩
    · rw [colorGraph_pairColor]
      exact hacyclic i
    · intro v
      have hset := congrArg (fun F : SimpleGraph V ↦ F.neighborSet v)
        (colorGraph_pairColor c i)
      have hncard :
          ((LinearArboricity.colorGraph (pairColor c) i).neighborSet v).ncard ≤ 2 := by
        rw [hset]
        exact ncard_neighborSet_pair_le_two c hmatching i v
      have hcard :
          ((LinearArboricity.colorGraph (pairColor c) i).neighborSet v).ncard =
            (LinearArboricity.colorGraph (pairColor c) i).degree v := by
        rw [← Set.fintypeCard_eq_ncard,
          SimpleGraph.card_neighborSet_eq_degree]
      rw [← hcard]
      exact hncard

/-- After pairing colors, mark a set `R` of cycle-breaking edges for an
additional `r`-color decomposition.  Unmarked edges keep their paired color;
marked edges use `remainderColor`.  The two color ranges are disjoint by the
canonical inclusions into `Fin (p + r)`. -/
def cycleBrokenColor (c : LinearArboricity.EdgePartition G (p * 2))
    (R : Set (Sym2 V)) {r : ℕ} (remainderColor : G.edgeSet → Fin r) :
    LinearArboricity.EdgePartition G (p + r) :=
  fun e ↦ if e.1 ∈ R then Fin.natAdd p (remainderColor e)
    else Fin.castAdd r (pairColor c e)

/-- The old-color part of `cycleBrokenColor` is exactly the paired graph with
the marked cycle-breaking edges deleted. -/
theorem colorGraph_cycleBrokenColor_castAdd
    (c : LinearArboricity.EdgePartition G (p * 2))
    (R : Set (Sym2 V)) {r : ℕ} (remainderColor : G.edgeSet → Fin r)
    (i : Fin p) :
    LinearArboricity.colorGraph (cycleBrokenColor c R remainderColor)
        (Fin.castAdd r i) =
      (LinearArboricity.colorGraph (pairColor c) i).deleteEdges R := by
  ext v w
  rw [SimpleGraph.deleteEdges_adj, ← SimpleGraph.mem_edgeSet,
    ← SimpleGraph.mem_edgeSet]
  rw [LinearArboricity.mem_colorGraph_edgeSet_iff,
    LinearArboricity.mem_colorGraph_edgeSet_iff]
  constructor
  · rintro ⟨hG, hc⟩
    by_cases hR : s(v, w) ∈ R
    · simp only [cycleBrokenColor, hR, if_true] at hc
      have hval := congrArg Fin.val hc
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    · refine ⟨⟨hG, ?_⟩, hR⟩
      simp only [cycleBrokenColor, hR, if_false, Fin.castAdd_inj] at hc
      exact hc
  · rintro ⟨⟨hG, hc⟩, hR⟩
    refine ⟨hG, ?_⟩
    simp only [cycleBrokenColor, hR, if_false, Fin.castAdd_inj]
    exact hc

/-- Exact cycle-breaking assembly.  It isolates the probabilistic part of
Alon's argument: one must choose `R` so that every deleted paired class is a
linear forest and then color the sparse remainder with few additional linear
forests.  Once those two facts are available, this constructor covers every
original edge exactly once. -/
def cycleBrokenDecomposition
    (c : LinearArboricity.EdgePartition G (p * 2))
    (R : Set (Sym2 V)) {r : ℕ} (remainderColor : G.edgeSet → Fin r)
    (hpaired : ∀ i : Fin p,
      Erdos622.SimpleGraph.IsLinearForest
        ((LinearArboricity.colorGraph (pairColor c) i).deleteEdges R))
    (hremainder : ∀ j : Fin r,
      Erdos622.SimpleGraph.IsLinearForest
        (LinearArboricity.colorGraph (cycleBrokenColor c R remainderColor)
          (Fin.natAdd p j))) :
    LinearArboricity.Decomposition G (p + r) where
  color := cycleBrokenColor c R remainderColor
  linear q := by
    refine Fin.addCases (motive := fun q ↦
      Erdos622.SimpleGraph.IsLinearForest
        (LinearArboricity.colorGraph (cycleBrokenColor c R remainderColor) q))
      ?_ ?_ q
    · intro i
      rw [colorGraph_cycleBrokenColor_castAdd]
      exact hpaired i
    · exact hremainder

end Pairing

section GreedyRemainder

open Erdos76
open PippengerSchedule

variable {G : SimpleGraph V}

theorem natAdd_injective (p q : ℕ) :
    Function.Injective (Fin.natAdd p : Fin q → Fin (p + q)) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [Fin.val_natAdd] at hval
  omega

/-- A hypergraph edge color in the rank-two encoding has the same graph as
the corresponding `LinearArboricity` color fiber. -/
theorem colorGraph_eq_matchingSubgraph
    {q : ℕ} (c : (graphHypergraph G).EdgeColoring q) (i : Fin q) :
    LinearArboricity.colorGraph
        (fun e : G.edgeSet ↦ c e) i =
      matchingSubgraph G (c.colorClass i) := by
  ext v w
  rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeSet]
  rw [LinearArboricity.mem_colorGraph_edgeSet_iff]
  constructor
  · rintro ⟨hG, hc⟩
    rw [matchingSubgraph, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨hG, ?_⟩, G.not_isDiag_of_mem_edgeSet hG⟩
    exact c.mem_colorClass i ⟨s(v, w), hG⟩ |>.mpr hc
  · intro h
    rw [matchingSubgraph, SimpleGraph.edgeSet_fromEdgeSet] at h
    obtain ⟨⟨hG, hcolor⟩, _⟩ := h
    exact ⟨hG, c.mem_colorClass i ⟨s(v, w), hG⟩ |>.mp hcolor⟩

/-- Crude but unconditional low-degree remainder bound.  Every finite simple
graph of maximum degree at most `D` decomposes into `2D+1` matchings, hence
into `2D+1` linear forests.  This is the deterministic final step in Alon's
cycle-breaking reduction; if the marked-edge graph has degree `o(D)`, its
extra color count is `o(D)`. -/
theorem exists_greedyLinearForestDecomposition (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ D) :
    Nonempty (LinearArboricity.Decomposition G (2 * D + 1)) := by
  let H := graphHypergraph G
  have hunif : H.IsUniform 2 := graphHypergraph_isUniform_two G
  have hHdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D := by
    intro v _hv
    rw [graphHypergraph_edgeDegree]
    have hcard : (G.neighborSet v).ncard = G.degree v := by
      rw [← Set.fintypeCard_eq_ncard,
        SimpleGraph.card_neighborSet_eq_degree]
    rw [← hcard]
    exact hdegree v
  obtain ⟨c⟩ := H.exists_edgeColoring_uniform_degree hunif hHdegree
  refine ⟨{
    color := fun e ↦ c e
    linear := ?_
  }⟩
  intro i
  rw [colorGraph_eq_matchingSubgraph]
  have hlinear := matchingSubgraph_linearForest G (c.colorClass i)
    (c.colorClass_isMatching i)
  exact ⟨hlinear.1, hlinear.2⟩

/-- Regard an edge marked by `R` as an edge of the graph containing exactly
the marked edges of `G`. -/
def toMarkedEdge (G : SimpleGraph V) (R : Set (Sym2 V))
    (e : G.edgeSet) (heR : e.1 ∈ R) : (G.deleteEdges Rᶜ).edgeSet :=
  ⟨e.1, by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨e.2, by simpa⟩⟩

/-- Extend a coloring of the marked-edge graph to all original edge indices.
Values on unmarked edges are immaterial to `cycleBrokenColor`; a positive
color count supplies a harmless default. -/
def extendMarkedColor (G : SimpleGraph V) (R : Set (Sym2 V)) {q : ℕ}
    (hq : 0 < q)
    (c : LinearArboricity.EdgePartition (G.deleteEdges Rᶜ) q) :
    LinearArboricity.EdgePartition G q :=
  fun e ↦ if heR : e.1 ∈ R then c (toMarkedEdge G R e heR) else ⟨0, hq⟩

/-- In the extra-color range, the assembled coloring is exactly the coloring
of the marked-edge graph. -/
theorem colorGraph_cycleBrokenColor_natAdd
    {p q : ℕ} (base : LinearArboricity.EdgePartition G (p * 2))
    (R : Set (Sym2 V)) (hq : 0 < q)
    (c : LinearArboricity.EdgePartition (G.deleteEdges Rᶜ) q) (j : Fin q) :
    LinearArboricity.colorGraph
        (cycleBrokenColor base R (extendMarkedColor G R hq c))
        (Fin.natAdd p j) =
      LinearArboricity.colorGraph c j := by
  ext v w
  rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeSet]
  rw [LinearArboricity.mem_colorGraph_edgeSet_iff,
    LinearArboricity.mem_colorGraph_edgeSet_iff]
  constructor
  · rintro ⟨hG, hcolor⟩
    by_cases hR : s(v, w) ∈ R
    · let eG : G.edgeSet := ⟨s(v, w), hG⟩
      let eR : (G.deleteEdges Rᶜ).edgeSet := toMarkedEdge G R eG hR
      refine ⟨eR.2, ?_⟩
      rw [cycleBrokenColor, if_pos hR] at hcolor
      have hcolor' : extendMarkedColor G R hq c eG = j :=
        natAdd_injective p q hcolor
      rw [extendMarkedColor, dif_pos hR] at hcolor'
      have hedge : toMarkedEdge G R eG hR =
          ⟨s(v, w), eR.2⟩ := by
        apply Subtype.ext
        rfl
      rwa [hedge] at hcolor'
    · have hval := congrArg Fin.val hcolor
      simp only [cycleBrokenColor, hR, if_false, Fin.val_castAdd,
        Fin.val_natAdd] at hval
      omega
  · rintro ⟨hK, hcolor⟩
    have hdata : s(v, w) ∈ G.edgeSet ∧ s(v, w) ∉ Rᶜ := by
      rw [SimpleGraph.edgeSet_deleteEdges] at hK
      exact hK
    have hG : s(v, w) ∈ G.edgeSet := hdata.1
    have hR : s(v, w) ∈ R := by simpa using hdata.2
    refine ⟨hG, ?_⟩
    rw [cycleBrokenColor, if_pos hR]
    apply congrArg (Fin.natAdd p)
    rw [extendMarkedColor, dif_pos hR]
    have hedge : toMarkedEdge G R ⟨s(v, w), hG⟩ hR =
        ⟨s(v, w), hK⟩ := by
      apply Subtype.ext
      rfl
    rwa [hedge]

/-- Fully unconditional marked-edge completion of the pairing step.  Once
deleting `R` opens every paired color class, a maximum-degree-`D` bound on the
marked-edge graph yields a complete decomposition using
`p + (2D+1)` linear forests. -/
theorem exists_cycleBrokenDecomposition_of_markedDegree_le
    {p : ℕ} (base : LinearArboricity.EdgePartition G (p * 2))
    (R : Set (Sym2 V)) (D : ℕ)
    (hpaired : ∀ i : Fin p,
      Erdos622.SimpleGraph.IsLinearForest
        ((LinearArboricity.colorGraph (pairColor base) i).deleteEdges R))
    (hdegree : ∀ v, (G.deleteEdges Rᶜ).degree v ≤ D) :
    Nonempty (LinearArboricity.Decomposition G (p + (2 * D + 1))) := by
  have hdecomp : Nonempty (LinearArboricity.Decomposition
      (G.deleteEdges Rᶜ) (2 * D + 1)) :=
    exists_greedyLinearForestDecomposition (G.deleteEdges Rᶜ) D (by
      intro v
      have hcard : ((G.deleteEdges Rᶜ).neighborSet v).ncard =
          (G.deleteEdges Rᶜ).degree v := by
        rw [← Set.fintypeCard_eq_ncard,
          SimpleGraph.card_neighborSet_eq_degree]
      rw [hcard]
      exact hdegree v)
  obtain ⟨d⟩ := hdecomp
  have hq : 0 < 2 * D + 1 := Nat.succ_pos _
  let remainderColor : LinearArboricity.EdgePartition G (2 * D + 1) :=
    extendMarkedColor G R hq d.color
  refine ⟨cycleBrokenDecomposition base R remainderColor hpaired ?_⟩
  intro j
  rw [show remainderColor = extendMarkedColor G R hq d.color by rfl]
  rw [colorGraph_cycleBrokenColor_natAdd]
  exact d.linear j

/-- Averaging consequence in the form consumed by induced-edge estimates:
some resulting linear forest contains at least the average number of edges. -/
theorem exists_large_linearForest_of_markedDegree_le
    {p : ℕ} (base : LinearArboricity.EdgePartition G (p * 2))
    (R : Set (Sym2 V)) (D : ℕ)
    (hpaired : ∀ i : Fin p,
      Erdos622.SimpleGraph.IsLinearForest
        ((LinearArboricity.colorGraph (pairColor base) i).deleteEdges R))
    (hdegree : ∀ v, (G.deleteEdges Rᶜ).degree v ≤ D) :
    ∃ F : SimpleGraph V,
      F ≤ G ∧ Erdos622.SimpleGraph.IsLinearForest F ∧
      (Fintype.card G.edgeSet : ℝ) / (p + (2 * D + 1) : ℕ) ≤
        (Fintype.card F.edgeSet : ℝ) := by
  obtain ⟨d⟩ := exists_cycleBrokenDecomposition_of_markedDegree_le
    base R D hpaired hdegree
  exact d.exists_large_linearForest (by omega)

end GreedyRemainder

/-- The all-false layer embedding. -/
def originalEmbedding (D : ℕ) : V ↪ Vertex D V where
  toFun v := (fun _ ↦ false, v)
  inj' := by
    intro v w h
    exact congrArg Prod.snd h

/-- The all-false layer is an induced copy of the original graph. -/
@[simp] theorem completion_adj_originalEmbedding (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (v w : V) :
    (completion G D hdegree).Adj (originalEmbedding D v) (originalEmbedding D w) ↔
      G.Adj v w := by
  constructor
  · intro h
    rcases h with hG | hcube
    · exact hG.2
    · rcases hcube with ⟨hvw, i, hi⟩
      cases hvw
      change (fun _ : Fin D ↦ false) =
          flip (fun _ : Fin D ↦ false) ⟨i.1, Nat.lt_of_lt_of_le i.2
            (Nat.sub_le D (G.degree v))⟩ at hi
      exact ((flip_ne (fun _ : Fin D ↦ false) _) hi.symm).elim
  · intro hvw
    exact Or.inl ⟨rfl, hvw⟩

/-- The canonical embedding as a graph embedding. -/
def originalGraphEmbedding (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) :
    G ↪g completion G D hdegree where
  __ := originalEmbedding D
  map_rel_iff' := by
    intro v w
    exact completion_adj_originalEmbedding G D hdegree v w

/-- Any decomposition of the regular completion restricts to the original
graph without using extra colors. -/
def restrictCompletionDecomposition {k : ℕ} (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D)
    (d : LinearArboricity.Decomposition (completion G D hdegree) k) :
    LinearArboricity.Decomposition G k :=
  pullbackDecomposition (originalGraphEmbedding G D hdegree) d

end

end GraphRegularCompletion
end Erdos622
