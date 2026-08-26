/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Section6Dichotomy
import ErdosProblems.Erdos547b.PrunedReducedLargeEdges

/-!
# Deleting entire pairs between nonlarge clusters

Zhao's large-cluster quota is larger than the regularity density cutoff.
This file performs the separate cluster-pair deletion, rather than requiring
the cutoff to rule out nonlarge--nonlarge pairs by itself. Edges incident to
a large cluster are unchanged; every other ordinary pair becomes empty.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClusterPairPruning

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoPrunedReducedLargeEdges Erdos547b.ZhaoQuantitativeLargeClusters

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

/-- Keep the cleaned edges with at least one endpoint in a large cluster. -/
def pairPrunedGraph (P : ClusterAssignment V I) (H : SimpleGraph V)
    (L : Finset I) : SimpleGraph V :=
  pruneSmallEdges H (clusterUnion P L : Set V)

instance (P : ClusterAssignment V I) (H : SimpleGraph V)
    [DecidableRel H.Adj] (L : Finset I) :
    DecidableRel (pairPrunedGraph P H L).Adj :=
  inferInstanceAs (DecidableRel (pruneSmallEdges H (clusterUnion P L : Set V)).Adj)

theorem pairPrunedGraph_le (P : ClusterAssignment V I) (H : SimpleGraph V)
    (L : Finset I) : pairPrunedGraph P H L ≤ H :=
  pruneSmallEdges_le H _

theorem mem_clusterUnion_iff_of_assignment
    (P : ClusterAssignment V I) (L : Finset I) {u : V} {i : I}
    (hu : P u = some i) : u ∈ clusterUnion P L ↔ i ∈ L := by
  simp [mem_clusterUnion, hu]

/-- The decision to keep a pair depends only on its cluster indices. -/
theorem adj_on_clusters
    (P : ClusterAssignment V I) (H : SimpleGraph V) (L : Finset I)
    {u v : V} {i j : I} (hu : P u = some i) (hv : P v = some j) :
    (pairPrunedGraph P H L).Adj u v ↔ H.Adj u v ∧ (i ∈ L ∨ j ∈ L) := by
  change H.Adj u v ∧ (u ∈ clusterUnion P L ∨ v ∈ clusterUnion P L) ↔ _
  rw [mem_clusterUnion_iff_of_assignment P L hu,
    mem_clusterUnion_iff_of_assignment P L hv]

/-- In particular the pointwise degree of every large-cluster vertex is
unchanged by this additional deletion. -/
theorem degree_eq_of_large_cluster
    (P : ClusterAssignment V I) (H : SimpleGraph V) [DecidableRel H.Adj]
    (L : Finset I) {i : I} (hi : i ∈ L) {u : V} (hu : P u = some i) :
    (pairPrunedGraph P H L).degree u = H.degree u := by
  apply pruneSmallEdges_degree_eq_of_mem H (clusterUnion P L : Set V)
  exact (mem_clusterUnion_iff_of_assignment P L hu).2 hi

/-- Every subpair is either retained verbatim or made empty. -/
theorem interedges_subsets_eq
    (P : ClusterAssignment V I) (H : SimpleGraph V) [DecidableRel H.Adj]
    (L : Finset I) {i j : I} {X Y : Finset V}
    (hX : X ⊆ clusterVertices P i) (hY : Y ⊆ clusterVertices P j) :
    (pairPrunedGraph P H L).interedges X Y =
      if i ∈ L ∨ j ∈ L then H.interedges X Y else ∅ := by
  ext p
  by_cases hx : p.1 ∈ X
  · by_cases hy : p.2 ∈ Y
    · have hp := adj_on_clusters P H L
        ((mem_clusterVertices P i p.1).1 (hX hx))
        ((mem_clusterVertices P j p.2).1 (hY hy))
      by_cases hkeep : i ∈ L ∨ j ∈ L
      · simp only [if_pos hkeep, SimpleGraph.mem_interedges_iff, hx, hy, true_and]
        simpa only [hkeep, and_true] using hp
      · simpa [hkeep, SimpleGraph.mem_interedges_iff, hx, hy] using hp
    · split_ifs <;> simp [SimpleGraph.mem_interedges_iff, hy]
  · split_ifs <;> simp [SimpleGraph.mem_interedges_iff, hx]

theorem density_subsets_eq
    (P : ClusterAssignment V I) (H : SimpleGraph V) [DecidableRel H.Adj]
    (L : Finset I) {i j : I} {X Y : Finset V}
    (hX : X ⊆ clusterVertices P i) (hY : Y ⊆ clusterVertices P j) :
    ((pairPrunedGraph P H L).edgeDensity X Y : ℚ) =
      if i ∈ L ∨ j ∈ L then H.edgeDensity X Y else 0 := by
  rw [SimpleGraph.edgeDensity_def,
    interedges_subsets_eq P H L hX hY]
  split_ifs
  · rfl
  · simp

/-- Whole-pair deletion preserves regularity, with exactly the old error. -/
theorem uniform_pair
    (P : ClusterAssignment V I) (H : SimpleGraph V) [DecidableRel H.Adj]
    (L : Finset I) {i j : I} {ε : ℚ}
    (h : H.IsUniform ε (clusterVertices P i) (clusterVertices P j)) :
    (pairPrunedGraph P H L).IsUniform ε (clusterVertices P i) (clusterVertices P j) := by
  intro X hX Y hY hcardX hcardY
  rw [density_subsets_eq P H L hX hY,
    density_subsets_eq P H L (Finset.Subset.refl _) (Finset.Subset.refl _)]
  by_cases hkeep : i ∈ L ∨ j ∈ L
  · simp only [if_pos hkeep]
    exact h hX hY hcardX hcardY
  · simp only [if_neg hkeep, sub_self, abs_zero]
    exact h.pos

/-- Every positive-density reduced edge now has a large endpoint, without
any comparison between the density cutoff and the reservoir quota. -/
theorem every_reduced_edge_meets_large
    (P : ClusterAssignment V I) (H : SimpleGraph V) [DecidableRel H.Adj]
    (L : Finset I) (ε d : ℚ) (hd : 0 < d) {i j : I}
    (hij : (regularityReducedGraph (pairPrunedGraph P H L)
      (clusterVertices P) ε d).Adj i j) : i ∈ L ∨ j ∈ L := by
  by_contra hnot
  have hzero : ((pairPrunedGraph P H L).edgeDensity
      (clusterVertices P i) (clusterVertices P j) : ℚ) = 0 := by
    rw [density_subsets_eq P H L (Finset.Subset.refl _) (Finset.Subset.refl _)]
    simp only [if_neg hnot]
  have hle : d ≤ ((pairPrunedGraph P H L).edgeDensity
      (clusterVertices P i) (clusterVertices P j) : ℚ) := hij.2.2
  rw [hzero] at hle
  exact (not_le_of_gt hd) hle

/-- Edge-respect transports to the correspondingly pruned reduced graph. -/
theorem respects_pruned_reduced_graph
    (P : ClusterAssignment V I) (H : SimpleGraph V) (R : SimpleGraph I)
    (L : Finset I) (h : EdgesRespectReducedGraph P H R) :
    EdgesRespectReducedGraph P (pairPrunedGraph P H L)
      (pruneSmallEdges R (L : Set I)) := by
  intro u v i j hu hv huv
  have hp := (adj_on_clusters P H L hu hv).1 huv
  exact ⟨h hu hv hp.1, hp.2⟩

/-- Every deleted edge meets an original high vertex outside the large
cluster union. Orienting toward that endpoint gives the global cost bound. -/
theorem card_deleted_edges_le
    (P : ClusterAssignment V I) (H : SimpleGraph V) [DecidableRel H.Adj]
    (L : Finset I) (F : Finset V)
    (hF : ∀ ⦃u v⦄, H.Adj u v → u ∈ F ∨ v ∈ F) :
    (H.edgeFinset \ (pairPrunedGraph P H L).edgeFinset).card ≤
      (F \ clusterUnion P L).card * Fintype.card V := by
  let B := F \ clusterUnion P L
  have hcover : H.edgeFinset \ (pairPrunedGraph P H L).edgeFinset ⊆
      (B ×ˢ Finset.univ).image (fun p : V × V ↦ s(p.1, p.2)) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : H.Adj u v := by simpa using (Finset.mem_sdiff.mp he).1
      have hnouv : ¬(pairPrunedGraph P H L).Adj u v := by
        simpa using (Finset.mem_sdiff.mp he).2
      have hu : u ∉ clusterUnion P L := by
        intro hu
        exact hnouv ⟨huv, Or.inl hu⟩
      have hv : v ∉ clusterUnion P L := by
        intro hv
        exact hnouv ⟨huv, Or.inr hv⟩
      rcases hF huv with huF | hvF
      · apply Finset.mem_image.mpr
        exact ⟨(u, v), Finset.mem_product.mpr
          ⟨Finset.mem_sdiff.mpr ⟨huF, hu⟩, Finset.mem_univ _⟩, rfl⟩
      · apply Finset.mem_image.mpr
        exact ⟨(v, u), Finset.mem_product.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hvF, hv⟩, Finset.mem_univ _⟩, Sym2.eq_swap⟩
  calc
    (H.edgeFinset \ (pairPrunedGraph P H L).edgeFinset).card ≤
        ((B ×ˢ Finset.univ).image (fun p : V × V ↦ s(p.1, p.2))).card :=
      Finset.card_le_card hcover
    _ ≤ (B ×ˢ (Finset.univ : Finset V)).card := Finset.card_image_le
    _ = (F \ clusterUnion P L).card * Fintype.card V := by
      simp only [B, Finset.card_product, Finset.card_univ]

/-- The global deletion bound with the actual high-degree quota. Only the
high vertices in nonlarge clusters and in the exceptional set can pay for
deleted edges; the quota is independent of the density cutoff. -/
theorem quantitative_card_deleted_edges_le
    [Fintype I]
    (P : ClusterAssignment V I) (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (threshold quota : ℕ)
    (hH : H ≤ pruneSmallEdges G {v | threshold ≤ G.degree v}) :
    let L := largeClustersAtLeast P G threshold quota
    (H.edgeFinset \ (pairPrunedGraph P H L).edgeFinset).card ≤
      ((exceptionalVertices P).card + nonLargeHighError P G threshold quota) *
        Fintype.card V := by
  dsimp only
  let L := largeClustersAtLeast P G threshold quota
  let F := highDegreeVertices G threshold
  have hlower := highDegreeVerticesInLargeClusters_card_lower P G threshold quota
  have hcard : (F \ clusterUnion P L).card +
      (highDegreeVerticesInLargeClusters P G threshold quota).card = F.card := by
    simpa only [F, L, highDegreeVerticesInLargeClusters] using
      (Finset.card_sdiff_add_card_inter F (clusterUnion P L))
  have hbad : (F \ clusterUnion P L).card ≤
      (exceptionalVertices P).card + nonLargeHighError P G threshold quota := by
    change (F \ clusterUnion P L).card ≤
      (exceptionalVertices P).card + (Fintype.card I - L.card) * (quota - 1)
    change F.card - (exceptionalVertices P).card -
      (Fintype.card I - L.card) * (quota - 1) ≤
      (highDegreeVerticesInLargeClusters P G threshold quota).card at hlower
    omega
  have hcover : ∀ ⦃u v⦄, H.Adj u v → u ∈ F ∨ v ∈ F := by
    intro u v huv
    have hhigh := (hH huv).2
    simpa only [F, mem_highDegreeVertices, Set.mem_ofPred_eq] using hhigh
  exact (card_deleted_edges_le P H L F hcover).trans
    (Nat.mul_le_mul_right (Fintype.card V) hbad)

end Erdos547b.ZhaoClusterPairPruning

#print axioms Erdos547b.ZhaoClusterPairPruning.adj_on_clusters
#print axioms Erdos547b.ZhaoClusterPairPruning.degree_eq_of_large_cluster
#print axioms Erdos547b.ZhaoClusterPairPruning.interedges_subsets_eq
#print axioms Erdos547b.ZhaoClusterPairPruning.uniform_pair
#print axioms Erdos547b.ZhaoClusterPairPruning.every_reduced_edge_meets_large
#print axioms Erdos547b.ZhaoClusterPairPruning.respects_pruned_reduced_graph
#print axioms Erdos547b.ZhaoClusterPairPruning.card_deleted_edges_le
#print axioms Erdos547b.ZhaoClusterPairPruning.quantitative_card_deleted_edges_le
