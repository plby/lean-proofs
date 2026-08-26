/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.DegreeForm
import ErdosProblems.Erdos547b.EvenReducedPadding
import ErdosProblems.Erdos547b.LargeClusterReservoir
import ErdosProblems.Erdos547b.Lemma611Full
import ErdosProblems.Erdos547b.Section6Dichotomy

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoPrunedReducedLargeEdges

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSection6Dichotomy

/-- Every edge of the reduced graph of the small--small pruned host has an
endpoint cluster meeting the original high-degree set.  Positive reduced
density supplies an actual pruned edge; such an edge cannot have two
low-degree endpoints. -/
theorem every_reduced_edge_meets_clustersMeeting
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (P : ClusterAssignment V ι)
    (C : ι → Finset V) (ε d : ℚ) (hd : 0 < d)
    (hcluster : ∀ i, C i = clusterVertices P i) :
    let H := pruneSmallEdges G {v | threshold ≤ G.degree v}
    let S := Finset.univ.filter fun v => threshold ≤ G.degree v
    let L := clustersMeeting P S
    ∀ ⦃i j : ι⦄,
      (regularityReducedGraph H C ε d).Adj i j → i ∈ L ∨ j ∈ L := by
  classical
  dsimp only
  let H := pruneSmallEdges G {v | threshold ≤ G.degree v}
  let S := Finset.univ.filter fun v => threshold ≤ G.degree v
  let L := clustersMeeting P S
  intro i j hij
  by_contra hlarge
  have hiL : i ∉ L := fun hi => hlarge (Or.inl hi)
  have hjL : j ∉ L := fun hj => hlarge (Or.inr hj)
  have hpositive : 0 < H.edgeDensity (C i) (C j) :=
    hd.trans_le hij.2.2
  have hinter : (H.interedges (C i) (C j)).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hzero : H.edgeDensity (C i) (C j) = 0 := by
      rw [H.edgeDensity_def, hempty]
      simp
    rw [hzero] at hpositive
    exact lt_irrefl 0 hpositive
  obtain ⟨p, hp⟩ := hinter
  have hp' := (SimpleGraph.mem_interedges_iff H).mp hp
  have hpi : p.1 ∈ C i := hp'.1
  have hpj : p.2 ∈ C j := hp'.2.1
  have hsmalli : ¬threshold ≤ G.degree p.1 := by
    intro hhigh
    apply hiL
    rw [mem_clustersMeeting]
    refine ⟨p.1, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhigh⟩
    · exact (mem_clusterVertices P i p.1).mp (by
        rw [← hcluster i]
        exact hpi)
  have hsmallj : ¬threshold ≤ G.degree p.2 := by
    intro hhigh
    apply hjL
    rw [mem_clustersMeeting]
    refine ⟨p.2, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhigh⟩
    · exact (mem_clusterVertices P j p.2).mp (by
        rw [← hcluster j]
        exact hpj)
  exact pruneSmallEdges_not_adj_of_not_mem G
    {v | threshold ≤ G.degree v} hsmalli hsmallj hp'.2.2

/-! ## Quantitative large clusters

The preceding one-vertex statement is not strong enough for Zhao's later
root selection.  The following counting argument is the quantitative
replacement.  In the vertex-pruned host every surviving edge has a
high-degree endpoint.  Hence, between two clusters which both contain fewer
than `quota` high-degree vertices, there are at most
`2 * (quota - 1) * clusterSize` ordered crossing edges.  A reduced pair whose
density is larger than that error therefore has a quantitatively large
endpoint.
-/

/-- Every ordered crossing edge of the vertex-pruned host lies either in
the high-degree reservoir of its left cluster or in that of its right
cluster. -/
theorem pruned_interedges_subset_reservoir_products
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (P : ClusterAssignment V ι)
    (C : ι → Finset V)
    (hcluster : ∀ i, C i = clusterVertices P i) (i j : ι) :
    let H := pruneSmallEdges G {v | threshold ≤ G.degree v}
    H.interedges (C i) (C j) ⊆
      (largeVertexReservoir P G threshold i ×ˢ C j) ∪
        (C i ×ˢ largeVertexReservoir P G threshold j) := by
  classical
  dsimp only
  intro p hp
  have hp' := (SimpleGraph.mem_interedges_iff
    (pruneSmallEdges G {v | threshold ≤ G.degree v})).mp hp
  have hhigh :=
    (pruneSmallEdges_adj G {v | threshold ≤ G.degree v} p.1 p.2).mp
      hp'.2.2
  rcases hhigh.2 with hleft | hright
  · apply Finset.mem_union_left
    apply Finset.mem_product.mpr
    refine ⟨?_, hp'.2.1⟩
    apply Finset.mem_inter.mpr
    refine ⟨?_, ?_⟩
    · rw [← hcluster i]
      exact hp'.1
    · exact (mem_highDegreeVertices G threshold p.1).mpr hleft
  · apply Finset.mem_union_right
    apply Finset.mem_product.mpr
    refine ⟨hp'.1, ?_⟩
    apply Finset.mem_inter.mpr
    refine ⟨?_, ?_⟩
    · rw [← hcluster j]
      exact hp'.2.1
    · exact (mem_highDegreeVertices G threshold p.2).mpr hright

/-- Cardinal form of `pruned_interedges_subset_reservoir_products`. -/
theorem pruned_interedges_card_le_reservoir_products
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (P : ClusterAssignment V ι)
    (C : ι → Finset V)
    (hcluster : ∀ i, C i = clusterVertices P i) (i j : ι) :
    let H := pruneSmallEdges G {v | threshold ≤ G.degree v}
    (H.interedges (C i) (C j)).card ≤
      (largeVertexReservoir P G threshold i).card * (C j).card +
        (C i).card * (largeVertexReservoir P G threshold j).card := by
  classical
  dsimp only
  calc
    ((pruneSmallEdges G {v | threshold ≤ G.degree v}).interedges
        (C i) (C j)).card ≤
        ((largeVertexReservoir P G threshold i ×ˢ C j) ∪
          (C i ×ˢ largeVertexReservoir P G threshold j)).card :=
      Finset.card_le_card
        (pruned_interedges_subset_reservoir_products
          G threshold P C hcluster i j)
    _ ≤ (largeVertexReservoir P G threshold i ×ˢ C j).card +
        (C i ×ˢ largeVertexReservoir P G threshold j).card :=
      Finset.card_union_le _ _
    _ = (largeVertexReservoir P G threshold i).card * (C j).card +
        (C i).card * (largeVertexReservoir P G threshold j).card := by
      simp only [Finset.card_product]

/-- If both endpoint clusters fail the quantitative quota, the pruned pair
has at most the explicit small--small error number of crossing edges. -/
theorem pruned_interedges_card_le_of_not_large
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota clusterSize : ℕ) (P : ClusterAssignment V ι)
    (C : ι → Finset V)
    (hcluster : ∀ i, C i = clusterVertices P i)
    (hclusterCard : ∀ i, (C i).card ≤ clusterSize)
    {i j : ι}
    (hi : i ∉ largeClustersAtLeast P G threshold quota)
    (hj : j ∉ largeClustersAtLeast P G threshold quota) :
    let H := pruneSmallEdges G {v | threshold ≤ G.degree v}
    (H.interedges (C i) (C j)).card ≤
      2 * (quota - 1) * clusterSize := by
  classical
  dsimp only
  have hri : (largeVertexReservoir P G threshold i).card ≤ quota - 1 := by
    have hnot : ¬ quota ≤
        (largeVertexReservoir P G threshold i).card := by
      simpa only [mem_largeClustersAtLeast] using hi
    omega
  have hrj : (largeVertexReservoir P G threshold j).card ≤ quota - 1 := by
    have hnot : ¬ quota ≤
        (largeVertexReservoir P G threshold j).card := by
      simpa only [mem_largeClustersAtLeast] using hj
    omega
  calc
    ((pruneSmallEdges G {v | threshold ≤ G.degree v}).interedges
        (C i) (C j)).card ≤
        (largeVertexReservoir P G threshold i).card * (C j).card +
          (C i).card * (largeVertexReservoir P G threshold j).card :=
      pruned_interedges_card_le_reservoir_products
        G threshold P C hcluster i j
    _ ≤ (quota - 1) * clusterSize + clusterSize * (quota - 1) :=
      Nat.add_le_add (Nat.mul_le_mul hri (hclusterCard j))
        (Nat.mul_le_mul (hclusterCard i) hrj)
    _ = 2 * (quota - 1) * clusterSize := by ring

/-- Quantitative replacement for `every_reduced_edge_meets_clustersMeeting`.
The last hypothesis is precisely the numeric separation between the reduced
density cutoff and the maximum number of pruned edges supported by two
non-large reservoirs. -/
theorem every_reduced_edge_meets_largeClustersAtLeast
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota clusterSize : ℕ) (P : ClusterAssignment V ι)
    (C : ι → Finset V) (ε d : ℚ)
    (hcluster : ∀ i, C i = clusterVertices P i)
    (hclusterCard : ∀ i, (C i).card = clusterSize)
    (hclusterSize : 0 < clusterSize)
    (hdensitySlots :
      (((2 * (quota - 1) * clusterSize : ℕ) : ℚ)) <
        d * (clusterSize : ℚ) * (clusterSize : ℚ)) :
    let H := pruneSmallEdges G {v | threshold ≤ G.degree v}
    let L := largeClustersAtLeast P G threshold quota
    ∀ {i j : ι},
      (regularityReducedGraph H C ε d).Adj i j → i ∈ L ∨ j ∈ L := by
  classical
  dsimp only
  intro i j hij
  by_contra hlarge
  have hi : i ∉ largeClustersAtLeast P G threshold quota :=
    fun hi => hlarge (Or.inl hi)
  have hj : j ∉ largeClustersAtLeast P G threshold quota :=
    fun hj => hlarge (Or.inr hj)
  have hupper := pruned_interedges_card_le_of_not_large
    G threshold quota clusterSize P C hcluster
      (fun k => (hclusterCard k).le) hi hj
  have hdense : d ≤
      (pruneSmallEdges G {v | threshold ≤ G.degree v}).edgeDensity
        (C i) (C j) := hij.2.2
  rw [SimpleGraph.edgeDensity_def, hclusterCard i, hclusterCard j] at hdense
  have hclusterSizeQ : (0 : ℚ) < (clusterSize : ℚ) := by
    exact_mod_cast hclusterSize
  have hdenom : (0 : ℚ) < (clusterSize : ℚ) * (clusterSize : ℚ) :=
    mul_pos hclusterSizeQ hclusterSizeQ
  have hlower :
      d * (clusterSize : ℚ) * (clusterSize : ℚ) ≤
        (((pruneSmallEdges G {v | threshold ≤ G.degree v}).interedges
          (C i) (C j)).card : ℚ) := by
    simpa only [mul_assoc] using (le_div_iff₀ hdenom).mp hdense
  have hupper' :
      ((((pruneSmallEdges G {v | threshold ≤ G.degree v}).interedges
          (C i) (C j)).card : ℕ) : ℚ) ≤
        ((2 * (quota - 1) * clusterSize : ℕ) : ℚ) := by
    exact_mod_cast hupper
  exact (not_lt_of_ge (hlower.trans hupper')) hdensitySlots

/-! ### Counting the high vertices retained by the rich cluster union -/

/-- The high-degree vertices which lie in a quantitatively large ordinary
cluster.  Exceptional high vertices and high vertices in small clusters are
the only high vertices omitted from this set. -/
def highDegreeVerticesInLargeClusters
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) : Finset V :=
  highDegreeVertices G threshold ∩
    clusterUnion P (largeClustersAtLeast P G threshold quota)

/-- Maximum number of high-degree vertices assigned to quantitatively
non-large clusters. -/
def nonLargeHighError
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) : ℕ :=
  (Fintype.card ι - (largeClustersAtLeast P G threshold quota).card) *
    (quota - 1)

theorem nonLargeHighError_le_card_mul
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) :
    nonLargeHighError P G threshold quota ≤
      Fintype.card ι * (quota - 1) := by
  unfold nonLargeHighError
  exact Nat.mul_le_mul_right (quota - 1)
    (Nat.sub_le (Fintype.card ι)
      (largeClustersAtLeast P G threshold quota).card)

theorem highDegreeVerticesInLargeClusters_subset_clusterUnion
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) :
    highDegreeVerticesInLargeClusters P G threshold quota ⊆
      clusterUnion P (largeClustersAtLeast P G threshold quota) :=
  Finset.inter_subset_right

theorem degree_of_mem_highDegreeVerticesInLargeClusters
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) {v : V}
    (hv : v ∈ highDegreeVerticesInLargeClusters P G threshold quota) :
    threshold ≤ G.degree v := by
  exact (mem_highDegreeVertices G threshold v).mp
    (Finset.inter_subset_left hv)

/-- Quantitative lower bound for the high vertices retained in large
clusters.  Each non-large cluster contributes at most `quota - 1` omitted
high vertices. -/
theorem highDegreeVerticesInLargeClusters_card_lower
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) :
    (highDegreeVertices G threshold).card -
        (exceptionalVertices P).card -
        (Fintype.card ι -
          (largeClustersAtLeast P G threshold quota).card) * (quota - 1) ≤
      (highDegreeVerticesInLargeClusters P G threshold quota).card := by
  classical
  let S := highDegreeVertices G threshold
  let L := largeClustersAtLeast P G threshold quota
  let B := highDegreeVerticesInLargeClusters P G threshold quota
  let smallReservoirs :=
    (Finset.univ \ L).biUnion (largeVertexReservoir P G threshold)
  have hcover : S ⊆ (exceptionalVertices P ∪ B) ∪ smallReservoirs := by
    intro v hvS
    cases hvP : P v with
    | none =>
        exact Finset.mem_union_left _ <|
          Finset.mem_union_left _ ((mem_exceptionalVertices P v).mpr hvP)
    | some i =>
        by_cases hi : i ∈ L
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          apply Finset.mem_inter.mpr
          refine ⟨hvS, ?_⟩
          rw [mem_clusterUnion]
          exact ⟨i, hi, hvP⟩
        · apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          refine ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
          apply Finset.mem_inter.mpr
          exact ⟨(mem_clusterVertices P i v).mpr hvP, hvS⟩
  have hsmall : smallReservoirs.card ≤
      (Finset.univ \ L).card * (quota - 1) := by
    calc
      smallReservoirs.card ≤
          ∑ i ∈ Finset.univ \ L,
            (largeVertexReservoir P G threshold i).card := by
        dsimp only [smallReservoirs]
        exact Finset.card_biUnion_le
      _ ≤ (Finset.univ \ L).card * (quota - 1) := by
        apply Finset.sum_le_card_nsmul
        intro i hi
        have hiNot : i ∉ L := (Finset.mem_sdiff.mp hi).2
        have hnotQuota : ¬ quota ≤
            (largeVertexReservoir P G threshold i).card := by
          simpa only [L, mem_largeClustersAtLeast] using hiNot
        omega
  have htotal : S.card ≤
      (exceptionalVertices P).card + B.card +
        (Finset.univ \ L).card * (quota - 1) := by
    calc
      S.card ≤ ((exceptionalVertices P ∪ B) ∪ smallReservoirs).card :=
        Finset.card_le_card hcover
      _ ≤ (exceptionalVertices P ∪ B).card + smallReservoirs.card :=
        Finset.card_union_le _ _
      _ ≤ ((exceptionalVertices P).card + B.card) +
          smallReservoirs.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (exceptionalVertices P).card + B.card +
          (Finset.univ \ L).card * (quota - 1) := by
        exact Nat.add_le_add_left hsmall _
  have hcomp : (Finset.univ \ L).card = Fintype.card ι - L.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ L)
  dsimp only [S, L, B] at htotal ⊢
  rw [hcomp] at htotal
  rw [Nat.sub_le_iff_le_add, Nat.sub_le_iff_le_add]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

/-- Specialization to the literal partition assignment stored by a
degree-form witness of the pruned host. -/
theorem every_degreeForm_reduced_edge_meets_large
    {V m₀ M : ℕ} {ε d : ℚ}
    (G : SimpleGraph (Fin V)) [DecidableRel G.Adj]
    (threshold : ℕ) (hd : 0 < d)
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | threshold ≤ G.degree v}) ε d m₀ M) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin V) ι :=
      partitionAssignment W.exceptional W.partition
    let R : SimpleGraph ι := regularityReducedGraph
      (pruneSmallEdges G {v | threshold ≤ G.degree v})
      (fun i : ι => i.1) ε d
    let S := Finset.univ.filter fun v => threshold ≤ G.degree v
    let L := clustersMeeting P S
    ∀ ⦃i j : ι⦄, R.Adj i j → i ∈ L ∨ j ∈ L := by
  classical
  dsimp only
  apply every_reduced_edge_meets_clustersMeeting G threshold
    (partitionAssignment W.exceptional W.partition)
    (fun i : {Q // Q ∈ W.partition.parts} => i.1) ε d hd
  intro i
  symm
  exact clusterVertices_partitionAssignment W.exceptional W.partition i

/-- Degree-form specialization of the quantitative edge-endpoint theorem.
Unlike `every_degreeForm_reduced_edge_meets_large`, its selected set carries
an actual `quota`-sized high-degree reservoir in every cluster. -/
theorem every_degreeForm_reduced_edge_meets_quantitativelyLarge
    {V m₀ M : ℕ} {ε d : ℚ}
    (G : SimpleGraph (Fin V)) [DecidableRel G.Adj]
    (threshold quota : ℕ)
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | threshold ≤ G.degree v}) ε d m₀ M)
    (hclusterSize : 0 < W.clusterSize)
    (hdensitySlots :
      (((2 * (quota - 1) * W.clusterSize : ℕ) : ℚ)) <
        d * (W.clusterSize : ℚ) * (W.clusterSize : ℚ)) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin V) ι :=
      partitionAssignment W.exceptional W.partition
    let R : SimpleGraph ι := regularityReducedGraph
      (pruneSmallEdges G {v | threshold ≤ G.degree v})
      (fun i : ι => i.1) ε d
    let L := largeClustersAtLeast P G threshold quota
    ∀ {i j : ι}, R.Adj i j → i ∈ L ∨ j ∈ L := by
  classical
  dsimp only
  apply every_reduced_edge_meets_largeClustersAtLeast
    G threshold quota W.clusterSize
      (partitionAssignment W.exceptional W.partition)
      (fun i : {Q // Q ∈ W.partition.parts} => i.1) ε d
  · intro i
    symm
    exact clusterVertices_partitionAssignment W.exceptional W.partition i
  · intro i
    exact W.equal_clusters i.1 i.2
  · exact hclusterSize
  · exact hdensitySlots

/-- Isolated padding preserves the property that every reduced edge meets
the selected large-cluster set. -/
theorem every_padGraph_edge_meets_padFinset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj] (L : Finset ι)
    (hlarge : ∀ ⦃i j⦄, R.Adj i j → i ∈ L ∨ j ∈ L) :
    ∀ ⦃x y : EvenPadding ι⦄,
      (padGraph R).Adj x y → x ∈ padFinset L ∨ y ∈ padFinset L := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          simpa using hlarge ((padGraph_adj_inl R i j).mp hxy)
      | inr e =>
          exact False.elim (padGraph_not_adj_inr_right R (Sum.inl i) e hxy)
  | inr e =>
      exact False.elim (padGraph_not_adj_inr_left R e y hxy)

/-- Any genuine edge of a subgraph inherits an endpoint-in-`L` statement
from its ambient graph.  This is exactly the raw-endpoint premise used by
the canonical orientation in Lemma 6.11. -/
theorem every_matching_edge_meets_finset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} [DecidableRel R.Adj]
    (L : Finset ι) (M : R.Subgraph)
    (hlarge : ∀ ⦃i j⦄, R.Adj i j → i ∈ L ∨ j ∈ L) :
    ∀ e : MatchingEdge M, e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L := by
  intro e
  have h := hlarge (M.adj_sub (orientedEndpoint_adj M L e))
  by_cases hfirst : e.1.out.1 ∈ L
  · exact Or.inl hfirst
  · right
    simpa [orientedEndpoint, rawEndpoint, hfirst] using h

/-- The exact `hlarge` argument required by Lemma 6.11 and Claim 6.18 for
the Claim-6.7 certificate returned from the canonical padded reduced graph. -/
theorem every_claim67_matching_edge_meets_large
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (L : Finset ι) (miss : ℕ)
    (C67 : Claim67Certificate (padGraph R) (padFinset L) miss)
    (hlarge : ∀ ⦃i j⦄, R.Adj i j → i ∈ L ∨ j ∈ L) :
    ∀ e : MatchingEdge C67.M,
      e.1.out.1 ∈ padFinset L ∨ e.1.out.2 ∈ padFinset L :=
  every_matching_edge_meets_finset (padFinset L) C67.M
    (every_padGraph_edge_meets_padFinset R L hlarge)

/-- End-to-end spelling for a certificate produced after applying degree
form to the vertex-pruned host. -/
theorem every_pruned_degreeForm_claim67_edge_meets_large
    {N m₀ M miss : ℕ} {ε d : ℚ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (threshold : ℕ) (hd : 0 < d)
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | threshold ≤ G.degree v}) ε d m₀ M) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin N) ι :=
      partitionAssignment W.exceptional W.partition
    let R : SimpleGraph ι := regularityReducedGraph
      (pruneSmallEdges G {v | threshold ≤ G.degree v})
      (fun i : ι => i.1) ε d
    letI : DecidableRel R.Adj := Classical.decRel _
    let S := Finset.univ.filter fun v => threshold ≤ G.degree v
    let L := clustersMeeting P S
    ∀ C67 : Claim67Certificate (padGraph R) (padFinset L) miss,
      ∀ e : MatchingEdge C67.M,
        e.1.out.1 ∈ padFinset L ∨ e.1.out.2 ∈ padFinset L := by
  classical
  dsimp only
  intro C67
  apply every_claim67_matching_edge_meets_large _ _ _ C67
  exact every_degreeForm_reduced_edge_meets_large G threshold hd W

/-- End-to-end quantitative form of the matching-edge endpoint property.
It plugs a certificate from `claim6_1_rich_full` directly into the
orientation premise of Lemma 6.11. -/
theorem every_pruned_degreeForm_claim67_edge_meets_quantitativelyLarge
    {N m₀ M miss : ℕ} {ε d : ℚ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (threshold quota : ℕ)
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | threshold ≤ G.degree v}) ε d m₀ M)
    (hclusterSize : 0 < W.clusterSize)
    (hdensitySlots :
      (((2 * (quota - 1) * W.clusterSize : ℕ) : ℚ)) <
        d * (W.clusterSize : ℚ) * (W.clusterSize : ℚ)) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin N) ι :=
      partitionAssignment W.exceptional W.partition
    let R : SimpleGraph ι := regularityReducedGraph
      (pruneSmallEdges G {v | threshold ≤ G.degree v})
      (fun i : ι => i.1) ε d
    letI : DecidableRel R.Adj := Classical.decRel _
    let L := largeClustersAtLeast P G threshold quota
    ∀ C67 : Claim67Certificate (padGraph R) (padFinset L) miss,
      ∀ e : MatchingEdge C67.M,
        e.1.out.1 ∈ padFinset L ∨ e.1.out.2 ∈ padFinset L := by
  classical
  dsimp only
  intro C67
  apply every_claim67_matching_edge_meets_large _ _ _ C67
  intro i j hij
  exact every_degreeForm_reduced_edge_meets_quantitativelyLarge
    G threshold quota W hclusterSize hdensitySlots hij

#print axioms every_reduced_edge_meets_largeClustersAtLeast
#print axioms every_degreeForm_reduced_edge_meets_quantitativelyLarge
#print axioms highDegreeVerticesInLargeClusters_card_lower
#print axioms every_pruned_degreeForm_claim67_edge_meets_quantitativelyLarge

end Erdos547b.ZhaoPrunedReducedLargeEdges
