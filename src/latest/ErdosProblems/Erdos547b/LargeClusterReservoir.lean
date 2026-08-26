/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Stability

/-!
# Quantitative large clusters and their high-degree reservoirs

In Zhao's Section 6, a reduced cluster is called large when it contains at
least `2 * sqrt d * N` vertices of host degree at least the tree size.  This
is quantitatively stronger than merely meeting the high-degree set.  The
distinction is essential in Claim 6.8 and Claim 6.17, where Lemma 6.5 is
applied with actual large-vertex reservoirs `A₀` and `B₀` inside two large
clusters.

This file records the exact finite definition and the reservoir extraction
facts.  It deliberately coexists with the older `clustersMeeting` notion:
callers which need Zhao's root reservoirs must use `largeClustersAtLeast`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoQuantitativeLargeClusters

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability

universe u v

/-- The literal host vertices of degree at least `threshold`. -/
def highDegreeVertices
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) : Finset V :=
  Finset.univ.filter fun z => threshold ≤ G.degree z

@[simp] theorem mem_highDegreeVertices
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (z : V) :
    z ∈ highDegreeVertices G threshold ↔ threshold ≤ G.degree z := by
  simp [highDegreeVertices]

/-- The actual high-degree vertices assigned to a cluster. -/
def largeVertexReservoir
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (i : I) : Finset V :=
  clusterVertices P i ∩ highDegreeVertices G threshold

theorem largeVertexReservoir_subset_cluster
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (i : I) :
    largeVertexReservoir P G threshold i ⊆ clusterVertices P i :=
  Finset.inter_subset_left

theorem largeVertexReservoir_subset_highDegree
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (i : I) :
    largeVertexReservoir P G threshold i ⊆ highDegreeVertices G threshold :=
  Finset.inter_subset_right

theorem degree_of_mem_largeVertexReservoir
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) (i : I) {z : V}
    (hz : z ∈ largeVertexReservoir P G threshold i) :
    threshold ≤ G.degree z := by
  exact (mem_highDegreeVertices G threshold z).mp
    (largeVertexReservoir_subset_highDegree P G threshold i hz)

/-- Zhao's quantitative family of large clusters. -/
def largeClustersAtLeast
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) : Finset I :=
  Finset.univ.filter fun i =>
    quota ≤ (largeVertexReservoir P G threshold i).card

@[simp] theorem mem_largeClustersAtLeast
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) (i : I) :
    i ∈ largeClustersAtLeast P G threshold quota ↔
      quota ≤ (largeVertexReservoir P G threshold i).card := by
  simp [largeClustersAtLeast]

/-- Membership in the quantitative large-cluster set supplies the literal
reservoir used as `A₀` or `B₀` in Zhao Lemma 6.5. -/
theorem largeVertexReservoir_card
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) {i : I}
    (hi : i ∈ largeClustersAtLeast P G threshold quota) :
    quota ≤ (largeVertexReservoir P G threshold i).card :=
  (mem_largeClustersAtLeast P G threshold quota i).mp hi

/-- Extract an exactly `quota`-sized large-vertex reservoir from a
quantitatively large cluster. -/
theorem exists_reservoir_card_eq
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) {i : I}
    (hi : i ∈ largeClustersAtLeast P G threshold quota) :
    ∃ A0 : Finset V,
      A0 ⊆ clusterVertices P i ∧
      A0.card = quota ∧
      ∀ z ∈ A0, threshold ≤ G.degree z := by
  obtain ⟨A0, hA0sub, hA0card⟩ :=
    Finset.exists_subset_card_eq
      (largeVertexReservoir_card P G threshold quota hi)
  refine ⟨A0,
    hA0sub.trans (largeVertexReservoir_subset_cluster P G threshold i),
    hA0card, ?_⟩
  intro z hz
  exact degree_of_mem_largeVertexReservoir P G threshold i (hA0sub hz)

/-- The full reservoir itself is often preferable to an arbitrary exact
subreservoir: it remains canonically tied to the degree-form assignment. -/
theorem reservoir_spec_of_mem_largeClustersAtLeast
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) {i : I}
    (hi : i ∈ largeClustersAtLeast P G threshold quota) :
    largeVertexReservoir P G threshold i ⊆ clusterVertices P i ∧
      quota ≤ (largeVertexReservoir P G threshold i).card ∧
      ∀ z ∈ largeVertexReservoir P G threshold i,
        threshold ≤ G.degree z := by
  exact ⟨largeVertexReservoir_subset_cluster P G threshold i,
    largeVertexReservoir_card P G threshold quota hi,
    fun _ hz => degree_of_mem_largeVertexReservoir P G threshold i hz⟩

/-- Every high-degree host vertex is exceptional or belongs to the
high-degree reservoir of its assigned cluster. -/
theorem highDegreeVertices_subset_exceptional_union_reservoirs
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold : ℕ) :
    highDegreeVertices G threshold ⊆
      exceptionalVertices P ∪
        Finset.univ.biUnion (largeVertexReservoir P G threshold) := by
  intro z hz
  cases hzP : P z with
  | none =>
      exact Finset.mem_union_left _
        ((mem_exceptionalVertices P z).mpr hzP)
  | some i =>
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      exact Finset.mem_inter.mpr
        ⟨(mem_clusterVertices P i z).mpr hzP, hz⟩

/-- Exact counting upper bound behind Zhao Claim 6.1(2).  A cluster outside
the quantitative large family contains at most `quota - 1` high-degree
vertices, while a large cluster contains at most the full cluster size. -/
theorem highDegree_card_le_exceptional_add_large_small
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota clusterSize : ℕ)
    (hquota : 0 < quota)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ clusterSize) :
    (highDegreeVertices G threshold).card ≤
      (exceptionalVertices P).card +
        (largeClustersAtLeast P G threshold quota).card * clusterSize +
        (Fintype.card I -
          (largeClustersAtLeast P G threshold quota).card) * (quota - 1) := by
  classical
  let L := largeClustersAtLeast P G threshold quota
  let reservoir := largeVertexReservoir P G threshold
  have hcover : (highDegreeVertices G threshold).card ≤
      (exceptionalVertices P).card +
        ∑ i : I, (reservoir i).card := by
    calc
      (highDegreeVertices G threshold).card ≤
          (exceptionalVertices P ∪
            Finset.univ.biUnion reservoir).card :=
        Finset.card_le_card
          (highDegreeVertices_subset_exceptional_union_reservoirs
            P G threshold)
      _ ≤ (exceptionalVertices P).card +
          (Finset.univ.biUnion reservoir).card :=
        Finset.card_union_le _ _
      _ ≤ (exceptionalVertices P).card +
          ∑ i : I, (reservoir i).card := by
        exact Nat.add_le_add_left
          Finset.card_biUnion_le _
  have hlarge : (∑ i ∈ L, (reservoir i).card) ≤ L.card * clusterSize := by
    apply Finset.sum_le_card_nsmul
    intro i hi
    exact (Finset.card_le_card
      (largeVertexReservoir_subset_cluster P G threshold i)).trans
        (hcluster i)
  have hsmall : (∑ i ∈ Finset.univ \ L, (reservoir i).card) ≤
      (Finset.univ \ L).card * (quota - 1) := by
    apply Finset.sum_le_card_nsmul
    intro i hi
    have hiNot : i ∉ L := (Finset.mem_sdiff.mp hi).2
    have hnotQuota : ¬quota ≤ (reservoir i).card := by
      simpa [L, reservoir, mem_largeClustersAtLeast] using hiNot
    omega
  have hsplit : (∑ i : I, (reservoir i).card) =
      (∑ i ∈ L, (reservoir i).card) +
        ∑ i ∈ Finset.univ \ L, (reservoir i).card := by
    have hs := Finset.sum_sdiff (Finset.subset_univ L)
      (f := fun i : I => (reservoir i).card)
    rw [← hs, Nat.add_comm]
  have hcomp : (Finset.univ \ L).card = Fintype.card I - L.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ L),
      Finset.card_univ]
  rw [hsplit] at hcover
  rw [hcomp] at hsmall
  have hbound :
      (highDegreeVertices G threshold).card ≤
        (exceptionalVertices P).card +
          L.card * clusterSize +
          (Fintype.card I - L.card) * (quota - 1) := by
    omega
  simpa only [L] using hbound

end Erdos547b.ZhaoQuantitativeLargeClusters

#print axioms Erdos547b.ZhaoQuantitativeLargeClusters.exists_reservoir_card_eq
