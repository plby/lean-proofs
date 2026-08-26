/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SpecialSegmentation
import ErdosProblems.Erdos547b.Lemma59Aggregate

/-!
# Capacity allocation for arbitrary-special hierarchical segments

All segments cut from one original root-deleted branch inherit the same
cluster-layer block.  This is essential: an internal special vertex has its
parent in the matching pair chosen for an earlier segment of that branch.
The cluster packing is therefore weighted by the number of marks in each
original branch.  Matching edges may then be assigned segment by segment.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalAllocation

open Finset Fintype
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59FullOnline

variable {r b : ℕ}

/-- Number of hierarchy roots originating in one old branch. -/
def branchMarkWeight (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b) : ℕ :=
  #{z ∈ marks F special | z.1 = j}

/-- The old branch containing a hierarchy segment. -/
def segmentBranch (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (i : Fin #(marks F special)) : Fin b :=
  (markEnum F special i).1.1

/-- Counting hierarchy roots after inheriting a branch assignment is the
weighted count of marks in the assigned old branches. -/
theorem rootLoad_inherited_eq
    {C : Type*} [Fintype C] [DecidableEq C]
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (branchCluster : Fin b → C) (C0 : C) :
    rootLoad (fun i ↦ branchCluster (segmentBranch F special i)) C0 =
      ∑ j ∈ Finset.univ.filter (branchCluster · = C0),
        branchMarkWeight F special j := by
  classical
  let selectedMarks :=
    (marks F special).filter fun z ↦ branchCluster z.1 = C0
  have hindex :
      #{i : Fin #(marks F special) |
          branchCluster (segmentBranch F special i) = C0} =
        #selectedMarks := by
    apply Finset.card_bij
      (fun i _hi ↦ (markEnum F special i).1)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨(markEnum F special i).2,
        (Finset.mem_filter.mp hi).2⟩
    · intro i _hi j _hj hij
      apply (markEnum F special).injective
      exact Subtype.ext hij
    · intro z hz
      have hzmark : z ∈ marks F special := (Finset.mem_filter.mp hz).1
      let i := markIndex F special z hzmark
      refine ⟨i, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [segmentBranch, i] using (Finset.mem_filter.mp hz).2
      · simpa [i] using markEnum_index F special z hzmark
  have hsum :
      (∑ j : Fin b,
        ∑ z ∈ selectedMarks.filter (fun z ↦ z.1 = j), 1) =
          #selectedMarks := by
    simpa using
      (sum_fiberwise selectedMarks (fun z : BranchVertex F ↦ z.1)
        (fun _z ↦ 1))
  rw [rootLoad, hindex]
  symm
  calc
    ∑ j ∈ Finset.univ.filter (branchCluster · = C0),
          branchMarkWeight F special j =
        ∑ j : Fin b, if branchCluster j = C0 then
          branchMarkWeight F special j else 0 := by simp
    _ = ∑ j : Fin b,
        ∑ z ∈ selectedMarks.filter (fun z ↦ z.1 = j), 1 := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hC : branchCluster j = C0
      · simp [hC, branchMarkWeight, selectedMarks, Finset.filter_filter,
          and_assoc]
      · simp [hC, branchMarkWeight, selectedMarks, Finset.filter_filter]
    _ = #selectedMarks := hsum

/-- Each hierarchy segment inherits its cluster from its old branch and is
assigned one allowed matching edge for its non-root vertices. -/
structure SpecialAggregateAllocation
    {C K : Type*} [Fintype C] [DecidableEq C] [DecidableEq K]
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (clusterCapacity : C → ℕ) (allowedEdges : C → Finset K)
    (base matchingSlack : ℕ) where
  branchCluster : Fin b → C
  segmentEdge : Fin #(marks F special) → K
  cluster_load : ∀ C0 : C,
    ∑ j ∈ Finset.univ.filter (branchCluster · = C0),
      branchMarkWeight F special j ≤ clusterCapacity C0
  root_load : ∀ C0 : C,
    rootLoad (fun i ↦ branchCluster (segmentBranch F special i)) C0 ≤
      clusterCapacity C0
  matching_allowed : ∀ i,
    segmentEdge i ∈ allowedEdges (branchCluster (segmentBranch F special i))
  matching_load : ∀ e : K,
    ∑ i : Fin #(marks F special),
      if segmentEdge i = e then
        (toHierarchicalSegmentForest F special).segments.size i - 1 else 0 ≤
      base + matchingSlack

/-- Weighted branch packing followed by allowed-edge segment packing.  Both
assignments are constructed from the two source cardinal budgets. -/
theorem exists_specialAggregateAllocation
    {C K : Type*}
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (clusterCapacity : C → ℕ) (allowedEdges : C → Finset K)
    (m base branchSlack matchingSlack : ℕ)
    (hmpos : 0 < m)
    (hbranchSmall : ∀ j,
      branchMarkWeight F special j ≤ branchSlack)
    (hclusterBudget :
      (∑ j : Fin b, branchMarkWeight F special j) +
          Fintype.card C * branchSlack ≤
        ∑ C0 : C, clusterCapacity C0)
    (hadjacent : ∀ C0 : C, m ≤ #(allowedEdges C0))
    (hsegmentSmall : ∀ i,
      (toHierarchicalSegmentForest F special).segments.size i - 1 ≤
        matchingSlack)
    (hdeep : ∑ i : Fin #(marks F special),
        ((toHierarchicalSegmentForest F special).segments.size i - 1) ≤
      m * base) :
    Nonempty (SpecialAggregateAllocation F special clusterCapacity
      allowedEdges base matchingSlack) := by
  classical
  obtain ⟨branchCluster, hbranchLoad⟩ :=
    Erdos547b.ForestMatching.capacity_packing
      (Finset.univ : Finset (Fin b)) (branchMarkWeight F special)
      clusterCapacity branchSlack
      (by intro j _; exact hbranchSmall j) (by simpa using hclusterBudget)
  let rootGroup : Fin #(marks F special) → C := fun i ↦
    branchCluster (segmentBranch F special i)
  obtain ⟨segmentEdge, hallowed, hmatchingLoad⟩ :=
    allowed_capacity_packing
      (Finset.univ : Finset (Fin #(marks F special)))
      (fun i ↦ (toHierarchicalSegmentForest F special).segments.size i - 1)
      (fun i ↦ allowedEdges (rootGroup i)) m base matchingSlack hmpos
      (by intro i _; exact hadjacent (rootGroup i))
      (by intro i _; exact hsegmentSmall i) (by simpa using hdeep)
  exact ⟨
    { branchCluster := branchCluster
      segmentEdge := segmentEdge
      cluster_load := by
        intro C0
        simpa only using hbranchLoad C0
      root_load := by
        intro C0
        rw [rootLoad_inherited_eq]
        exact hbranchLoad C0
      matching_allowed := by
        intro i
        exact hallowed i (Finset.mem_univ i)
      matching_load := by
        intro e
        simpa [Finset.sum_filter] using hmatchingLoad e }⟩

end Erdos547b.ZhaoLemma59HierarchicalAllocation

#print axioms Erdos547b.ZhaoLemma59HierarchicalAllocation.exists_specialAggregateAllocation
