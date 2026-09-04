/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchyClassification
import ErdosProblems.Erdos547b.Lemma59Aggregate
import ErdosProblems.Erdos547b.ForestMatching

/-!
# Matching allocation for the Claim 6.16 whole-tree hierarchy

The strengthened whole-tree segmentation splits every nontrivial segment
into one of the literal source forests `F₀`, `F₁`, and `F_b`.  This module
performs the three independent allowed-edge packings.  It contains no host
copy, candidate-degree, or containment hypothesis: the only host input is
the finite set of genuinely allowed matching edges and its cardinal lower
bound.

The result deliberately retains three edge index types.  A downstream host
constructor can therefore use the actual submatchings `M_out \ M_b`, `M₁`,
and `M_b`, prove that their endpoint supports are disjoint, and only then
combine their indices into the single `group` map expected by the online
hierarchy.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchicalAllocation

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoLemma59FullOnline
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- Three concrete matching assignments for the non-root hierarchy
segments.  The assignment functions are total only so that they can be fed
directly to later candidate definitions; their specifications concern the
corresponding source class. -/
structure ThreeClassSegmentAllocation
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (k0 k1 kb : ℕ)
    (allowed0 : SegmentIndex hT P optional → Finset (Fin k0))
    (allowed1 : SegmentIndex hT P optional → Finset (Fin k1))
    (allowedb : SegmentIndex hT P optional → Finset (Fin kb))
    (base0 base1 baseb : ℕ) where
  F0edge : SegmentIndex hT P optional → Fin k0
  F1edge : SegmentIndex hT P optional → Fin k1
  Fbedge : SegmentIndex hT P optional → Fin kb
  F0_allowed : ∀ i ∈ F0Segments hT P optional S, F0edge i ∈ allowed0 i
  F1_allowed : ∀ i ∈ F1Segments hT P optional S, F1edge i ∈ allowed1 i
  Fb_allowed : ∀ i ∈ FbSegments hT P optional, Fbedge i ∈ allowedb i
  F0_load : ∀ e : Fin k0,
    ∑ i ∈ (F0Segments hT P optional S).filter (F0edge · = e),
        segmentDeepWeight hT P optional i ≤ base0 + small
  F1_load : ∀ e : Fin k1,
    ∑ i ∈ (F1Segments hT P optional S).filter (F1edge · = e),
        segmentDeepWeight hT P optional i ≤ base1 + small
  Fb_load : ∀ e : Fin kb,
    ∑ i ∈ (FbSegments hT P optional).filter (Fbedge · = e),
        segmentDeepWeight hT P optional i ≤ baseb + small

/-- Number of hierarchy segment roots cut from one selected canonical
branch.  This is the weighted Level-1-plus-special demand assigned to a C
cluster. -/
def F0segmentRootWeight
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) : ℕ :=
  #((F0Segments hT P optional S).filter fun i ↦
    segmentSourceClass hT P optional i = Sum.inr j)

/-- Source-faithful coherent allocation object.  Allocations are attached
to original canonical branches, not independently to their hierarchy
segments.  Every segment cut from a branch therefore inherits the same
matching edge; in `F₀` it also inherits the same accessible C cluster. -/
structure SourceSegmentAllocation
    {CIndex K0 K1 Kb : Type*}
    [Fintype CIndex] [DecidableEq CIndex]
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCapacity : CIndex → ℕ)
    (allowed0 : CIndex → Finset K0)
    (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (base0 : ℕ) where
  F0cluster : BranchIndex P → CIndex
  F0edge : BranchIndex P → K0
  F1edge : BranchIndex P → K1
  Fbedge : BranchIndex P → Kb
  F0_cluster_load : ∀ C0 : CIndex,
    ∑ j ∈ S.selected.filter (F0cluster · = C0),
      F0segmentRootWeight hT P optional S j ≤ clusterCapacity C0
  F0_allowed : ∀ j ∈ S.selected, F0edge j ∈ allowed0 (F0cluster j)
  F0_load : ∀ e : K0,
    ∑ j ∈ S.selected.filter (F0edge · = e),
      ((branchForest P).branches.size j - 1) ≤ base0 + small
  F1_load : ∀ e : K1,
    ∑ j ∈ (majorResidualBranches P S).filter (F1edge · = e),
      (branchForest P).branches.size j ≤ capacity1 e
  Fb_load : ∀ e : Kb,
    ∑ j ∈ (minorBranches P).filter (Fbedge · = e),
      (branchForest P).branches.size j ≤ capacityb e

/-- The literal source demand bounds imply the three aggregate budgets used
by allowed-bin packing. -/
theorem threeClass_deep_budgets
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (m0 m1 mb base0 base1 baseb : ℕ)
    (hbudget0 : (∑ j ∈ S.selected,
        ((branchForest P).branches.size j - 1)) ≤ m0 * base0)
    (hbudget1 : (∑ j ∈ majorResidualBranches P S,
        ((branchForest P).branches.size j - 1)) ≤ m1 * base1)
    (hbudgetb : (∑ j ∈ minorBranches P,
        ((branchForest P).branches.size j - 1)) ≤ mb * baseb) :
    (∑ i ∈ F0Segments hT P optional S,
        segmentDeepWeight hT P optional i) ≤ m0 * base0 ∧
      (∑ i ∈ F1Segments hT P optional S,
        segmentDeepWeight hT P optional i) ≤ m1 * base1 ∧
      (∑ i ∈ FbSegments hT P optional,
        segmentDeepWeight hT P optional i) ≤ mb * baseb := by
  exact ⟨(sum_F0_segmentDeepWeight_le hT P optional S).trans hbudget0,
    (sum_F1_segmentDeepWeight_le hT P optional S).trans hbudget1,
    (sum_Fb_segmentDeepWeight_le hT P optional).trans hbudgetb⟩

/-- Every item in the three matching packings has weight at most the Zhao
component bound `small`. -/
theorem threeClass_segmentDeepWeight_le_small
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∀ i ∈ F0Segments hT P optional S,
      segmentDeepWeight hT P optional i ≤ small) ∧
    (∀ i ∈ F1Segments hT P optional S,
      segmentDeepWeight hT P optional i ≤ small) ∧
    (∀ i ∈ FbSegments hT P optional,
      segmentDeepWeight hT P optional i ≤ small) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact (Nat.sub_le _ _).trans
      (F0_segment_size_le_small hT P optional S i hi)
  · intro i hi
    exact (Nat.sub_le _ _).trans
      (F1_segment_size_le_small hT P optional S i hi)
  · intro i hi
    exact (Nat.sub_le _ _).trans
      (Fb_segment_size_le_small hT P optional i hi)

/-- Source-shaped three-way matching allocator.  Each allowed set is an
actual finite set of matching-edge indices.  In the Claim-6.16
specialization `allowed0` is the genuine C-to-`M₂` access set, while
`allowed1` and `allowedb` are supplied by the corresponding residual arrows.
No pointwise host-degree hypothesis occurs here. -/
theorem exists_threeClassSegmentAllocation
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (k0 k1 kb : ℕ)
    (allowed0 : SegmentIndex hT P optional → Finset (Fin k0))
    (allowed1 : SegmentIndex hT P optional → Finset (Fin k1))
    (allowedb : SegmentIndex hT P optional → Finset (Fin kb))
    (m0 m1 mb base0 base1 baseb : ℕ)
    (hk0 : 0 < k0) (hk1 : 0 < k1) (hkb : 0 < kb)
    (hm0 : 0 < m0) (hm1 : 0 < m1) (hmb : 0 < mb)
    (hallowed0 : ∀ i ∈ F0Segments hT P optional S,
      m0 ≤ #(allowed0 i))
    (hallowed1 : ∀ i ∈ F1Segments hT P optional S,
      m1 ≤ #(allowed1 i))
    (hallowedb : ∀ i ∈ FbSegments hT P optional,
      mb ≤ #(allowedb i))
    (hbudget0 : (∑ j ∈ S.selected,
        ((branchForest P).branches.size j - 1)) ≤ m0 * base0)
    (hbudget1 : (∑ j ∈ majorResidualBranches P S,
        ((branchForest P).branches.size j - 1)) ≤ m1 * base1)
    (hbudgetb : (∑ j ∈ minorBranches P,
        ((branchForest P).branches.size j - 1)) ≤ mb * baseb) :
    Nonempty (ThreeClassSegmentAllocation hT P optional S k0 k1 kb
      allowed0 allowed1 allowedb base0 base1 baseb) := by
  classical
  let : Nonempty (Fin k0) := ⟨⟨0, hk0⟩⟩
  let : Nonempty (Fin k1) := ⟨⟨0, hk1⟩⟩
  let : Nonempty (Fin kb) := ⟨⟨0, hkb⟩⟩
  obtain ⟨hdeep0, hdeep1, hdeepb⟩ :=
    threeClass_deep_budgets hT P optional S m0 m1 mb base0 base1 baseb
      hbudget0 hbudget1 hbudgetb
  obtain ⟨hsmall0, hsmall1, hsmallb⟩ :=
    threeClass_segmentDeepWeight_le_small hT P optional S
  obtain ⟨F0edge, hF0allowed, hF0load⟩ :=
    allowed_capacity_packing (F0Segments hT P optional S)
      (segmentDeepWeight hT P optional) allowed0 m0 base0 small hm0
      hallowed0 hsmall0 hdeep0
  obtain ⟨F1edge, hF1allowed, hF1load⟩ :=
    allowed_capacity_packing (F1Segments hT P optional S)
      (segmentDeepWeight hT P optional) allowed1 m1 base1 small hm1
      hallowed1 hsmall1 hdeep1
  obtain ⟨Fbedge, hFballowed, hFbload⟩ :=
    allowed_capacity_packing (FbSegments hT P optional)
      (segmentDeepWeight hT P optional) allowedb mb baseb small hmb
      hallowedb hsmallb hdeepb
  exact ⟨{
    F0edge := F0edge
    F1edge := F1edge
    Fbedge := Fbedge
    F0_allowed := hF0allowed
    F1_allowed := hF1allowed
    Fb_allowed := hFballowed
    F0_load := hF0load
    F1_load := hF1load
    Fb_load := hFbload
  }⟩

/-- Joint selected-`F₀` cluster allocation and independent residual matching
packings.  This is the exact static allocator consumed by the canonical
cleaned-system construction: `allowed0` will be instantiated by the genuine
indexed C-to-`M_out` access edges from `IndexedHostSystem`, not by a
pointwise graph-neighbor premise. -/
theorem exists_sourceSegmentAllocation
    {CIndex K0 K1 Kb : Type*}
    [Fintype CIndex] [DecidableEq CIndex] [Nonempty CIndex]
    [Fintype K0] [DecidableEq K0] [Nonempty K0]
    [Fintype K1] [DecidableEq K1] [Nonempty K1]
    [Fintype Kb] [DecidableEq Kb] [Nonempty Kb]
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCapacity : CIndex → ℕ)
    (allowed0 : CIndex → Finset K0)
    (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (m0 base0 rootSlack : ℕ)
    (hm0 : 0 < m0)
    (hrootSmall : ∀ j ∈ S.selected,
      F0segmentRootWeight hT P optional S j ≤ rootSlack)
    (hlevel0 : (∑ j ∈ S.selected,
        F0segmentRootWeight hT P optional S j) +
          Fintype.card CIndex * rootSlack ≤
      ∑ C0 : CIndex, clusterCapacity C0)
    (hallowed0 : ∀ C0, m0 ≤ #(allowed0 C0))
    (hbudget0 : (∑ j ∈ S.selected,
        ((branchForest P).branches.size j - 1)) ≤ m0 * base0)
    (hbudget1 : OrderedBranchForest.edgeDemand (F1 P S) +
        Fintype.card K1 * small ≤ ∑ e : K1, capacity1 e)
    (hbudgetb : OrderedBranchForest.edgeDemand (Fb P) +
        Fintype.card Kb * small ≤ ∑ e : Kb, capacityb e) :
    Nonempty (SourceSegmentAllocation hT P optional S
      clusterCapacity allowed0 capacity1 capacityb base0) := by
  classical
  have hsmall0 : ∀ j ∈ S.selected,
      (branchForest P).branches.size j - 1 ≤ small := by
    intro j _hj
    exact (Nat.sub_le _ _).trans (canonical_branch_size_le_small P j)
  have hsmall1 : ∀ j ∈ majorResidualBranches P S,
      (branchForest P).branches.size j ≤ small := by
    intro j _hj
    exact canonical_branch_size_le_small P j
  have hsmallb : ∀ j ∈ minorBranches P,
      (branchForest P).branches.size j ≤ small := by
    intro j _hj
    exact canonical_branch_size_le_small P j
  obtain ⟨F0cluster, hF0clusterLoad⟩ :=
    Erdos547b.ForestMatching.capacity_packing S.selected
      (F0segmentRootWeight hT P optional S) clusterCapacity rootSlack
      hrootSmall hlevel0
  obtain ⟨F0edge, hF0allowed, hF0load⟩ :=
    allowed_capacity_packing S.selected
      (fun j ↦ (branchForest P).branches.size j - 1)
      (fun j ↦ allowed0 (F0cluster j)) m0 base0 small hm0
      (fun j hj ↦ hallowed0 (F0cluster j)) hsmall0 hbudget0
  have hbudget1' :
      (∑ j ∈ majorResidualBranches P S,
          (branchForest P).branches.size j) + Fintype.card K1 * small ≤
        ∑ e : K1, capacity1 e := by
    simpa only [F1, OrderedBranchForest.edgeDemand_restrict] using hbudget1
  have hbudgetb' :
      (∑ j ∈ minorBranches P, (branchForest P).branches.size j) +
          Fintype.card Kb * small ≤ ∑ e : Kb, capacityb e := by
    simpa only [Fb, OrderedBranchForest.edgeDemand_restrict] using hbudgetb
  obtain ⟨F1edge, hF1load⟩ := Erdos547b.ForestMatching.capacity_packing
    (majorResidualBranches P S) (branchForest P).branches.size
    capacity1 small hsmall1 hbudget1'
  obtain ⟨Fbedge, hFbload⟩ := Erdos547b.ForestMatching.capacity_packing
    (minorBranches P) (branchForest P).branches.size
    capacityb small hsmallb hbudgetb'
  exact ⟨{
    F0cluster := F0cluster
    F0edge := F0edge
    F1edge := F1edge
    Fbedge := Fbedge
    F0_cluster_load := hF0clusterLoad
    F0_allowed := hF0allowed
    F0_load := hF0load
    F1_load := hF1load
    Fb_load := hFbload
  }⟩

end Erdos547b.ZhaoClaim616HierarchicalAllocation

#print axioms Erdos547b.ZhaoClaim616HierarchicalAllocation.threeClass_deep_budgets
#print axioms Erdos547b.ZhaoClaim616HierarchicalAllocation.exists_threeClassSegmentAllocation
#print axioms Erdos547b.ZhaoClaim616HierarchicalAllocation.exists_sourceSegmentAllocation
