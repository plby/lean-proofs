/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchyAttachments
import ErdosProblems.Erdos547b.Claim616HierarchicalAllocation

/-!
# Per-bin source loads for the Claim 6.16 hierarchy

These are the filtered inequalities consumed directly by the unified-pool
realizer.  They only specialize `SourceSegmentAllocation` and the source
nonmixing/mass injection; no host graph occurs here.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchyLoadBounds

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

section

variable (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
variable (optional : Finset V)
variable (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
variable {CIndex K0 K1 Kb : Type*}
variable [Fintype CIndex] [DecidableEq CIndex]
variable [Fintype K0] [DecidableEq K0]
variable [Fintype K1] [DecidableEq K1]
variable [Fintype Kb] [DecidableEq Kb]
variable {clusterCapacity : CIndex → ℕ}
variable {allowed0 : CIndex → Finset K0}
variable {capacity1 : K1 → ℕ} {capacityb : Kb → ℕ}
variable {base0 : ℕ}
variable (A : SourceSegmentAllocation hT P optional S clusterCapacity allowed0
  capacity1 capacityb base0)

def F0edgeSegments (e : K0) : Finset (SegmentIndex hT P optional) :=
  (F0Segments hT P optional S).filter fun i ↦
    ∃ j, segmentSourceClass hT P optional i = Sum.inr j ∧ A.F0edge j = e

def F1edgeSegments (e : K1) : Finset (SegmentIndex hT P optional) :=
  (F1Segments hT P optional S).filter fun i ↦
    ∃ j, segmentSourceClass hT P optional i = Sum.inr j ∧ A.F1edge j = e

def FbedgeSegments (e : Kb) : Finset (SegmentIndex hT P optional) :=
  (FbSegments hT P optional).filter fun i ↦
    ∃ j, segmentSourceClass hT P optional i = Sum.inr j ∧ A.Fbedge j = e

def F0clusterSegments (C0 : CIndex) : Finset (SegmentIndex hT P optional) :=
  (F0Segments hT P optional S).filter fun i ↦
    ∃ j, segmentSourceClass hT P optional i = Sum.inr j ∧ A.F0cluster j = C0

theorem F1edgeSegments_load (e : K1) :
    (∑ i ∈ F1edgeSegments hT P optional S A e,
        (AllocationHierarchy hT P optional).segments.size i) ≤ capacity1 e := by
  let I := F1edgeSegments hT P optional S A e
  let B := (majorResidualBranches P S).filter (A.F1edge · = e)
  have hmass := sum_segmentSize_le_branchMass_of_class hT P optional I B (by
    intro i hi a
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨j, hjClass, hjEdge⟩ := hi'.2
    obtain ⟨k, hkResidual, hkClass⟩ :=
      (mem_F1Segments_iff hT P optional S i).mp hi'.1
    have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
    subst k
    refine ⟨j, Finset.mem_filter.mpr ⟨hkResidual, hjEdge⟩, ?_⟩
    exact (wholeSegment_sourceClass_eq_of_boundary hT P optional
      (canonicalWholeSourceBoundary hT P optional) i a).trans hjClass)
  exact hmass.trans (A.F1_load e)

theorem FbedgeSegments_load (e : Kb) :
    (∑ i ∈ FbedgeSegments hT P optional S A e,
        (AllocationHierarchy hT P optional).segments.size i) ≤ capacityb e := by
  let I := FbedgeSegments hT P optional S A e
  let B := (minorBranches P).filter (A.Fbedge · = e)
  have hmass := sum_segmentSize_le_branchMass_of_class hT P optional I B (by
    intro i hi a
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨j, hjClass, hjEdge⟩ := hi'.2
    obtain ⟨k, hkMinor, hkClass⟩ :=
      (mem_FbSegments_iff hT P optional i).mp hi'.1
    have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
    subst k
    refine ⟨j, Finset.mem_filter.mpr ⟨hkMinor, hjEdge⟩, ?_⟩
    exact (wholeSegment_sourceClass_eq_of_boundary hT P optional
      (canonicalWholeSourceBoundary hT P optional) i a).trans hjClass)
  exact hmass.trans (A.Fb_load e)

theorem F0edgeSegments_deep_load (e : K0) :
    (∑ i ∈ F0edgeSegments hT P optional S A e,
        segmentDeepWeight hT P optional i) ≤ base0 + small := by
  let I := F0edgeSegments hT P optional S A e
  let B := S.selected.filter (A.F0edge · = e)
  have hmass : (∑ i ∈ I,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      ∑ j ∈ B, (branchForest P).branches.size j := by
    apply sum_segmentSize_le_branchMass_of_class hT P optional
    intro i hi a
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨j, hjClass, hjEdge⟩ := hi'.2
    obtain ⟨k, hkSelected, hkClass⟩ :=
      (mem_F0Segments_iff hT P optional S i).mp hi'.1
    have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
    subst k
    refine ⟨j, Finset.mem_filter.mpr ⟨hkSelected, hjEdge⟩, ?_⟩
    exact (wholeSegment_sourceClass_eq_of_boundary hT P optional
      (canonicalWholeSourceBoundary hT P optional) i a).trans hjClass
  have hroots : #B ≤ #I := by
    apply card_branch_le_segment_of_rootClasses hT P optional
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    obtain ⟨i, hiF0, hiClass⟩ :=
      exists_F0Segment_of_mem hT P optional S j hj'.1
    exact ⟨i, Finset.mem_filter.mpr
      ⟨hiF0, ⟨j, hiClass, hj'.2⟩⟩, hiClass⟩
  exact (sum_segmentDeepWeight_le_branchDemand hT P optional I B hmass hroots).trans
    (A.F0_load e)

theorem F0clusterSegments_card (C0 : CIndex) :
    #(F0clusterSegments hT P optional S A C0) ≤ clusterCapacity C0 := by
  let source := F0Segments hT P optional S
  let B := S.selected.filter (A.F0cluster · = C0)
  let classes : Finset (CanonicalSourceClass P) := B.image Sum.inr
  have hfilter : source.filter
        (fun i ↦ segmentSourceClass hT P optional i ∈ classes) =
      F0clusterSegments hT P optional S A C0 := by
    ext i
    constructor
    · intro hi
      have hi' := Finset.mem_filter.mp hi
      obtain ⟨j, hjB, hjClass⟩ := Finset.mem_image.mp hi'.2
      have hj := Finset.mem_filter.mp hjB
      exact Finset.mem_filter.mpr
        ⟨hi'.1, ⟨j, hjClass.symm, hj.2⟩⟩
    · intro hi
      have hi' := Finset.mem_filter.mp hi
      obtain ⟨j, hjClass, hjCluster⟩ := hi'.2
      obtain ⟨k, hkSelected, hkClass⟩ :=
        (mem_F0Segments_iff hT P optional S i).mp hi'.1
      have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
      subst k
      apply Finset.mem_filter.mpr
      refine ⟨hi'.1, Finset.mem_image.mpr ?_⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨hkSelected, hjCluster⟩, hjClass.symm⟩
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter source classes
    (segmentSourceClass hT P optional)
  have hsum : #(F0clusterSegments hT P optional S A C0) =
      ∑ j ∈ B, F0segmentRootWeight hT P optional S j := by
    rw [← hfilter, ← hfiber]
    change (∑ c ∈ B.image Sum.inr,
        #(source.filter (segmentSourceClass hT P optional · = c))) = _
    rw [Finset.sum_image (fun j _ k _ hjk ↦ Sum.inr.inj hjk)]
    apply Finset.sum_congr rfl
    intro j hj
    rfl
  rw [hsum]
  exact A.F0_cluster_load C0

end

end Erdos547b.ZhaoClaim616HierarchyLoadBounds

#print axioms Erdos547b.ZhaoClaim616HierarchyLoadBounds.F0edgeSegments_deep_load
#print axioms Erdos547b.ZhaoClaim616HierarchyLoadBounds.F1edgeSegments_load
#print axioms Erdos547b.ZhaoClaim616HierarchyLoadBounds.FbedgeSegments_load
#print axioms Erdos547b.ZhaoClaim616HierarchyLoadBounds.F0clusterSegments_card
