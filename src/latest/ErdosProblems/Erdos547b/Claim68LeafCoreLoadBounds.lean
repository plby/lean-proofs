/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68LeafCoreClassification
import ErdosProblems.Erdos547b.Claim616HierarchicalAllocation

/-!
# Matching-bin loads of the Claim 6.8 leaf core

The branch-coherent `SourceSegmentAllocation` is chosen on the original
Zhao branches.  This file proves that the leaf-deleted hierarchy inherits
its three matching-bin bounds.  Leaf deletion only removes source
coordinates, so no host or embedding premise is involved.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim68LeafCoreLoadBounds

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim68LeafCoreClassification

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

section

variable (hT : T.IsTree) (P : TreePartition.ZhaoForestPartition T globalRoot small)
variable (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
variable {c k0 k1 kb : ℕ}
variable {clusterCapacity : Fin c → ℕ}
variable {allowed0 : Fin c → Finset (Fin k0)}
variable {capacity1 : Fin k1 → ℕ} {capacityb : Fin kb → ℕ}
variable {base0 : ℕ}
variable (A : SourceSegmentAllocation hT P ∅ S c k0 k1 kb
  clusterCapacity allowed0 capacity1 capacityb base0)

def leafF0edgeSegments (e : Fin k0) :
    Finset (LeafSegmentIndex P hT) :=
  (leafF0Segments P hT S).filter fun i ↦
    ∃ j, leafSegmentSourceClass P hT i = Sum.inr j ∧ A.F0edge j = e

def leafF1edgeSegments (e : Fin k1) :
    Finset (LeafSegmentIndex P hT) :=
  (leafF1Segments P hT S).filter fun i ↦
    ∃ j, leafSegmentSourceClass P hT i = Sum.inr j ∧ A.F1edge j = e

def leafFbedgeSegments (e : Fin kb) :
    Finset (LeafSegmentIndex P hT) :=
  (leafFbSegments P hT).filter fun i ↦
    ∃ j, leafSegmentSourceClass P hT i = Sum.inr j ∧ A.Fbedge j = e

theorem leafF1edgeSegments_load (e : Fin k1) :
    (∑ i ∈ leafF1edgeSegments hT P S A e,
        (leafAllocationHierarchy P hT).segments.size i) ≤ capacity1 e := by
  let I := leafF1edgeSegments hT P S A e
  let B := (majorResidualBranches P S).filter (A.F1edge · = e)
  have hmass := sum_leafSegmentSize_le_branchMass_of_class P hT I B (by
    intro i hi a
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨j, hjClass, hjEdge⟩ := hi'.2
    obtain ⟨k, hkResidual, hkClass⟩ :=
      (mem_leafF1Segments_iff P hT S i).mp hi'.1
    have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
    subst k
    refine ⟨j, Finset.mem_filter.mpr ⟨hkResidual, hjEdge⟩, ?_⟩
    exact (leafWholeSegment_sourceClass_eq P hT i a).trans hjClass)
  exact hmass.trans (by simpa [B] using A.F1_load e)

theorem leafFbedgeSegments_load (e : Fin kb) :
    (∑ i ∈ leafFbedgeSegments hT P A e,
        (leafAllocationHierarchy P hT).segments.size i) ≤ capacityb e := by
  let I := leafFbedgeSegments hT P A e
  let B := (minorBranches P).filter (A.Fbedge · = e)
  have hmass := sum_leafSegmentSize_le_branchMass_of_class P hT I B (by
    intro i hi a
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨j, hjClass, hjEdge⟩ := hi'.2
    obtain ⟨k, hkMinor, hkClass⟩ :=
      (mem_leafFbSegments_iff P hT i).mp hi'.1
    have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
    subst k
    refine ⟨j, Finset.mem_filter.mpr ⟨hkMinor, hjEdge⟩, ?_⟩
    exact (leafWholeSegment_sourceClass_eq P hT i a).trans hjClass)
  exact hmass.trans (by simpa [B] using A.Fb_load e)

theorem leafF0edgeSegments_deep_load (e : Fin k0) :
    (∑ i ∈ leafF0edgeSegments hT P S A e,
        leafSegmentDeepWeight P hT i) ≤ base0 + small := by
  let I := leafF0edgeSegments hT P S A e
  let B := S.selected.filter (A.F0edge · = e)
  have hmass : (∑ i ∈ I,
        (leafAllocationHierarchy P hT).segments.size i) ≤
      ∑ j ∈ B, (branchForest P).branches.size j := by
    apply sum_leafSegmentSize_le_branchMass_of_class P hT
    intro i hi a
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨j, hjClass, hjEdge⟩ := hi'.2
    obtain ⟨k, hkSelected, hkClass⟩ :=
      (mem_leafF0Segments_iff P hT S i).mp hi'.1
    have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
    subst k
    refine ⟨j, Finset.mem_filter.mpr ⟨hkSelected, hjEdge⟩, ?_⟩
    exact (leafWholeSegment_sourceClass_eq P hT i a).trans hjClass
  have hroots : #B ≤ #I := by
    apply card_branch_le_leafSegment_of_rootClasses P hT
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    obtain ⟨i, hiClass⟩ := exists_leafSegmentRoot_of_selectedBranch
      P hT S j hj'.1
    have hiF0 : i ∈ leafF0Segments P hT S :=
      (mem_leafF0Segments_iff P hT S i).2 ⟨j, hj'.1, hiClass⟩
    exact ⟨i, Finset.mem_filter.mpr
      ⟨hiF0, ⟨j, hiClass, hj'.2⟩⟩, hiClass⟩
  exact (sum_leafSegmentDeepWeight_le_branchDemand P hT I B hmass hroots).trans
    (by simpa [B] using A.F0_load e)

end

end Erdos547b.ZhaoClaim68LeafCoreLoadBounds

#print axioms Erdos547b.ZhaoClaim68LeafCoreLoadBounds.leafF0edgeSegments_deep_load
#print axioms Erdos547b.ZhaoClaim68LeafCoreLoadBounds.leafF1edgeSegments_load
#print axioms Erdos547b.ZhaoClaim68LeafCoreLoadBounds.leafFbedgeSegments_load
