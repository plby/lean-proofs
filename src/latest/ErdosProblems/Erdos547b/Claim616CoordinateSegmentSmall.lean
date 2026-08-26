/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchyClassification

/-!
# Uniform smallness of the Claim 6.16 allocation hierarchy

The coordinate embedding endpoint asks for one size bound covering every
hierarchy segment.  Branch-class segments inherit the canonical Zhao branch
bound, while component-root segments are singletons.  This file packages that
four-way source classification into the one premise used by the final rich
application.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateSegmentSmall

open Finset
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyClassification

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- Every segment in the allocation hierarchy has at most the Zhao partition
scale `small`. -/
theorem allocationHierarchy_segment_size_le_small
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small) (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : SegmentIndex hT P optional) :
    (AllocationHierarchy hT P optional).segments.size i ≤ small := by
  have hi : i ∈ rootSegments hT P optional ∪
      (F0Segments hT P optional S ∪
        (F1Segments hT P optional S ∪ FbSegments hT P optional)) := by
    rw [segmentClass_cover hT P optional S]
    exact Finset.mem_univ i
  simp only [Finset.mem_union] at hi
  rcases hi with hiRoot | hiF0 | hiF1 | hiFb
  · rw [rootSegment_size_eq_one hT P optional i hiRoot]
    exact hsmall
  · exact F0_segment_size_le_small hT P optional S i hiF0
  · exact F1_segment_size_le_small hT P optional S i hiF1
  · exact Fb_segment_size_le_small hT P optional i hiFb

end Erdos547b.ZhaoClaim616CoordinateSegmentSmall

#print axioms Erdos547b.ZhaoClaim616CoordinateSegmentSmall.allocationHierarchy_segment_size_le_small
