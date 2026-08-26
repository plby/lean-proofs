/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateRootLoad

/-!
# Canonical cardinal bound for distinguished root segments

A hierarchy segment in a component-root source class is a singleton, and two
such segments with the same component class have the same literal segment
root.  Injectivity of the whole-hierarchy coordinate map therefore injects
all distinguished-root segments into the finite component index set.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateRootCount

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateRootLoad
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- On either distinguished side, there is at most one hierarchy root
segment per Zhao component. -/
theorem card_rootReservoirSegments_le_numParts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (side : Fin 2) :
    #(rootReservoirSegments hT P optional side) ≤ P.numParts := by
  classical
  let I := rootReservoirSegments hT P optional side
  have hclass : ∀ z : {i // i ∈ I},
      ∃ q : Fin P.numParts,
        segmentSourceClass hT P optional z.1 = Sum.inl q := by
    intro z
    exact ⟨Classical.choose (Finset.mem_filter.mp z.2).2,
      (Classical.choose_spec (Finset.mem_filter.mp z.2).2).1⟩
  let f : {i // i ∈ I} → Fin P.numParts := fun z ↦
    Classical.choose (hclass z)
  have hf : Function.Injective f := by
    intro z w hzw
    have hzClass : segmentSourceClass hT P optional z.1 = Sum.inl (f z) :=
      Classical.choose_spec (hclass z)
    have hwClass : segmentSourceClass hT P optional w.1 = Sum.inl (f w) :=
      Classical.choose_spec (hclass w)
    have hzRoot : SegmentRootOriginal hT P optional z.1 = P.roots (f z) := by
      apply (literalSourceClass_eq_inl_iff P _ (f z)).mp
      exact hzClass
    have hwRoot : SegmentRootOriginal hT P optional w.1 = P.roots (f w) := by
      apply (literalSourceClass_eq_inl_iff P _ (f w)).mp
      exact hwClass
    have hrootCoordinate :
        (AllocationHierarchy hT P optional).segmentRoot z.1 =
          (AllocationHierarchy hT P optional).segmentRoot w.1 := by
      apply wholeHierarchyOriginalVertex_injective hT
        (AllocationSpecial hT P optional)
      change SegmentRootOriginal hT P optional z.1 =
        SegmentRootOriginal hT P optional w.1
      exact hzRoot.trans (congrArg P.roots hzw) |>.trans hwRoot.symm
    have hsigma := Sum.inr.inj hrootCoordinate
    apply Subtype.ext
    exact (Sigma.mk.inj_iff.mp hsigma).1
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [I, Fintype.card_coe, Fintype.card_fin] using hcard

end Erdos547b.ZhaoClaim616CoordinateRootCount

#print axioms Erdos547b.ZhaoClaim616CoordinateRootCount.card_rootReservoirSegments_le_numParts
