/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateCanonicalOptional

/-!
# Counting direct hierarchy children

The target-cleaning Hall budget only depends on the number of hierarchy
segments attached directly to the global source root.  This module bounds
that number by the total mark count and then by the literal canonical and
optional mark budgets.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateDirectCount

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616CoordinateCanonicalOptional
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The total number of hierarchy segments is controlled by the branch-root
marks and the allocation special set. -/
theorem card_segments_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    Fintype.card (SegmentIndex hT P optional) ≤
      Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
        (P.numParts + Fintype.card (BranchIndex P) + #optional) := by
  calc
    Fintype.card (SegmentIndex hT P optional) =
        #(marks (wholeBranchForest T hT globalRoot)
          (AllocationSpecial hT P optional)) := by
      simp only [SegmentIndex, Fintype.card_fin]
    _ ≤ Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
          #(AllocationSpecial hT P optional) :=
      card_marks_le (wholeBranchForest T hT globalRoot)
        (AllocationSpecial hT P optional)
    _ ≤ Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
          (P.numParts + Fintype.card (BranchIndex P) + #optional) :=
      Nat.add_le_add_left (card_AllocationSpecial_le hT P optional) _

/-- Canonical cut-parent marks contribute at most one further `P.numParts`
to the total hierarchy-segment count. -/
theorem card_segments_canonicalOptional_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small) :
    Fintype.card (SegmentIndex hT P (canonicalOptional P)) ≤
      Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
        (P.numParts + Fintype.card (BranchIndex P) + P.numParts) := by
  exact (card_segments_le hT P (canonicalOptional P)).trans
    (Nat.add_le_add_left
      (Nat.add_le_add_left (canonicalOptional_card_le_numParts P)
        (P.numParts + Fintype.card (BranchIndex P)))
      (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot))))

/-- Direct children form a subset of all hierarchy segments, whose cardinal
is controlled by the branch-root marks plus the allocation special set. -/
theorem card_directSegments_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    #(Finset.univ.filter fun i : SegmentIndex hT P optional ↦
        (AllocationHierarchy hT P optional).parent i = Sum.inl 0) ≤
      Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
        (P.numParts + Fintype.card (BranchIndex P) + #optional) := by
  calc
    #(Finset.univ.filter fun i : SegmentIndex hT P optional ↦
        (AllocationHierarchy hT P optional).parent i = Sum.inl 0) ≤
        #(Finset.univ : Finset (SegmentIndex hT P optional)) :=
      Finset.card_filter_le _ _
    _ = #(marks (wholeBranchForest T hT globalRoot)
          (AllocationSpecial hT P optional)) := by
      simp only [SegmentIndex, Finset.card_univ, Fintype.card_fin]
    _ ≤ Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
          #(AllocationSpecial hT P optional) :=
      card_marks_le (wholeBranchForest T hT globalRoot)
        (AllocationSpecial hT P optional)
    _ ≤ Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
          (P.numParts + Fintype.card (BranchIndex P) + #optional) :=
      Nat.add_le_add_left (card_AllocationSpecial_le hT P optional) _

/-- With the canonical cut-parent optional set, its cardinal contribution is
at most one further `P.numParts`. -/
theorem card_directSegments_canonicalOptional_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small) :
    #(Finset.univ.filter fun i : SegmentIndex hT P (canonicalOptional P) ↦
        (AllocationHierarchy hT P (canonicalOptional P)).parent i =
          Sum.inl 0) ≤
      Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
        (P.numParts + Fintype.card (BranchIndex P) + P.numParts) := by
  exact (card_directSegments_le hT P (canonicalOptional P)).trans
    (Nat.add_le_add_left
      (Nat.add_le_add_left (canonicalOptional_card_le_numParts P)
        (P.numParts + Fintype.card (BranchIndex P)))
      (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot))))

end Erdos547b.ZhaoClaim616CoordinateDirectCount

#print axioms Erdos547b.ZhaoClaim616CoordinateDirectCount.card_directSegments_le
#print axioms Erdos547b.ZhaoClaim616CoordinateDirectCount.card_directSegments_canonicalOptional_le
#print axioms Erdos547b.ZhaoClaim616CoordinateDirectCount.card_segments_le
#print axioms Erdos547b.ZhaoClaim616CoordinateDirectCount.card_segments_canonicalOptional_le
