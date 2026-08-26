/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCutCoordinates

/-!
# The actual Zhao partition supplies the cut-coordinate data

The parent coordinate decodes to the recorded original tree vertex.
Earlier ownership, reservoir-side compatibility and rooted colour zero
follow from the partition ordering, tree parity and the reconnect rule.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePartitionCutCoordinates

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.TreePartition
open Erdos547b.ZhaoSourceGlobalPrefixState Erdos547b.ZhaoSourceTwoSideFamilyAdvance
open Erdos547b.ZhaoSourcePendingParentDegree Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoClaim68 Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyAttachments Erdos547b.ZhaoClaim616HierarchyClassification

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

private theorem otherSide_eq_of_ne (s t : Fin 2) (h : s ≠ t) : otherSide s = t := by
  fin_cases s <;> fin_cases t <;> simp_all [otherSide]

/-- Adjacent component roots have opposite reservoir tags. -/
theorem componentReservoirSide_opposite_of_adj (hT : T.IsTree)
    (i j : Fin P.numParts) (hij : T.Adj (P.roots i) (P.roots j)) :
    otherSide (componentReservoirSide P i) = componentReservoirSide P j := by
  apply otherSide_eq_of_ne
  have hparity := TreePartition.rootParity_ne_of_adj hT globalRoot hij
  unfold componentReservoirSide
  by_cases hi : T.dist globalRoot (P.roots i) % 2 = (majorParity P).val
  · by_cases hj : T.dist globalRoot (P.roots j) % 2 = (majorParity P).val
    · exact (hparity (hi.trans hj.symm)).elim
    · simp [hi, hj]
  · by_cases hj : T.dist globalRoot (P.roots j) % 2 = (majorParity P).val
    · simp [hi, hj]
    · have hiLt := Nat.mod_lt (T.dist globalRoot (P.roots i)) (by omega : 0 < 2)
      have hjLt := Nat.mod_lt (T.dist globalRoot (P.roots j)) (by omega : 0 < 2)
      have hmLt := (majorParity P).isLt
      have heq : T.dist globalRoot (P.roots i) % 2 = T.dist globalRoot (P.roots j) % 2 := by omega
      exact (hparity heq).elim

def partitionParent (i : Fin P.numParts) (hi : i.val ≠ 0) :
    CutCoordinate (branchForest P).branches P.numParts :=
  if hroot : P.parent i hi = P.roots (P.parentPart i hi) then
    Sum.inl (P.parentPart i hi)
  else Sum.inr (cutParentBranchCoordinate P i hi hroot)

def coordinateVertex (x : CutCoordinate (branchForest P).branches P.numParts) : U :=
  match x with
  | Sum.inl i => P.roots i
  | Sum.inr a => (partitionBranchEquivNonroots P a).1

theorem partitionParent_vertex (i : Fin P.numParts) (hi : i.val ≠ 0) :
    coordinateVertex P (partitionParent P i hi) = P.parent i hi := by
  unfold partitionParent
  split_ifs with hroot
  · exact hroot.symm
  · exact cutParentBranchCoordinate_value P i hi hroot

theorem partitionParent_before (i : Fin P.numParts) (hi : i.val ≠ 0) :
    (coordinateOwner (branchForest P).branches (branchForest P).owner (partitionParent P i hi)).val < i.val := by
  unfold partitionParent
  split_ifs with hroot
  · exact P.parent_earlier i hi
  · change ((branchForest P).owner (cutParentBranchCoordinate P i hi hroot).1).val < i.val
    rw [cutParentBranchCoordinate_owner]
    exact P.parent_earlier i hi

theorem partitionParent_color (hT : T.IsTree) (i : Fin P.numParts) (hi : i.val ≠ 0) :
    coordinateColor (branchForest P).branches (partitionParent P i hi) := by
  unfold partitionParent
  split_ifs with hroot
  · trivial
  · exact cutParent_coordinate_color_zero hT P i hi hroot

theorem partitionParent_side (hT : T.IsTree) {k : ℕ}
    (locate : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 × Fin k)
    (hlocate : ∀ j, (locate j).1 = componentReservoirSide P ((branchForest P).owner j))
    (i : Fin P.numParts) (hi : i.val ≠ 0) :
    coordinateSide (branchForest P).branches (componentReservoirSide P) locate (partitionParent P i hi) =
      componentReservoirSide P i := by
  unfold partitionParent
  split_ifs with hroot
  · apply componentReservoirSide_opposite_of_adj P hT
    have ha := (P.cut_adj i hi).symm
    rwa [hroot] at ha
  · change (locate (cutParentBranchCoordinate P i hi hroot).1).1 = componentReservoirSide P i
    rw [hlocate, cutParentBranchCoordinate_owner]
    have hp : T.dist globalRoot (P.roots i) % 2 =
        T.dist globalRoot (P.roots (P.parentPart i hi)) % 2 :=
      (P.reconnect_rule i hi).resolve_left hroot
    unfold componentReservoirSide
    rw [hp]

/-- All cut data are supplied by the literal tree partition and source
family tags. There is no host-side premise in this constructor. -/
def partitionCutSource (hT : T.IsTree) {k : ℕ}
    (locate : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 × Fin k)
    (hlocate : ∀ j, (locate j).1 = componentReservoirSide P ((branchForest P).owner j)) :
    CutSource (branchForest P).branches (branchForest P).owner (componentReservoirSide P) locate where
  parent := partitionParent P
  before := partitionParent_before P
  side := partitionParent_side P hT locate hlocate
  color := partitionParent_color P hT

end Erdos547b.ZhaoSourcePartitionCutCoordinates

#print axioms Erdos547b.ZhaoSourcePartitionCutCoordinates.componentReservoirSide_opposite_of_adj
#print axioms Erdos547b.ZhaoSourcePartitionCutCoordinates.partitionParent_vertex
#print axioms Erdos547b.ZhaoSourcePartitionCutCoordinates.partitionCutSource
