/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinatePairFacts

/-!
# Segment color equals canonical branch parity

The coordinate source layout is indexed by parity in the original canonical
branch, whereas the dynamic local tree theorems use the canonical two-coloring
of each marked segment.  These colorings agree because both color the segment
root zero and both flip across every segment edge.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateSegmentColor

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616RichCoordinatePairFacts
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

/-- Two `Fin 2` colorings of a tree which agree at one root agree
everywhere. -/
theorem finTwoColoring_eq_of_root
    {A : Type u} {G : SimpleGraph A}
    (hG : G.IsTree) (root : A) (c d : G.Coloring (Fin 2))
    (hroot : c root = d root) (a : A) : c a = d a := by
  induction hd : G.dist root a using Nat.strong_induction_on generalizing a with
  | h n ih =>
      by_cases ha : a = root
      · subst a
        exact hroot
      · let p := TreePartition.parent hG root ha
        have hdist := TreePartition.parent_dist_add_one hG root ha
        have hdist' : G.dist root p + 1 = G.dist root a := by
          simpa [p] using hdist
        have hpEq : c p = d p :=
          ih (G.dist root p) (by omega) p rfl
        have hpa : G.Adj p a := TreePartition.parent_adj hG root ha
        have hcne : c p ≠ c a := c.valid hpa
        have hdne : d p ≠ d a := d.valid hpa
        apply Fin.ext
        have hpVal : (c p).val = (d p).val := congrArg Fin.val hpEq
        have hcVal : (c p).val ≠ (c a).val := by
          intro heq
          exact hcne (Fin.ext heq)
        have hdVal : (d p).val ≠ (d a).val := by
          intro heq
          exact hdne (Fin.ext heq)
        have hcp := (c p).isLt
        have hca := (c a).isLt
        have hdp := (d p).isLt
        have hda := (d a).isLt
        omega

universe v

variable {V : Type v} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Canonical branch parity on a marked segment is its intrinsic tree
two-coloring rooted at the segment root. -/
theorem segmentEndpointSide_eq_coloringTwoOfVert
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    segmentEndpointSide hT P optional i j a =
      ((AllocationHierarchy hT P optional).segments.isTree i).coloringTwoOfVert
        ((AllocationHierarchy hT P optional).segments.root i) a := by
  let F := AllocationHierarchy hT P optional
  let sourceColor : (F.segments.tree i).Coloring (Fin 2) :=
    SimpleGraph.Coloring.mk
      (fun x => canonicalBranchSide P j
        (wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional) (Sum.inr ⟨i, x⟩))) (by
        intro x y hxy
        exact canonicalBranchSide_ne_of_adj hT P j
          (segmentInternal_original_adj hT P optional i x y hxy))
  let intrinsic := (F.segments.isTree i).coloringTwoOfVert (F.segments.root i)
  have hroot : sourceColor (F.segments.root i) =
      intrinsic (F.segments.root i) := by
    have hsource : sourceColor (F.segments.root i) =
        segmentEndpointSide hT P optional i j (F.segments.root i) := by
      rfl
    have hside := segmentEndpointSide_root_zero_of_optionalParity
      hT P optional hparity i j hclass
    have hintrinsic : intrinsic (F.segments.root i) = 0 := by
      exact coloringTwoOfVert_root
        (F.segments.tree i) (F.segments.isTree i) (F.segments.root i)
    exact hsource.trans (hside.trans hintrinsic.symm)
  have heq := finTwoColoring_eq_of_root
    (F.segments.isTree i) (F.segments.root i)
    sourceColor intrinsic hroot a
  have hsource : sourceColor a = segmentEndpointSide hT P optional i j a := by
    rfl
  have hintrinsic : intrinsic a =
      ((AllocationHierarchy hT P optional).segments.isTree i).coloringTwoOfVert
        ((AllocationHierarchy hT P optional).segments.root i) a := by
    rfl
  exact hsource.symm.trans (heq.trans hintrinsic)

end Erdos547b.ZhaoClaim616CoordinateSegmentColor

#print axioms Erdos547b.ZhaoClaim616CoordinateSegmentColor.segmentEndpointSide_eq_coloringTwoOfVert
