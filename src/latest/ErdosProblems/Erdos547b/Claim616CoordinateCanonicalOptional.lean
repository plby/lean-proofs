/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateCutParents
import ErdosProblems.Erdos547b.Claim616CoordinateSegmentSmall

/-!
# Canonical optional marks for the coordinate Claim 6.16 hierarchy

The final rich application always marks the recorded Zhao cut parents.  This
small interface fixes that choice and exposes its cardinal, parity, attachment,
and segment-size consequences without leaving an arbitrary optional set at the
public boundary.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateCanonicalOptional

open Finset
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateCutParents
open Erdos547b.ZhaoClaim616CoordinateSegmentSmall

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- The source-faithful optional set: exactly the recorded cut parents. -/
abbrev canonicalOptional
    (P : ZhaoForestPartition T globalRoot small) : Finset V :=
  cutParentVertices P

theorem canonicalOptional_card_le_numParts
    (P : ZhaoForestPartition T globalRoot small) :
    #(canonicalOptional P) ≤ P.numParts :=
  card_cutParentVertices_le_numParts P

theorem canonicalOptional_parity
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small) :
    OptionalBranchRootParity P (canonicalOptional P) :=
  cutParentVertices_optionalBranchRootParity hT P

theorem canonicalOptional_covers_cutParents
    (P : ZhaoForestPartition T globalRoot small) :
    cutParentVertices P ⊆ canonicalOptional P :=
  fun _ hx ↦ hx

theorem canonicalOptional_segment_size_le_small
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : SegmentIndex hT P (canonicalOptional P)) :
    (AllocationHierarchy hT P (canonicalOptional P)).segments.size i ≤ small :=
  allocationHierarchy_segment_size_le_small hT P hsmall
    (canonicalOptional P) S i

end Erdos547b.ZhaoClaim616CoordinateCanonicalOptional

#print axioms Erdos547b.ZhaoClaim616CoordinateCanonicalOptional.canonicalOptional_parity
#print axioms Erdos547b.ZhaoClaim616CoordinateCanonicalOptional.canonicalOptional_segment_size_le_small
