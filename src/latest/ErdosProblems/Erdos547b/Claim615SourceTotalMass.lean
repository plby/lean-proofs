/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615SourceMass

/-!
# Total source mass of the Claim-6.15 branch forest

The branch coordinates are equivalent to the literal nonroot vertices of the
Zhao partition.  Consequently the total branch demand is exactly the tree
order minus the number of component roots.  This is the source accounting
identity used when the three physical packing budgets are added together.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615SourceTotalMass

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoLemma59Part2Full

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The total ordered-branch demand counts the literal nonroot vertices. -/
theorem edgeDemand_branchForest_eq_card_partitionNonroots
    (P : ZhaoForestPartition T globalRoot small) :
    OrderedBranchForest.edgeDemand (branchForest P) =
      (partitionNonroots P).card := by
  have hcard := Fintype.card_congr (partitionBranchEquivNonroots P)
  simp only [Fintype.card_sigma, Fintype.card_fin, Fintype.card_coe] at hcard
  simpa only [OrderedBranchForest.edgeDemand] using hcard

/-- Restoring the one root of each partition component recovers every tree
vertex. -/
theorem edgeDemand_branchForest_add_numParts
    (P : ZhaoForestPartition T globalRoot small) :
    OrderedBranchForest.edgeDemand (branchForest P) + P.numParts =
      Fintype.card V := by
  rw [edgeDemand_branchForest_eq_card_partitionNonroots]
  exact card_partitionNonroots_add_numParts P

/-- In particular the total physical source demand is at most the tree
order. -/
theorem edgeDemand_branchForest_le_card
    (P : ZhaoForestPartition T globalRoot small) :
    OrderedBranchForest.edgeDemand (branchForest P) ≤ Fintype.card V := by
  have h := edgeDemand_branchForest_add_numParts P
  omega

/-- The branch mass of the canonical major parity half is the cardinality of
the corresponding literal vertex part. -/
theorem branchMass_halfBranches_eq_majorPart_card
    (P : ZhaoForestPartition T globalRoot small) :
    branchMass P (halfBranches P) = (majorPart P).card := by
  symm
  exact majorPart_card_eq_halfBranchMass P

/-- The same identification for the complementary parity half. -/
theorem branchMass_minorBranches_eq_minorPart_card
    (P : ZhaoForestPartition T globalRoot small) :
    branchMass P (minorBranches P) = (minorPart P).card := by
  have hbranch :
      branchMass P (halfBranches P) + branchMass P (minorBranches P) =
        OrderedBranchForest.edgeDemand (branchForest P) := by
    rw [branchMass, branchMass, OrderedBranchForest.edgeDemand,
      ← Finset.sum_union (halfBranches_disjoint_minorBranches P),
      halfBranches_union_minorBranches]
  have hvertex :
      (majorPart P).card + (minorPart P).card =
        (partitionNonroots P).card := by
    rw [← Finset.card_union_of_disjoint (major_minor_disjoint P),
      major_union_minor P]
  rw [edgeDemand_branchForest_eq_card_partitionNonroots,
    branchMass_halfBranches_eq_majorPart_card] at hbranch
  omega

/-- The source forest rooted on `B` is no larger than the canonical major
half rooted on `A`. -/
theorem branchMass_minor_le_half
    (P : ZhaoForestPartition T globalRoot small) :
    branchMass P (minorBranches P) ≤ branchMass P (halfBranches P) := by
  rw [branchMass_minorBranches_eq_minorPart_card,
    branchMass_halfBranches_eq_majorPart_card]
  exact minor_card_le_major_card P

end Erdos547b.ZhaoClaim615SourceTotalMass

#print axioms Erdos547b.ZhaoClaim615SourceTotalMass.edgeDemand_branchForest_eq_card_partitionNonroots
#print axioms Erdos547b.ZhaoClaim615SourceTotalMass.edgeDemand_branchForest_add_numParts
#print axioms Erdos547b.ZhaoClaim615SourceTotalMass.branchMass_minor_le_half
