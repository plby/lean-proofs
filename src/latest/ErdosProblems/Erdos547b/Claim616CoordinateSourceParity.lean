/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateOrientation
import ErdosProblems.Erdos547b.Claim616HierarchyAttachments

/-!
# Source parity of the coordinate Claim 6.16 branch reservoirs

The owner of a major-half branch uses distinguished reservoir side zero,
whereas the owner of a minor-half branch uses side one.  These are literal
consequences of the canonical parity partition and contain no host data.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateSourceParity

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyAttachments

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

@[simp] theorem componentReservoirSide_owner_eq_zero_of_mem_halfBranches
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P)
    (hj : j ∈ halfBranches P) :
    componentReservoirSide P ((branchForest P).owner j) = 0 := by
  have hparity := (Finset.mem_filter.mp hj).2
  simp [componentReservoirSide, hparity]

@[simp] theorem componentReservoirSide_owner_eq_one_of_mem_minorBranches
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P)
    (hj : j ∈ minorBranches P) :
    componentReservoirSide P ((branchForest P).owner j) = 1 := by
  have hminor := (mem_minorBranches P j).mp hj
  rw [componentReservoirSide, if_neg]
  intro hmajor
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card
  · simp [majorParity, minorParity, h] at hmajor hminor
    omega
  · simp [majorParity, minorParity, h] at hmajor hminor
    omega

@[simp] theorem componentReservoirSide_owner_eq_zero_of_mem_selected
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) (hj : j ∈ S.selected) :
    componentReservoirSide P ((branchForest P).owner j) = 0 := by
  exact componentReservoirSide_owner_eq_zero_of_mem_halfBranches P j
    (S.selected_available hj)

@[simp] theorem componentReservoirSide_owner_eq_zero_of_mem_majorResidual
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) (hj : j ∈ majorResidualBranches P S) :
    componentReservoirSide P ((branchForest P).owner j) = 0 := by
  exact componentReservoirSide_owner_eq_zero_of_mem_halfBranches P j
    ((mem_majorResidualBranches P S j).mp hj).1

end Erdos547b.ZhaoClaim616CoordinateSourceParity

#print axioms Erdos547b.ZhaoClaim616CoordinateSourceParity.componentReservoirSide_owner_eq_zero_of_mem_halfBranches
#print axioms Erdos547b.ZhaoClaim616CoordinateSourceParity.componentReservoirSide_owner_eq_one_of_mem_minorBranches
