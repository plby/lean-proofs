/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFamilyCapacity
import ErdosProblems.Erdos547b.Claim615SourceSelection
import ErdosProblems.Erdos547b.Claim616HierarchyAttachments
import ErdosProblems.Erdos547b.SourceTwoSideFamilyAdvance
import ErdosProblems.Erdos547b.Claim615SourceTotalMass

/-!
# The literal three source families in the exceptional case

The selected family may lie on either root side. Its complement on that
side and the whole opposite side complete a covering decomposition.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceExceptionalFamilies

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceTwoSideFamilyAdvance
open Erdos547b.ZhaoClaim616ResidualAllocation (minorBranches
  halfBranches_union_minorBranches halfBranches_disjoint_minorBranches)

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

def sideBranches (s : Fin 2) : Finset (BranchIndex P) :=
  Finset.univ.filter fun i => componentReservoirSide P ((branchForest P).owner i) = s

@[simp] theorem mem_sideBranches (s : Fin 2) (i : BranchIndex P) :
    i ∈ sideBranches P s ↔ componentReservoirSide P ((branchForest P).owner i) = s := by
  simp only [sideBranches, Finset.mem_filter, Finset.mem_univ, true_and]

theorem sideBranches_disjoint (s : Fin 2) :
    Disjoint (sideBranches P s) (sideBranches P (otherSide s)) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  exact otherSide_ne s ((mem_sideBranches P _ i).mp hj |>.symm.trans ((mem_sideBranches P _ i).mp hi))

theorem mem_sideBranches_or_other (s : Fin 2) (i : BranchIndex P) :
    i ∈ sideBranches P s ∨ i ∈ sideBranches P (otherSide s) := by
  simp only [mem_sideBranches]
  generalize componentReservoirSide P ((branchForest P).owner i) = t
  fin_cases s <;> fin_cases t <;> decide

@[simp] theorem sideBranches_zero : sideBranches P 0 = halfBranches P := by
  ext i
  simp [sideBranches, componentReservoirSide, halfBranches]

@[simp] theorem sideBranches_one : sideBranches P 1 = minorBranches P := by
  have hcover := halfBranches_union_minorBranches P
  have hdisjoint := halfBranches_disjoint_minorBranches P
  ext i
  have hm : i ∈ halfBranches P ∨ i ∈ minorBranches P := by
    rw [← Finset.mem_union, hcover]
    exact Finset.mem_univ i
  have hn : ¬(i ∈ halfBranches P ∧ i ∈ minorBranches P) := by
    rintro ⟨hi, hj⟩
    exact Finset.disjoint_left.mp hdisjoint hi hj
  have hside : i ∈ sideBranches P 1 ↔ i ∉ halfBranches P := by
    simp [sideBranches, componentReservoirSide, halfBranches]
  rw [hside]
  tauto

def balancedSideBranches (s : Fin 2) (ratio : ℝ) : Finset (BranchIndex P) :=
  (sideBranches P s).filter fun i => ratio < branchRatio P i ∧ branchRatio P i < 1 - ratio

def nontrivialSideBranches (s : Fin 2) : Finset (BranchIndex P) :=
  (sideBranches P s).filter fun i => 2 ≤ (branchForest P).branches.size i

@[simp] theorem balancedSideBranches_zero (ratio : ℝ) :
    balancedSideBranches P 0 ratio = balancedMajorBranches P ratio := by
  simp only [balancedSideBranches, balancedMajorBranches, sideBranches_zero]

@[simp] theorem nontrivialSideBranches_zero :
    nontrivialSideBranches P 0 = nontrivialMajorBranches P := by
  simp only [nontrivialSideBranches, nontrivialMajorBranches, sideBranches_zero]

theorem branchRatio_eq (i : BranchIndex P) :
    branchRatio P i =
      (#(Erdos547b.ZhaoLemma58GroupedSmallForest.colourClass (branchForest P).branches i 0) : ℝ) /
        (branchForest P).branches.size i := rfl

theorem balancedSide_branchValid (s : Fin 2) (ratio : ℝ)
    (i : BranchIndex P) (hi : i ∈ balancedSideBranches P s ratio) :
    FamilyKind.BranchValid (.threshold ratio) (branchForest P).branches i := by
  have h := (Finset.mem_filter.mp hi).2
  exact ⟨h.1.le, h.2.le⟩

theorem nontrivialSide_branchValid (s : Fin 2) (lambda : ℝ)
    (i : BranchIndex P) (hi : i ∈ nontrivialSideBranches P s) :
    FamilyKind.BranchValid (.appendix lambda) (branchForest P).branches i :=
  (Finset.mem_filter.mp hi).2

/-- Exceptional, same-side residual, and opposite-side families. -/
def exceptionalFamilies (s : Fin 2) (selected : Finset (BranchIndex P)) :
    Fin 3 → Finset (BranchIndex P) :=
  ![selected, sideBranches P s \ selected, sideBranches P (otherSide s)]

def exceptionalTags (s : Fin 2) : Fin 3 → Fin 2 := ![s, s, otherSide s]

theorem exceptionalFamilies_cover (s : Fin 2) (selected : Finset (BranchIndex P))
    (i : BranchIndex P) : ∃ j, i ∈ exceptionalFamilies P s selected j := by
  by_cases hi : i ∈ selected
  · exact ⟨0, hi⟩
  · rcases mem_sideBranches_or_other P s i with hs | ht
    · exact ⟨1, Finset.mem_sdiff.mpr ⟨hs, hi⟩⟩
    · exact ⟨2, ht⟩

theorem exceptionalFamilies_side (s : Fin 2) (selected : Finset (BranchIndex P))
    (hselected : selected ⊆ sideBranches P s) (j : Fin 3) (i : BranchIndex P)
    (hi : i ∈ exceptionalFamilies P s selected j) :
    componentReservoirSide P ((branchForest P).owner i) = exceptionalTags s j := by
  fin_cases j
  · exact (mem_sideBranches P s i).mp (hselected hi)
  · exact (mem_sideBranches P s i).mp (Finset.mem_sdiff.mp hi).1
  · exact (mem_sideBranches P (otherSide s) i).mp hi

theorem sideBranches_union (s : Fin 2) :
    sideBranches P s ∪ sideBranches P (otherSide s) = Finset.univ := by
  ext i
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  exact mem_sideBranches_or_other P s i

/-- Literal branch mass is conserved by the selected/residual split. -/
theorem exceptional_mass_eq (s : Fin 2) (selected : Finset (BranchIndex P))
    (hselected : selected ⊆ sideBranches P s) :
    branchMass P selected + branchMass P (sideBranches P s \ selected) +
      branchMass P (sideBranches P (otherSide s)) = branchMass P Finset.univ := by
  have hsplit := Finset.sum_sdiff hselected (f := (branchForest P).branches.size)
  have hunion := Finset.sum_union (sideBranches_disjoint P s) (f := (branchForest P).branches.size)
  rw [sideBranches_union] at hunion
  change branchMass P (sideBranches P s \ selected) + branchMass P selected =
    branchMass P (sideBranches P s) at hsplit
  change branchMass P Finset.univ = branchMass P (sideBranches P s) +
    branchMass P (sideBranches P (otherSide s)) at hunion
  omega

/-- At tree order q+1 at least one component root is removed, so the
three family's combined branch demand is at most q, not q+1. -/
theorem exceptional_mass_le {q : ℕ} (hcard : Fintype.card U = q + 1)
    (s : Fin 2) (selected : Finset (BranchIndex P))
    (hselected : selected ⊆ sideBranches P s) :
    (branchMass P selected : ℝ) + (branchMass P (sideBranches P s \ selected) : ℝ) +
      (branchMass P (sideBranches P (otherSide s)) : ℝ) ≤ q := by
  have htotal := Erdos547b.ZhaoClaim615SourceTotalMass.edgeDemand_branchForest_add_numParts P
  have hpos := P.numParts_pos
  change branchMass P Finset.univ + P.numParts = Fintype.card U at htotal
  rw [hcard] at htotal
  have hnat : branchMass P selected + branchMass P (sideBranches P s \ selected) +
      branchMass P (sideBranches P (otherSide s)) ≤ q := by
    rw [exceptional_mass_eq P s selected hselected]
    omega
  exact_mod_cast hnat

end Erdos547b.ZhaoSourceExceptionalFamilies

#print axioms Erdos547b.ZhaoSourceExceptionalFamilies.balancedSide_branchValid
#print axioms Erdos547b.ZhaoSourceExceptionalFamilies.exceptionalFamilies_cover
#print axioms Erdos547b.ZhaoSourceExceptionalFamilies.exceptionalFamilies_side
#print axioms Erdos547b.ZhaoSourceExceptionalFamilies.exceptional_mass_le
