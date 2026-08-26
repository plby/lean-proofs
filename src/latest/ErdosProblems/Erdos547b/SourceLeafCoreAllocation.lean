/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLeafCoreNumerics
import ErdosProblems.Erdos547b.TwoRowSurplusAllocation

/-! # The actual two matching allocations for the leaf-deleted core -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLeafCoreAllocation

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceLeafCoreNumerics Erdos547b.ZhaoSourceLeafCoreMass
open Erdos547b.ZhaoSourceReconnectedTwoRowCopy Erdos547b.ZhaoTwoRowSurplusAllocation
open Erdos547b.ZhaoSourceLeafBranchRestriction Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoClaim68ConcreteLeaves
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyAttachments Erdos547b.ZhaoLemma611Full

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ} (P : ZhaoForestPartition T globalRoot small)

abbrev coreForest := OrderedBranchForest.restrict (branchForest P) (keptBranches P)

def coreMass (s : Fin 2) : ℝ :=
  ∑ i ∈ sideFamily (coreForest P) (componentReservoirSide P) s, ((coreForest P).branches.size i : ℝ)

theorem coreMass_nonneg (s : Fin 2) : 0 ≤ coreMass P s :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem coreMass_sum : coreMass P 0 + coreMass P 1 = (OrderedBranchForest.edgeDemand (coreForest P) : ℝ) := by
  rw [coreMass, coreMass, sum_sideFamily_zero_add_one]
  simp only [OrderedBranchForest.edgeDemand, Nat.cast_sum]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q) (hT : T.IsTree)

include hT in
theorem exists_coreAllocation
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hleaves : 11 * (fourthRoot α : ℝ) ^ 2 * q ≤ (originalLevelOneLeaves P).card) :
    ∃ E : Fin 2 → Finset (MatchingEdge Q.claim67.M),
      Disjoint (E 0) (E 1) ∧ (∀ s, E s ⊆ awayEdges W Q) ∧
      ∀ s, coreMass P s + 3 * (gamma α : ℝ) * q ≤ ∑ e ∈ E s, sideWeight W Q S s e := by
  have hsurplus (s : Fin 2) : coreMass P 0 + coreMass P 1 +
      2 * (3 * (gamma α : ℝ) * q) + 2 * (2 * (W.clusterSize : ℝ)) ≤
        ∑ e ∈ awayEdges W Q, sideWeight W Q S s e := by
    rw [coreMass_sum]
    exact core_row_surplus W Q S P hT hα hα1 hhost horder hcard hleaves s
  have hγ : (0 : ℝ) ≤ gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1.le
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  obtain ⟨Ea, Eb, hEa, hEb, hdis, _, ha, hb⟩ := exists_twoRowSurplus (awayEdges W Q)
    (sideWeight W Q S 0) (sideWeight W Q S 1) (coreMass P 0) (coreMass P 1) (3 * (gamma α : ℝ) * q)
    (2 * W.clusterSize) (fun e _ => sideWeight_nonneg W Q S 0 e) (fun e _ => sideWeight_nonneg W Q S 1 e)
    (fun e _ => sideWeight_le W Q S 0 e) (fun e _ => sideWeight_le W Q S 1 e)
    (coreMass_nonneg P 0) (coreMass_nonneg P 1) (by positivity) (by positivity)
    (hsurplus 0) (hsurplus 1)
  exact ⟨![Ea, Eb], hdis, (by intro s; fin_cases s; exact hEa; exact hEb),
    (by intro s; fin_cases s; exact ha.le; exact hb.le)⟩

end Erdos547b.ZhaoSourceLeafCoreAllocation

#print axioms Erdos547b.ZhaoSourceLeafCoreAllocation.coreMass_sum
#print axioms Erdos547b.ZhaoSourceLeafCoreAllocation.exists_coreAllocation
