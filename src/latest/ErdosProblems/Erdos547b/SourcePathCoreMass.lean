/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePathCoreGraph
import ErdosProblems.Erdos547b.SourceLeafCoreMass

/-! # Exact source mass of the literal postponed-path core -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePathCoreMass

open Finset SimpleGraph Erdos547b.TreePartition Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoSourcePathCoreGraph Erdos547b.ZhaoSourcePathBranchRestriction
open Erdos547b.ZhaoClaim617CleanLoss Erdos547b.ZhaoClaim617CleanSelection
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyAttachments Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoSourceReconnectedTwoRowCopy Erdos547b.ZhaoSourceLeafCoreMass

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small p : ℕ} (P : ZhaoForestPartition T globalRoot small)
variable (hp : p ≤ (cleanBranches P).card)

abbrev coreForest := OrderedBranchForest.restrict (branchForest P) (keptBranches P hp)

def coreMass (s : Fin 2) : ℝ :=
  ∑ i ∈ sideFamily (coreForest P hp) (componentReservoirSide P) s,
    ((coreForest P hp).branches.size i : ℝ)

theorem coreMass_nonneg (s : Fin 2) : 0 ≤ coreMass P hp s :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem coreMass_sum : coreMass P hp 0 + coreMass P hp 1 =
    (OrderedBranchForest.edgeDemand (coreForest P hp) : ℝ) := by
  rw [coreMass, coreMass, sum_sideFamily_zero_add_one]
  simp only [OrderedBranchForest.edgeDemand, Nat.cast_sum]

variable (hT : T.IsTree)

include hT in
theorem retained_vertex_count : P.numParts + OrderedBranchForest.edgeDemand (coreForest P hp) +
    2 * p = Fintype.card U := by
  have h := Fintype.card_congr (pathCoreGraphIso P hp hT
    (sideLocate (branchForest P) (componentReservoirSide P)) (fun _ => rfl)).toEquiv
  simp only [OrderedBranchForest.Vertex, Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma] at h
  have hc := selectedCore_card P hp
  change _ = P.numParts + OrderedBranchForest.edgeDemand (coreForest P hp) at h
  omega

include hT in
theorem retained_mass_le {q : ℕ} (hcard : Fintype.card U = q + 1) :
    (OrderedBranchForest.edgeDemand (coreForest P hp) : ℝ) + 2 * p ≤ q := by
  have h := retained_vertex_count P hp hT
  have hpos := P.numParts_pos
  have hnat : OrderedBranchForest.edgeDemand (coreForest P hp) + 2 * p ≤ q := by omega
  exact_mod_cast hnat

include hT in
theorem coreMass_sum_add_paths_le {q : ℕ} (hcard : Fintype.card U = q + 1) :
    coreMass P hp 0 + coreMass P hp 1 + 2 * p ≤ q := by
  rw [coreMass_sum]
  exact retained_mass_le P hp hT hcard

end Erdos547b.ZhaoSourcePathCoreMass

#print axioms Erdos547b.ZhaoSourcePathCoreMass.retained_vertex_count
#print axioms Erdos547b.ZhaoSourcePathCoreMass.coreMass_sum_add_paths_le
