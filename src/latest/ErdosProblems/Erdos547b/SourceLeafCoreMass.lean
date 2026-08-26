/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLeafCoreGraph
import ErdosProblems.Erdos547b.SourceReconnectedTwoRowCopy

/-!
# Exact source-order saving for the literal leaf-deleted core
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLeafCoreMass

open Finset SimpleGraph Erdos547b.TreePartition Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoSourceReconnectedTwoRowCopy Erdos547b.ZhaoSourceLeafCoreGraph
open Erdos547b.ZhaoSourceLeafBranchRestriction Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim68ConcreteLeaves Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyAttachments

theorem sum_sideFamily_zero_add_one {r b : ℕ} (F : OrderedBranchForest r b)
    (rootSide : Fin r → Fin 2) (w : Fin b → ℝ) :
    (∑ i ∈ sideFamily F rootSide 0, w i) + (∑ i ∈ sideFamily F rootSide 1, w i) = ∑ i, w i := by
  have hdis : Disjoint (sideFamily F rootSide 0) (sideFamily F rootSide 1) := by
    apply Finset.disjoint_left.mpr
    intro i h0 h1
    have hzero := (Finset.mem_filter.mp h0).2
    have hone := (Finset.mem_filter.mp h1).2
    have h : (0 : Fin 2) = 1 := hzero.symm.trans hone
    exact (by decide : (0 : Fin 2) ≠ 1) h
  have hunion : sideFamily F rootSide 0 ∪ sideFamily F rootSide 1 = Finset.univ := by
    ext i
    simp only [sideFamily, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one _
  rw [← Finset.sum_union hdis, hunion]

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ} (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)

include hT in
theorem retained_vertex_count : P.numParts +
    OrderedBranchForest.edgeDemand (OrderedBranchForest.restrict (branchForest P) (keptBranches P)) +
      (originalLevelOneLeaves P).card = Fintype.card U := by
  have h := Fintype.card_congr (leafCoreGraphIso P hT
    (sideLocate (branchForest P) (componentReservoirSide P)) (fun _ => rfl)).toEquiv
  change Fintype.card (LeafDeletedVertex P) =
    Fintype.card (OrderedBranchForest.restrict (branchForest P) (keptBranches P)).Vertex at h
  simp only [OrderedBranchForest.Vertex, Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma] at h
  rw [card_leafDeletedVertex] at h
  have hle : (originalLevelOneLeaves P).card ≤ Fintype.card U := Finset.card_le_univ _
  change Fintype.card U - (originalLevelOneLeaves P).card =
    P.numParts + OrderedBranchForest.edgeDemand (OrderedBranchForest.restrict (branchForest P) (keptBranches P)) at h
  omega

include hT in
theorem retained_mass_le {q : ℕ} (hcard : Fintype.card U = q + 1) :
    (OrderedBranchForest.edgeDemand (OrderedBranchForest.restrict (branchForest P) (keptBranches P)) : ℝ) +
      (originalLevelOneLeaves P).card ≤ q := by
  have h := retained_vertex_count P hT
  have hpos := P.numParts_pos
  have hnat : OrderedBranchForest.edgeDemand (OrderedBranchForest.restrict (branchForest P) (keptBranches P)) +
      (originalLevelOneLeaves P).card ≤ q := by omega
  exact_mod_cast hnat

end Erdos547b.ZhaoSourceLeafCoreMass

#print axioms Erdos547b.ZhaoSourceLeafCoreMass.sum_sideFamily_zero_add_one
#print axioms Erdos547b.ZhaoSourceLeafCoreMass.retained_vertex_count
#print axioms Erdos547b.ZhaoSourceLeafCoreMass.retained_mass_le
