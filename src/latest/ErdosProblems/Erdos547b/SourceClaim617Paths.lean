/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim617CleanCount
import ErdosProblems.Erdos547b.Claim617CleanSelection

/-! The literal postponed core supplied by the source host estimates. -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClaim617Paths

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoSourceClaim617CleanCount Erdos547b.ZhaoSourceClaim617PathNumerics
open Erdos547b.ZhaoClaim617CleanLoss Erdos547b.ZhaoClaim617CleanSelection
open Erdos547b.ZhaoClaim68 Erdos547b.ZhaoClaim68ParityHalf

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (O : Output W Q S (branchMass P (sideBranches P 1)))

include hT in
theorem exists_postponedCore
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G)
    (hcross : (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card) :
    ∃ hp : postponedCount α q ≤ (cleanBranches P).card,
      Nonempty {x // x ∉ (selectedPaths P hp).middleSet} ∧
      (selectedPaths P hp).core.IsTree ∧
      Fintype.card {x // x ∉ (selectedPaths P hp).middleSet} +
        2 * postponedCount α q = q + 1 ∧
      ∀ i, (selectedPaths P hp).parent i = P.roots (selectedRootIndex P hp i) ∧
        T.dist globalRoot ((selectedPaths P hp).parent i) % 2 = (majorParity P).val ∧
        (selectedPaths P hp).middle i ∉ partitionRoots P ∧
        (selectedPaths P hp).leaf i ∉ partitionRoots P ∧
        (selectedPaths P hp).middle i ∉ partitionParents P ∧
        (selectedPaths P hp).leaf i ∉ partitionParents P := by
  let hp := postponedCount_le_cleanBranches W Q S hT P O hα hα1 hhost horder hcard hnot hcross
  refine ⟨hp, ⟨selectedCoreRoot P hT hp⟩, selectedCore_isTree P hT hp,
    (selectedCore_card P hp).trans hcard, ?_⟩
  intro i
  exact ⟨selectedPaths_parent P hp i, selectedPaths_parent_parity P hp i,
    selectedPaths_middle_not_root P hp i, selectedPaths_leaf_not_root P hp i,
    selectedPaths_middle_not_parent P hp i, selectedPaths_leaf_not_parent P hp i⟩

end Erdos547b.ZhaoSourceClaim617Paths

#print axioms Erdos547b.ZhaoSourceClaim617Paths.exists_postponedCore
