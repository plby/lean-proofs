/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSelectedMarkedBudgets
import ErdosProblems.Erdos547b.SourceExceptionalFamilies

/-!
# Literal source masses and saving of the selected marked forest
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedResidualSource

open Finset SimpleGraph Erdos547b.TreePartition Erdos547b.RegularPair
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceClaim616Selection Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoClaim616 Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb) (C : Finset (EvenPadding (Index W)))
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] {globalRoot : U} {small : ℕ}
variable (sourceP : ZhaoForestPartition T globalRoot small)
variable (F : SelectedF0Within (branchForest sourceP) (halfBranches sourceP)
  (selectionTarget W Q S O C) (freshBranchBound α W.clusterSize))

theorem selected_saving :
    (∑ e ∈ MatchingDecomposition.MzeroEdges O.D C, sideWeight W Q S 0 e) +
      (crossingScale W : ℝ) * W.clusterSize / 2 ≤ (branchMass sourceP F.selected : ℝ) := by
  have hlow := F.lower
  rw [OrderedBranchForest.edgeDemand_restrict] at hlow
  have hlowR : (selectionTarget W Q S O C : ℝ) ≤ (branchMass sourceP F.selected : ℝ) := by
    exact_mod_cast hlow
  exact (Nat.le_ceil _).trans hlowR

theorem minorResidual_eq : sideBranches sourceP 1 \ F.selected = sideBranches sourceP 1 := by
  apply Finset.sdiff_eq_self_of_disjoint
  have hselected : F.selected ⊆ sideBranches sourceP 0 := by
    simpa only [sideBranches_zero] using F.selected_available
  have hdis := (sideBranches_disjoint sourceP 0).symm
  exact hdis.mono_right hselected

theorem residual_mass_le (hcard : Fintype.card U = q + 1) :
    (branchMass sourceP F.selected : ℝ) +
      (branchMass sourceP (sideBranches sourceP 0 \ F.selected) : ℝ) +
      (branchMass sourceP (sideBranches sourceP 1 \ F.selected) : ℝ) ≤ q := by
  rw [minorResidual_eq W Q S O C sourceP F]
  exact exceptional_mass_le sourceP hcard 0 F.selected (by simpa only [sideBranches_zero] using F.selected_available)

end Erdos547b.ZhaoSourceMarkedResidualSource

#print axioms Erdos547b.ZhaoSourceMarkedResidualSource.selected_saving
#print axioms Erdos547b.ZhaoSourceMarkedResidualSource.minorResidual_eq
#print axioms Erdos547b.ZhaoSourceMarkedResidualSource.residual_mass_le
