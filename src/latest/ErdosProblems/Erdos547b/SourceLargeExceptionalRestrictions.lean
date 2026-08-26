/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLargeExceptionalForcing
import ErdosProblems.Erdos547b.SourceRawDiscrepancy

/-!
# Exceptional-family restrictions in the large-minor case

Noncontainment supplies the raw-row discrepancy through its proved
allocation argument. A large exceptional family then constructs the
forbidden complete tree. Only the source forest-mass claim remains an
input here; no degree budget or embedding continuation is assumed.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLargeExceptionalRestrictions

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceLargeExceptionalForcing Erdos547b.ZhaoSourceRawDiscrepancy
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem unbalancedAway_card_lt_of_largeMinor
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hminor : (fourthRoot α : ℝ) * q ≤ (branchMass P (sideBranches P 1) : ℝ))
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (hnot : ¬Nonempty (T.Copy (embeddingHost W))) (s : Fin 2)
    (hmass : (α : ℝ) / 32 * q ≤ (branchMass P (balancedSideBranches P s ((α : ℝ) / 16)) : ℝ)) :
    ((unbalancedAway W Q S s).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W) := by
  apply lt_of_not_ge
  intro hfamily
  exact hnot (exists_treeCopy_of_largeUnbalancedFamily W Q S hT P hα hα1 hhost horder hcard
    s hfamily hmass
    (fun R hR => (raw_discrepancy_lt_anySide W Q S hT P hα hα1 hhost horder hcard
      hminor hsmall hroots hnot s R hR).le) hsmall hroots)

include hT in
theorem nonextremeAway_card_lt_of_largeMinor
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hminor : (fourthRoot α : ℝ) * q ≤ (branchMass P (sideBranches P 1) : ℝ))
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (hnot : ¬Nonempty (T.Copy (embeddingHost W))) (s : Fin 2)
    (hmass : (q : ℝ) / 2 - 12 * (fourthRoot α : ℝ) ^ 2 * q ≤
      (branchMass P (nontrivialSideBranches P s) : ℝ)) :
    ((nonextremeAway W Q S s).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W) := by
  apply lt_of_not_ge
  intro hfamily
  exact hnot (exists_treeCopy_of_largeNonextremeFamily W Q S hT P hα hα1 hhost horder hcard
    s hfamily hmass
    (fun R hR => (raw_discrepancy_lt_anySide W Q S hT P hα hα1 hhost horder hcard
      hminor hsmall hroots hnot s R hR).le) hsmall hroots)

end Erdos547b.ZhaoSourceLargeExceptionalRestrictions

#print axioms Erdos547b.ZhaoSourceLargeExceptionalRestrictions.unbalancedAway_card_lt_of_largeMinor
#print axioms Erdos547b.ZhaoSourceLargeExceptionalRestrictions.nonextremeAway_card_lt_of_largeMinor
