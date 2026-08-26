/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedResidualAllocation
import ErdosProblems.Erdos547b.SourceMarkedTwoRowTreeCopy
import ErdosProblems.Erdos547b.SourceRawDiscrepancy

/-!
# Claim 6.16 from the actual source host

Dense reduced crossing edges and too much large-branch mass construct the
forbidden whole tree. Both minor-family cases are handled by the literal
residual allocation; no graph embedding continuation is assumed.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClaim616FromHost

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceMarkedResidualAllocation Erdos547b.ZhaoSourceMarkedTwoRowTreeCopy
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceRawDiscrepancy
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceClaim616Selection
open Erdos547b.ZhaoSourceCrossingClusters Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceFreshPartitionBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim616HierarchyClassification Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U}
variable (sourceP : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (O : Output W Q S (branchMass sourceP (sideBranches sourceP 1)))

include hT in
theorem largeHalfMass_lt_of_crossing
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬Nonempty (T.Copy (embeddingHost W)))
    (hcross : (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card) :
    (largeHalfMass sourceP : ℝ) < 3 * (crossingScale W : ℝ) * W.clusterSize := by
  by_contra hmass
  have hmass' := le_of_not_gt hmass
  obtain ⟨C, hCV1, _, hCcard, ⟨P⟩⟩ := exists_geometry W Q S O hα hα1 hhost horder hcross
  obtain ⟨F, _, _, _⟩ := exists_selectedForest W Q S O C sourceP hα hα1 hhost horder hCcard
    (canonical_branch_size_le_small sourceP) hmass'
  have hroots : (sourceP.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
    subst hostN
    exact freshPartition_root_bound hα hα1 W horder hcard sourceP
  obtain ⟨E, hdisjoint, haway, hresidual, hbudget⟩ :=
    exists_residualAllocation W Q S O C sourceP F hα hα1 hhost horder hcard rfl (by
      intro hlarge R hR
      have hd := raw_discrepancy_lt_of_not_copy W Q S hT sourceP hα hα1 hhost horder hcard
        (le_of_not_gt hlarge) (canonical_branch_size_le_small sourceP) hroots hnot R
        (hR.trans (O.min_subset_away W Q S))
      exact (le_abs_self _).trans hd.le)
  exact hnot (exists_treeCopy_of_twoRowBudgets W Q S O P hT sourceP F hα hα1 hhost horder hcard
    hCV1 hCcard E hdisjoint haway hresidual (fun s _ => hbudget s))

end Erdos547b.ZhaoSourceClaim616FromHost

#print axioms Erdos547b.ZhaoSourceClaim616FromHost.largeHalfMass_lt_of_crossing
