/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedBudgetTreeCopy
import ErdosProblems.Erdos547b.SourceSelectedMarkedBudgets
import ErdosProblems.Erdos547b.Claim616CoordinateSourceParity

/-!
# The actual selected F0 supplies every marked source budget

Only the explicit ordinary residual allocations and their scalar capacities
remain as inputs. Mark counts, branch scale, selected mass, owner sides and
the number of roots follow from the same literal fresh partition.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSelectedMarkedTreeCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.TreePartition
open Erdos547b.ZhaoSourceMarkedTerminalTreeCopy Erdos547b.ZhaoSourceSelectedMarkedBudgets
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceFreshPartitionBounds
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceClaim616Selection
open Erdos547b.ZhaoSourceCrossingClusters Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchyClassification Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616CoordinateSourceParity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U}
variable (sourceP : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (F : SelectedF0Within (branchForest sourceP) (halfBranches sourceP)
  (selectionTarget W Q S O C) (freshBranchBound α W.clusterSize))
variable {k : ℕ} (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin (Fintype.card (ChildKey sourceP.orderedForest))))
variable (locate : Fin (Fintype.card (ChildKey sourceP.orderedForest)) → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∉ F.selected → i ∈ family (locate i).1 (locate i).2)
variable (hlocate : ∀ i, (locate i).1 = componentReservoirSide sourceP ((branchForest sourceP).owner i))

include P hT locate hcover hlocate in
theorem exists_treeCopy_of_residualBudgets
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hk : k ≤ 3) (hCV1 : C ⊆ O.D.V1) (hCcard : C.card = crossingScale W)
    (hkind : ∀ s j, (kinds s j).Valid α)
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => (branchForest sourceP).owner i ≤ (branchForest sourceP).owner j))
    (hside : ∀ s j i, i ∈ family s j → componentReservoirSide sourceP ((branchForest sourceP).owner i) = s)
    (hbranch : ∀ s j, ∀ i ∈ family s j, (kinds s j).BranchValid (branchForest sourceP).branches i)
    (hedge : ∀ s j, ∀ e ∈ allocation s j, edgeValid W Q S (rootCluster W Q s) (kinds s j) e)
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
    (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hresidual : ∀ s j e, e ∈ allocation s j →
      e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges)
    (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (allocation s)).card ≤ globalCount)
    (hbudget : ∀ s j, family s j ≠ [] → mass (fun i => ((branchForest sourceP).branches.size i : ℝ)) (family s j) ≤
      (∑ e ∈ allocation s j, capacity W Q S (rootCluster W Q s) (kinds s j) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (allocation s j).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount) :
    Nonempty (T.Copy (embeddingHost W)) := by
  have hC : 0 < C.card := hCcard.symm ▸ (scale_bounds W Q S O hα hα1 hhost horder).1
  have hroots : (sourceP.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
    subst hostN
    exact freshPartition_root_bound hα hα1 W horder hcard sourceP
  exact exists_treeCopy_of_sourceBudgets W Q S O P hT sourceP F.selected kinds allocation family locate hcover hlocate
    hα hα1 hhost horder hk hCV1 hC hkind hnd hordered hside
    (componentReservoirSide_owner_eq_zero_of_mem_selected sourceP F)
    hbranch hedge (canonical_branch_size_le_small sourceP) hdisjoint haway hresidual globalCount hglobal hbudget
    (fun i hi => (selected_branch_bounds W Q S O C sourceP F i hi).1)
    (prefix_marks_bound W sourceP hα hα1 hhost horder hcard F.selected)
    (prefix_mass_bound W Q S O C sourceP hα hα1 hhost horder hCcard F F.selected (Finset.Subset.refl _)).le hroots

end Erdos547b.ZhaoSourceSelectedMarkedTreeCopy

#print axioms Erdos547b.ZhaoSourceSelectedMarkedTreeCopy.exists_treeCopy_of_residualBudgets
