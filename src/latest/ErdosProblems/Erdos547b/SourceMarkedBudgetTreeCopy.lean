/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedTerminalTreeCopy

/-!
# A tree copy from explicit marked and ordinary source budgets

The finite cut-prefix induction constructs every root and branch image.
Actual source parent coordinates supply their own protected marks.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedTerminalTreeCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.TreePartition
open Erdos547b.ZhaoSourceMarkedGlobalPrefix Erdos547b.ZhaoSourcePartitionCutCoordinates
open Erdos547b.ZhaoSourcePartitionCutMarks Erdos547b.ZhaoSourcePrivatePairGeometry
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoClaim68 Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616HierarchyAttachments

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (sourceP : ZhaoForestPartition T globalRoot small) {k : ℕ}
variable (selected : Finset (Fin (Fintype.card (ChildKey sourceP.orderedForest))))
variable (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin (Fintype.card (ChildKey sourceP.orderedForest))))
variable (locate : Fin (Fintype.card (ChildKey sourceP.orderedForest)) → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∉ selected → i ∈ family (locate i).1 (locate i).2)
variable (hlocate : ∀ i, (locate i).1 = componentReservoirSide sourceP ((branchForest sourceP).owner i))

include P hT locate hcover hlocate in
theorem exists_treeCopy_of_sourceBudgets
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3) (hCV1 : C ⊆ O.D.V1) (hC : 0 < C.card)
    (hkind : ∀ s j, (kinds s j).Valid α)
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => (branchForest sourceP).owner i ≤ (branchForest sourceP).owner j))
    (hside : ∀ s j i, i ∈ family s j → componentReservoirSide sourceP ((branchForest sourceP).owner i) = s)
    (hselectedSide : ∀ i ∈ selected, componentReservoirSide sourceP ((branchForest sourceP).owner i) = 0)
    (hbranch : ∀ s j, ∀ i ∈ family s j, (kinds s j).BranchValid (branchForest sourceP).branches i)
    (hedge : ∀ s j, ∀ e ∈ allocation s j, edgeValid W Q S (rootCluster W Q s) (kinds s j) e)
    (hsmall : ∀ i, (branchForest sourceP).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
    (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hresidual : ∀ s j e, e ∈ allocation s j →
      e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges)
    (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (allocation s)).card ≤ globalCount)
    (hbudget : ∀ s j, family s j ≠ [] → mass (fun i => ((branchForest sourceP).branches.size i : ℝ)) (family s j) ≤
      (∑ e ∈ allocation s j, capacity W Q S (rootCluster W Q s) (kinds s j) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (allocation s j).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (hselectedSize : ∀ i ∈ selected, 3 ≤ (branchForest sourceP).branches.size i)
    (hmarks : (∑ i ∈ selected, ((branchMarks sourceP i).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize)
    (hselectedMass : (∑ i ∈ selected, ((branchForest sourceP).branches.size i : ℝ)) ≤
      (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize)
    (hroots : (sourceP.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  have hselectedLocate : ∀ i ∈ selected, (locate i).1 = 0 := by
    intro i hi
    rw [hlocate i, hselectedSide i hi]
  have hsameSide (s : Fin 2) : Pairwise (fun i j => Disjoint (allocation s i) (allocation s j)) := by
    intro i j hne
    exact hdisjoint ⟨s, i⟩ ⟨s, j⟩ (fun h => hne (congrArg Prod.snd h))
  obtain ⟨A⟩ := exists_terminalCutPrefix W Q S O P (branchForest sourceP).branches (branchForest sourceP).owner
    (branchMarks sourceP) selected (componentReservoirSide sourceP) kinds allocation family locate hcover
    (partitionCutSource sourceP hT locate hlocate)
    hα hα1 hhost horder hk hCV1 hC hkind hsameSide hside hselectedSide hselectedLocate
    hbranch hedge hsmall haway globalCount hglobal hbudget hselectedSize hmarks hselectedMass
    (fun i _ a ha => branchMarks_color sourceP hT i a ha) hroots
    (partitionParent_marked sourceP selected) hnd hordered
  exact ⟨terminalTreeCopy W Q S O P hT sourceP selected kinds allocation family locate hcover hlocate
    A hCV1 hresidual hdisjoint haway⟩

end Erdos547b.ZhaoSourceMarkedTerminalTreeCopy

#print axioms Erdos547b.ZhaoSourceMarkedTerminalTreeCopy.exists_treeCopy_of_sourceBudgets
