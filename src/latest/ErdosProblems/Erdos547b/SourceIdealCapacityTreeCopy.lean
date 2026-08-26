/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFiniteCapacityLayout
import ErdosProblems.Erdos547b.SourceCapacityBudgetMargins
import ErdosProblems.Erdos547b.SourceMatchingVolume

/-!
# Complete tree construction from the paper's ideal source-weight margin

Actual matching volume pays the global count allowance. The explicit
parameter hierarchy pays every capacity, packing and bad-edge loss from
three gamma times q. All family lists and host images are constructed.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceIdealCapacityTreeCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.TreePartition
open Erdos547b.ZhaoSourceFiniteCapacityLayout Erdos547b.ZhaoSourceCapacityBudgetMargins
open Erdos547b.ZhaoSourceMatchingVolume Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim616HierarchyAttachments

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small) {k : ℕ}

include hT in
theorem exists_treeCopy_of_idealSourceBudgets
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
    (kinds : Fin 2 → Fin k → FamilyKind) (hkind : ∀ s j, (kinds s j).Valid α)
    (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
    (family : Fin 2 → Fin k → Finset (Fin (Fintype.card (ChildKey P.orderedForest))))
    (hcover : ∀ i, ∃ s j, i ∈ family s j)
    (hside : ∀ s j i, i ∈ family s j → componentReservoirSide P ((branchForest P).owner i) = s)
    (hbranch : ∀ s j, ∀ i ∈ family s j, (kinds s j).BranchValid (branchForest P).branches i)
    (hedge : ∀ s j, ∀ e ∈ allocation s j, edgeValid W Q S (rootCluster W Q s) (kinds s j) e)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
    (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hbudget : ∀ s j, family s j ≠ ∅ →
      (∑ i ∈ family s j, ((branchForest P).branches.size i : ℝ)) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ allocation s j, idealCapacity W Q S (rootCluster W Q s) (kinds s j) e)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  apply exists_treeCopy_of_finsetSourceBudgets W Q S hT P hα hα1 hhost horder hk kinds hkind
    allocation family hcover hside hbranch hedge hsmall hdisjoint haway
    (Fintype.card (MatchingEdge Q.claim67.M)) (fun _ => Finset.card_le_univ _)
  · intro s j hnonempty
    exact capacityBudget_of_ideal_margin W Q S (rootCluster W Q s) hα hα1 (kinds s j)
      (allocation s j) (Fintype.card (MatchingEdge Q.claim67.M))
      (matchingVolume_bound W Q hhost _) (fullMatchingVolume_bound W Q hhost) _ (hbudget s j hnonempty)
  · exact hroots

end Erdos547b.ZhaoSourceIdealCapacityTreeCopy

#print axioms Erdos547b.ZhaoSourceIdealCapacityTreeCopy.exists_treeCopy_of_idealSourceBudgets
