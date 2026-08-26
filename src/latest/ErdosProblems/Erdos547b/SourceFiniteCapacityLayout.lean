/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityTerminalTreeCopy

/-!
# From finite source-family allocations to the actual tree copy

Filter the existing global owner-sorted enumeration by each source set.
This constructs every list-order and classifier requirement and preserves
the exact source mass. Empty source slots impose no scalar budget.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFiniteCapacityLayout

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceSortedBranchOrder Erdos547b.ZhaoSourceSaturatedPacking

def familyList {b r : ℕ} (owner : Fin b → Fin r) (selected : Finset (Fin b)) : List (Fin b) :=
  (ownerSortedList owner).filter (fun i => i ∈ selected)

theorem mem_familyList {b r : ℕ} (owner : Fin b → Fin r) (selected : Finset (Fin b)) (i : Fin b) :
    i ∈ familyList owner selected ↔ i ∈ selected := by
  simp only [familyList, List.mem_filter, mem_ownerSortedList owner i, decide_eq_true_eq, true_and]

theorem familyList_nodup {b r : ℕ} (owner : Fin b → Fin r) (selected : Finset (Fin b)) :
    (familyList owner selected).Nodup :=
  (ownerSortedList_nodup owner).filter _

theorem familyList_ordered {b r : ℕ} (owner : Fin b → Fin r) (selected : Finset (Fin b)) :
    (familyList owner selected).Pairwise (fun i j => owner i ≤ owner j) :=
  (pairwise_ownerSortedList owner).sublist List.filter_sublist

theorem familyList_toFinset {b r : ℕ} (owner : Fin b → Fin r) (selected : Finset (Fin b)) :
    (familyList owner selected).toFinset = selected := by
  ext i
  simp only [List.mem_toFinset, mem_familyList]

theorem mass_familyList {b r : ℕ} (owner : Fin b → Fin r) (selected : Finset (Fin b)) (weight : Fin b → ℝ) :
    mass weight (familyList owner selected) = ∑ i ∈ selected, weight i := by
  unfold mass
  rw [← List.sum_toFinset weight (familyList_nodup owner selected), familyList_toFinset]

open Erdos547b.TreePartition Erdos547b.ZhaoSourceCapacityTerminalTreeCopy
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoClaim616HierarchyAttachments

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small) {k : ℕ}

include hT in
theorem exists_treeCopy_of_finsetSourceBudgets
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
    (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (allocation s)).card ≤ globalCount)
    (hbudget : ∀ s j, family s j ≠ ∅ → (∑ i ∈ family s j, ((branchForest P).branches.size i : ℝ)) ≤
      (∑ e ∈ allocation s j, capacity W Q S (rootCluster W Q s) (kinds s j) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (allocation s j).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  let lists := fun s j => familyList (branchForest P).owner (family s j)
  choose side index hchosen using hcover
  let locate := fun i => (side i, index i)
  have hcoverList : ∀ i, i ∈ lists (locate i).1 (locate i).2 := by
    intro i
    exact (mem_familyList _ _ i).mpr (hchosen i)
  apply exists_treeCopy_of_sourceBudgets W Q S hT P kinds allocation lists locate hcoverList
    hα hα1 hhost horder hk hkind
    (fun s j => familyList_nodup _ _) (fun s j => familyList_ordered _ _)
    (fun s j i hi => hside s j i ((mem_familyList _ _ i).mp hi))
    (fun s j i hi => hbranch s j i ((mem_familyList _ _ i).mp hi))
    hedge hsmall hdisjoint haway globalCount hglobal
  · intro s j hne
    change mass _ (familyList (branchForest P).owner (family s j)) ≤ _
    rw [mass_familyList]
    apply hbudget s j
    intro hempty
    apply hne
    simp only [lists, familyList, hempty, Finset.notMem_empty, decide_false, List.filter_false]
  · exact hroots

end Erdos547b.ZhaoSourceFiniteCapacityLayout

#print axioms Erdos547b.ZhaoSourceFiniteCapacityLayout.mass_familyList
#print axioms Erdos547b.ZhaoSourceFiniteCapacityLayout.exists_treeCopy_of_finsetSourceBudgets
