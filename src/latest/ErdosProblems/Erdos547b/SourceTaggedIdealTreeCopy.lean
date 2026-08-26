/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceIdealCapacityTreeCopy

/-!
# Actual tree construction from globally tagged source families

Place each source family and its matching on its designated root side.
The opposite-side slot is empty and carries no budget obligation.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceTaggedIdealTreeCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.TreePartition
open Erdos547b.ZhaoSourceIdealCapacityTreeCopy Erdos547b.ZhaoSourceCapacityBudgetMargins
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
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
theorem exists_treeCopy_of_taggedIdealBudgets
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
    (tag : Fin k → Fin 2) (kinds : Fin k → FamilyKind)
    (hkind : ∀ j, (kinds j).Valid α)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M))
    (family : Fin k → Finset (Fin (Fintype.card (ChildKey P.orderedForest))))
    (hcover : ∀ i, ∃ j, i ∈ family j)
    (hside : ∀ j i, i ∈ family j → componentReservoirSide P ((branchForest P).owner i) = tag j)
    (hbranch : ∀ j, ∀ i ∈ family j, (kinds j).BranchValid (branchForest P).branches i)
    (hedge : ∀ j, ∀ e ∈ allocation j, edgeValid W Q S (rootCluster W Q (tag j)) (kinds j) e)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (allocation i) (allocation j))
    (haway : ∀ j, allocation j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hbudget : ∀ j, family j ≠ ∅ →
      (∑ i ∈ family j, ((branchForest P).branches.size i : ℝ)) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ allocation j, idealCapacity W Q S (rootCluster W Q (tag j)) (kinds j) e)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  let all : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M) :=
    fun s j => if tag j = s then allocation j else ∅
  let families : Fin 2 → Fin k → Finset (Fin (Fintype.card (ChildKey P.orderedForest))) :=
    fun s j => if tag j = s then family j else ∅
  apply exists_treeCopy_of_idealSourceBudgets W Q S hT P hα hα1 hhost horder hk
    (fun _ j => kinds j) (fun _ j => hkind j) all families
  · intro i
    obtain ⟨j, hj⟩ := hcover i
    exact ⟨tag j, j, by simpa only [families, if_pos rfl] using hj⟩
  · intro s j i hi
    by_cases hs : tag j = s
    · exact (hside j i (by simpa only [families, if_pos hs] using hi)).trans hs
    · simp only [families, if_neg hs, Finset.notMem_empty] at hi
  · intro s j i hi
    by_cases hs : tag j = s
    · exact hbranch j i (by simpa only [families, if_pos hs] using hi)
    · simp only [families, if_neg hs, Finset.notMem_empty] at hi
  · intro s j e he
    by_cases hs : tag j = s
    · subst s
      exact hedge j e (by simpa only [all, if_pos rfl] using he)
    · simp only [all, if_neg hs, Finset.notMem_empty] at he
  · exact hsmall
  · rintro ⟨s, i⟩ ⟨t, j⟩ hne
    change Disjoint (all s i) (all t j)
    by_cases hs : tag i = s
    · by_cases ht : tag j = t
      · simp only [all, if_pos hs, if_pos ht]
        apply hdisjoint i j
        intro hij
        apply hne
        subst j
        exact Prod.ext (hs.symm.trans ht) rfl
      · simp only [all, if_neg ht, Finset.disjoint_empty_right]
    · simp only [all, if_neg hs, Finset.disjoint_empty_left]
  · intro s j e he
    by_cases hs : tag j = s
    · exact haway j (by simpa only [all, if_pos hs] using he)
    · simp only [all, if_neg hs, Finset.notMem_empty] at he
  · intro s j hnonempty
    by_cases hs : tag j = s
    · subst s
      simpa only [families, all, if_pos rfl] using
        hbudget j (by simpa only [families, if_pos rfl] using hnonempty)
    · simp only [families, if_neg hs, ne_eq, not_true_eq_false] at hnonempty
  · exact hroots

end Erdos547b.ZhaoSourceTaggedIdealTreeCopy

#print axioms Erdos547b.ZhaoSourceTaggedIdealTreeCopy.exists_treeCopy_of_taggedIdealBudgets
