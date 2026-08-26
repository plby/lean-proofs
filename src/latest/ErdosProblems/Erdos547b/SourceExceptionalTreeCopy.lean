/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceTaggedIdealTreeCopy
import ErdosProblems.Erdos547b.SourceExceptionalFamilies
import ErdosProblems.Erdos547b.SourceExceptionalIdealGains

/-!
# The exceptional family and two residuals reconstruct the actual tree

The three literal source sets supply every source coordinate. Matching
disjointness and ideal-weight inequalities suffice for the checked global
embedding; no graph-copy callback is introduced here.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceExceptionalTreeCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.TreePartition
open Erdos547b.ZhaoSourceTaggedIdealTreeCopy Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceExceptionalIdealGains Erdos547b.ZhaoSourceCapacityBudgetMargins
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoSourceTwoSideFamilyAdvance

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem exists_treeCopy_of_exceptionalBudgets
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (s : Fin 2) (selected : Finset (BranchIndex P))
    (hselected : selected ⊆ sideBranches P s)
    (kind : FamilyKind) (hkind : kind.Valid α)
    (hbranch : ∀ i ∈ selected, kind.BranchValid (branchForest P).branches i)
    (E0 E1 Eb : Finset (MatchingEdge Q.claim67.M))
    (h01 : Disjoint E0 E1) (h0b : Disjoint E0 Eb) (h1b : Disjoint E1 Eb)
    (haway : E0 ∪ E1 ∪ Eb ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hedge : ∀ e ∈ E0, edgeValid W Q S (rootCluster W Q s) kind e)
    (hbudget0 : (branchMass P selected : ℝ) + 3 * (gamma α : ℝ) * q ≤
      ∑ e ∈ E0, idealCapacity W Q S (rootCluster W Q s) kind e)
    (hbudget1 : (branchMass P (sideBranches P s \ selected) : ℝ) + 3 * (gamma α : ℝ) * q ≤
      ∑ e ∈ E1, rowWeight W S (Sum.inl (rootCluster W Q s)) e)
    (hbudgetb : (branchMass P (sideBranches P (otherSide s)) : ℝ) + 3 * (gamma α : ℝ) * q ≤
      ∑ e ∈ Eb, rowWeight W S (Sum.inl (rootCluster W Q (otherSide s))) e)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  let kinds : Fin 3 → FamilyKind := ![kind, .threshold 0, .threshold 0]
  let allocation : Fin 3 → Finset (MatchingEdge Q.claim67.M) := ![E0, E1, Eb]
  have hkind0 : FamilyKind.Valid α (.threshold 0) := by
    constructor <;> norm_num
  have hcast (family : Finset (BranchIndex P)) :
      (∑ i ∈ family, ((branchForest P).branches.size i : ℝ)) = (branchMass P family : ℝ) := by
    simp only [branchMass, Nat.cast_sum]
  apply exists_treeCopy_of_taggedIdealBudgets W Q S hT P hα hα1 hhost horder
    (by decide) (exceptionalTags s) kinds
    (by intro j; fin_cases j; exact hkind; exact hkind0; exact hkind0)
    allocation (exceptionalFamilies P s selected)
    (exceptionalFamilies_cover P s selected) (exceptionalFamilies_side P s selected hselected)
  · intro j i hi
    fin_cases j
    · exact hbranch i hi
    · exact ordinary_branchValid _ _
    · exact ordinary_branchValid _ _
  · intro j e he
    fin_cases j
    · exact hedge e he
    · trivial
    · trivial
  · exact hsmall
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h01
    · exact h0b
    · exact h01.symm
    · exact (hij rfl).elim
    · exact h1b
    · exact h0b.symm
    · exact h1b.symm
    · exact (hij rfl).elim
  · intro j e he
    apply haway
    fin_cases j
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
    · exact Finset.mem_union_right _ he
  · intro j _
    fin_cases j
    · change (∑ i ∈ selected, ((branchForest P).branches.size i : ℝ)) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ E0, idealCapacity W Q S (rootCluster W Q s) kind e
      rw [hcast]
      exact hbudget0
    · change (∑ i ∈ sideBranches P s \ selected, ((branchForest P).branches.size i : ℝ)) +
        3 * (gamma α : ℝ) * q ≤ ∑ e ∈ E1, idealCapacity W Q S (rootCluster W Q s) (.threshold 0) e
      simpa only [hcast, ordinary_idealCapacity] using hbudget1
    · change (∑ i ∈ sideBranches P (otherSide s), ((branchForest P).branches.size i : ℝ)) +
        3 * (gamma α : ℝ) * q ≤
          ∑ e ∈ Eb, idealCapacity W Q S (rootCluster W Q (otherSide s)) (.threshold 0) e
      simpa only [hcast, ordinary_idealCapacity] using hbudgetb
  · exact hroots

end Erdos547b.ZhaoSourceExceptionalTreeCopy

#print axioms Erdos547b.ZhaoSourceExceptionalTreeCopy.exists_treeCopy_of_exceptionalBudgets
