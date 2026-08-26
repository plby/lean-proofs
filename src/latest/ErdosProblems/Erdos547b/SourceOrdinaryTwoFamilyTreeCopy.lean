/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceTaggedIdealTreeCopy
import ErdosProblems.Erdos547b.SourceExceptionalFamilies
import ErdosProblems.Erdos547b.SourceExceptionalIdealGains
import ErdosProblems.Erdos547b.SourceSwappedRootRows

/-!
# Realize the ordinary two-row allocation, including its swapped alternative

Both canonical parity families are copied in the actual regular-pair host.
The second allocation alternative uses the explicitly exchanged rich
certificate and clean roots, without changing the original tree data.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceOrdinaryTwoFamilyTreeCopy

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceTaggedIdealTreeCopy Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceExceptionalIdealGains Erdos547b.ZhaoSourceSwappedRootRows
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoSourceCapacityBudgetMargins
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoSourceTwoSideFamilyAdvance

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem exists_treeCopy_of_twoRowBudgets
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (Ea Eb : Finset (MatchingEdge Q.claim67.M)) (hdisjoint : Disjoint Ea Eb)
    (ha : Ea ⊆ awayEdges W Q) (hb : Eb ⊆ awayEdges W Q)
    (hbudgeta : (branchMass P (sideBranches P 0) : ℝ) + 3 * (gamma α : ℝ) * q ≤
      ∑ e ∈ Ea, sideWeight W Q S 0 e)
    (hbudgetb : (branchMass P (sideBranches P 1) : ℝ) + 3 * (gamma α : ℝ) * q ≤
      ∑ e ∈ Eb, sideWeight W Q S 1 e)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  let allocation : Fin 2 → Finset (MatchingEdge Q.claim67.M) := ![Ea, Eb]
  have hcast (f : Finset (BranchIndex P)) :
      (∑ i ∈ f, ((branchForest P).branches.size i : ℝ)) = (branchMass P f : ℝ) := by
    simp only [branchMass, Nat.cast_sum]
  apply exists_treeCopy_of_taggedIdealBudgets W Q S hT P hα hα1 hhost horder
    (by decide) id (fun _ => .threshold 0) (by intro j; constructor <;> norm_num)
    allocation (sideBranches P)
  · intro i
    exact ⟨_, (mem_sideBranches P _ i).mpr rfl⟩
  · intro j i hi
    exact (mem_sideBranches P j i).mp hi
  · intro j i _
    exact ordinary_branchValid _ _
  · intro j e _
    trivial
  · exact hsmall
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hdisjoint
    · exact hdisjoint.symm
    · exact (hij rfl).elim
  · intro j
    fin_cases j
    · exact ha
    · exact hb
  · intro j _
    fin_cases j
    · change (∑ i ∈ sideBranches P 0, ((branchForest P).branches.size i : ℝ)) +
        3 * (gamma α : ℝ) * q ≤ ∑ e ∈ Ea, idealCapacity W Q S (rootCluster W Q 0) (.threshold 0) e
      simpa only [hcast, ordinary_idealCapacity] using hbudgeta
    · change (∑ i ∈ sideBranches P 1, ((branchForest P).branches.size i : ℝ)) +
        3 * (gamma α : ℝ) * q ≤ ∑ e ∈ Eb, idealCapacity W Q S (rootCluster W Q 1) (.threshold 0) e
      simpa only [hcast, ordinary_idealCapacity] using hbudgetb
  · exact hroots

include hT in
theorem exists_treeCopy_of_twoRowAllocationOrSwap
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (hallocation :
      (∃ E ⊆ awayEdges W Q,
        (branchMass P (sideBranches P 1) : ℝ) + 3 * (gamma α : ℝ) * q ≤ ∑ e ∈ E, sideWeight W Q S 1 e ∧
        (branchMass P (sideBranches P 0) : ℝ) + 3 * (gamma α : ℝ) * q ≤
          ∑ e ∈ awayEdges W Q \ E, sideWeight W Q S 0 e) ∨
      (∃ E ⊆ awayEdges W Q,
        (branchMass P (sideBranches P 1) : ℝ) + 3 * (gamma α : ℝ) * q ≤ ∑ e ∈ E, sideWeight W Q S 0 e ∧
        (branchMass P (sideBranches P 0) : ℝ) + 3 * (gamma α : ℝ) * q ≤
          ∑ e ∈ awayEdges W Q \ E, sideWeight W Q S 1 e))
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  have hdisjoint (E : Finset (MatchingEdge Q.claim67.M)) : Disjoint (awayEdges W Q \ E) E := by
    rw [Finset.disjoint_left]
    intro e he hE
    exact (Finset.mem_sdiff.mp he).2 hE
  rcases hallocation with ⟨E, hE, hb, ha⟩ | ⟨E, hE, hb, ha⟩
  · exact exists_treeCopy_of_twoRowBudgets W Q S hT P hα hα1 hhost horder
      (awayEdges W Q \ E) E (hdisjoint E) Finset.sdiff_subset hE ha hb hsmall hroots
  · apply exists_treeCopy_of_twoRowBudgets W (swapCertificate W Q) (swapSource W Q S)
      hT P hα hα1 hhost horder (awayEdges W Q \ E) E (hdisjoint E)
    · rw [awayEdges_swap]
      exact Finset.sdiff_subset
    · rw [awayEdges_swap]
      exact hE
    · calc
        _ ≤ ∑ e ∈ awayEdges W Q \ E, sideWeight W Q S 1 e := ha
        _ = _ := Finset.sum_congr rfl (fun e _ => (sideWeight_swap W Q S 0 e).symm)
    · calc
        _ ≤ ∑ e ∈ E, sideWeight W Q S 0 e := hb
        _ = _ := Finset.sum_congr rfl (fun e _ => (sideWeight_swap W Q S 1 e).symm)
    · exact hsmall
    · exact hroots

end Erdos547b.ZhaoSourceOrdinaryTwoFamilyTreeCopy

#print axioms Erdos547b.ZhaoSourceOrdinaryTwoFamilyTreeCopy.exists_treeCopy_of_twoRowBudgets
#print axioms Erdos547b.ZhaoSourceOrdinaryTwoFamilyTreeCopy.exists_treeCopy_of_twoRowAllocationOrSwap
