/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceBalancedMassFromHost
import ErdosProblems.Erdos547b.SourceNonextremeBalancedForcing
import ErdosProblems.Erdos547b.SourceExceptionalRootExchange
import ErdosProblems.Erdos547b.SourceRawDiscrepancy

/-!
# Both exceptional-family bounds from the actual source host

Noncontainment outside EC1 supplies the balanced source mass. Either the
minor family is large and its raw discrepancy is already bounded, or it
is small and a preliminary reservation is constructed. The actual root
exchange proves both physical rows' bounds from the same chosen parity.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceExceptionalRestrictions

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceBalancedMassFromHost Erdos547b.ZhaoSourceNonextremeBalancedForcing
open Erdos547b.ZhaoSourceExceptionalRootExchange Erdos547b.ZhaoSourceRawDiscrepancy
open Erdos547b.ZhaoSourceLargeExceptionalForcing Erdos547b.ZhaoSourceSmallExceptionalForcing
open Erdos547b.ZhaoSourceSwappedRootRows Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {n M : ℕ}
variable (H : SimpleGraph (Fin (2 * n - 2))) [DecidableRel H.Adj]
variable (W : Witness α (n - 1) M H) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem exceptional_card_bounds_of_notEC1
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ n - 1)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    ∀ u : Fin 2,
      ((unbalancedAway W Q S u).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W) ∧
      ((nonextremeAway W Q S u).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W) := by
  have hn : 2 ≤ n := by
    have hh := W.five_ordinaryParts_le_host
    have hp := W.ordinaryParts_pos
    omega
  have hhost : 2 * n - 2 = 2 * (n - 1) := by omega
  have hcard' : Fintype.card U = (n - 1) + 1 := by omega
  have hnotHost : ¬Nonempty (T.Copy (embeddingHost W)) := by
    rintro ⟨E⟩
    exact hnot (((SimpleGraph.Copy.ofLE (embeddingHost W) H (embeddingHost_le_original W)).comp E).isContained)
  obtain ⟨s, hmass⟩ := exists_balancedSide_mass_of_notEC1 H W hα hα1 horder hlarge hnotEC1
    hT hcard hnot P hroots
  have hbound (Q' : Certificate W) (S' : CleanSourceWitness W Q') :
      ((unbalancedAway W Q' S' s).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W) ∧
      ((nonextremeAway W Q' S' s).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W) := by
    by_cases hminor : (fourthRoot α : ℝ) * (n - 1 : ℕ) ≤ (branchMass P (sideBranches P 1) : ℝ)
    · have hrows := fun R hR => (raw_discrepancy_lt_anySide W Q' S' hT P hα hα1 hhost horder hcard'
        hminor hsmall hroots hnotHost s R hR).le
      constructor
      · apply lt_of_not_ge
        intro hfamily
        exact hnotHost (exists_treeCopy_of_largeUnbalancedFamily W Q' S' hT P hα hα1 hhost horder
          hcard' s hfamily hmass.le hrows hsmall hroots)
      · apply lt_of_not_ge
        intro hfamily
        exact hnotHost (exists_treeCopy_of_largeNonextremeBalanced W Q' S' hT P hα hα1 hhost horder
          hcard' s hfamily hmass.le hrows hsmall hroots)
    · have hminor' := lt_of_not_ge hminor
      have hs := balancedSide_eq_zero_of_smallMinor P hα hα1 (n - 1) s hminor' hmass.le
      have hother : (branchMass P (sideBranches P (otherSide s)) : ℝ) ≤
          (fourthRoot α : ℝ) * (n - 1 : ℕ) := by
        rw [hs]
        exact hminor'.le
      constructor
      · apply lt_of_not_ge
        intro hfamily
        exact hnotHost (exists_treeCopy_of_smallUnbalancedFamily W Q' S' hT P hα hα1 hhost horder
          hcard' s hfamily hmass.le hother hsmall hroots)
      · apply lt_of_not_ge
        intro hfamily
        exact hnotHost (exists_treeCopy_of_smallNonextremeBalanced W Q' S' hT P hα hα1 hhost horder
          hcard' s hfamily hmass.le hother hsmall hroots)
  intro u
  by_cases hu : u = s
  · subst u
    exact hbound Q S
  · have hother : otherSide s = u := by
      fin_cases u <;> fin_cases s <;>
        first | exact (hu rfl).elim | rfl
    have h := hbound (swapCertificate W Q) (swapSource W Q S)
    rw [unbalancedAway_swap W Q S s, nonextremeAway_swap W Q S s, hother] at h
    exact h

end Erdos547b.ZhaoSourceExceptionalRestrictions

#print axioms Erdos547b.ZhaoSourceExceptionalRestrictions.exceptional_card_bounds_of_notEC1
