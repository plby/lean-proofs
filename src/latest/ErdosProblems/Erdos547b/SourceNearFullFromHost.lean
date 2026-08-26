/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceNearFullMatching
import ErdosProblems.Erdos547b.SourceExceptionalRestrictions
import ErdosProblems.Erdos547b.SourceFreshPartitionBounds

/-!
# Near-full matching from the actual nonextremal omitted-tree host

The source partition, exceptional restrictions and optional reservation
are all constructed. In the large-minor case the same actual matching
has the second-row lower bound, by the checked raw discrepancy theorem.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceNearFullFromHost

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceNearFullNumerics
open Erdos547b.ZhaoSourceExceptionalRestrictions Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceFreshPartitionBounds Erdos547b.ZhaoSourceRawDiscrepancy
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

theorem support_bounds {fb : ℝ} (O : Output W Q S fb) :
    (1 - 8 * (eta α : ℝ)) * paddedHalf (Index W) ≤ (O.D.V1.card : ℝ) ∧
      O.D.V1.card ≤ paddedHalf (Index W) ∧
      paddedHalf (Index W) ≤ O.D.V2.card ∧
      (O.D.V2.card : ℝ) ≤ (1 + 8 * (eta α : ℝ)) * paddedHalf (Index W) := by
  have hlow : (1 - 8 * (eta α : ℝ)) * paddedHalf (Index W) ≤ (O.D.V1.card : ℝ) := by
    have h := Nat.le_ceil ((1 - 8 * (eta α : ℝ)) * paddedHalf (Index W))
    have hc : (lowerCount W : ℝ) ≤ O.D.V1.card := by exact_mod_cast O.D.V1_card_lower
    exact h.trans hc
  have hup : O.D.V1.card ≤ paddedHalf (Index W) := O.D.V1_card_upper
  have hsum : O.D.V1.card + O.D.V2.card = 2 * paddedHalf (Index W) := by
    rw [O.D.V2_card, card_evenPadding]
    change O.D.V1.card + (2 * paddedHalf (Index W) - O.D.V1.card) = 2 * paddedHalf (Index W)
    omega
  refine ⟨hlow, hup, by omega, ?_⟩
  have hsumR : (O.D.V1.card : ℝ) + O.D.V2.card = 2 * paddedHalf (Index W) := by exact_mod_cast hsum
  nlinarith only [hsumR, hlow]

theorem reserved_support_bound {fb : ℝ} (O : Output W Q S fb)
    (hα : 0 < α) :
    ((Erdos547b.ZhaoStability.matchingSupport O.D.Mb).card : ℝ) ≤
      4 * (fourthRoot α : ℝ) * paddedHalf (Index W) := by
  have h := O.D.Mb_support_card
  have hR : ((Erdos547b.ZhaoStability.matchingSupport O.D.Mb).card : ℝ) ≤
      2 * (reserveEdgeCap W : ℝ) := by exact_mod_cast h
  have ht : (0 : ℝ) ≤ fourthRoot α := by exact_mod_cast (parameter_pos hα).2.2.2.1.le
  have hf : (reserveEdgeCap W : ℝ) ≤ 2 * (fourthRoot α : ℝ) * paddedHalf (Index W) :=
    Nat.floor_le (by positivity)
  linarith only [hR, hf]

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem degreeB_order_of_largeMinor
    (O : Output W Q S (branchMass P (sideBranches P 1)))
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (hnot : ¬Nonempty (T.Copy (embeddingHost W)))
    (hminor : (fourthRoot α : ℝ) * q ≤ (branchMass P (sideBranches P 1) : ℝ)) :
    (1 - 9 * (eta α : ℝ)) * q < ∑ e ∈ O.D.minEdges, sideWeight W Q S 1 e := by
  have hdiscrepancy := raw_discrepancy_lt_of_not_copy W Q S hT P hα hα1 hhost horder hcard
    hminor hsmall hroots hnot O.D.minEdges (O.min_subset_away W Q S)
  have hA := O.degreeA_order W Q S hα hα1
  have ht := (parameter_bounds hα hα1).2.2.2
  have ht15 : 15 * (fourthRoot α : ℝ) ≤ eta α := by
    nlinarith only [ht, sq_nonneg (fourthRoot α : ℝ), (parameter_bounds hα hα1).1]
  have htq := mul_le_mul_of_nonneg_right ht15 (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hdiff := (abs_lt.mp hdiscrepancy).2
  linarith only [hdiff, hA, htq]

variable {n : ℕ} (H : SimpleGraph (Fin (2 * n - 2))) [DecidableRel H.Adj]

include hT in
theorem exists_output_of_notEC1
    (Z : Witness α (n - 1) M H) (R : Certificate Z) (C : CleanSourceWitness Z R)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ n - 1)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α Z.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * Z.clusterSize) :
    ∃ O : Output Z R C (branchMass P (sideBranches P 1)),
      (fourthRoot α : ℝ) * (n - 1 : ℕ) ≤ (branchMass P (sideBranches P 1) : ℝ) →
        (1 - 9 * (eta α : ℝ)) * (n - 1 : ℕ) < ∑ e ∈ O.D.minEdges, sideWeight Z R C 1 e := by
  have hbound := exceptional_card_bounds_of_notEC1 H Z R C hT P hα hα1 horder hlarge
    hnotEC1 hcard hnot hsmall hroots 0
  have hn : 2 ≤ n := by
    have hh := Z.five_ordinaryParts_le_host
    have hp := Z.ordinaryParts_pos
    omega
  have hhost : 2 * n - 2 = 2 * (n - 1) := by omega
  obtain ⟨O⟩ := exists_output Z R C hα hα1 hhost horder hbound.1 hbound.2
    (branchMass P (sideBranches P 1)) (Nat.cast_nonneg _)
  refine ⟨O, degreeB_order_of_largeMinor Z R C hT P O hα hα1 hhost horder (by omega)
    hsmall hroots ?_⟩
  rintro ⟨E⟩
  exact hnot (((SimpleGraph.Copy.ofLE (embeddingHost Z) H (embeddingHost_le_original Z)).comp E).isContained)

include hT in
theorem exists_partition_and_output_of_notEC1
    (Z : Witness α (n - 1) M H) (R : Certificate Z) (C : CleanSourceWitness Z R)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ n - 1)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H) (root : U) :
    ∃ P : ZhaoForestPartition T root (freshBranchBound α Z.clusterSize),
      (P.numParts : ℝ) ≤ (epsilon α : ℝ) * Z.clusterSize ∧
      (∀ i, (branchForest P).branches.size i ≤ freshBranchBound α Z.clusterSize) ∧
      ∃ O : Output Z R C (branchMass P (sideBranches P 1)),
        (fourthRoot α : ℝ) * (n - 1 : ℕ) ≤ (branchMass P (sideBranches P 1) : ℝ) →
          (1 - 9 * (eta α : ℝ)) * (n - 1 : ℕ) < ∑ e ∈ O.D.minEdges, sideWeight Z R C 1 e := by
  have hn : 2 ≤ n := by
    have hh := Z.five_ordinaryParts_le_host
    have hp := Z.ordinaryParts_pos
    omega
  have hgeneral {hostN q : ℕ} {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
      (W : Witness α q M G) (hh : hostN = 2 * q) (ho : orderThreshold α M ≤ q)
      (hc : Fintype.card U = q + 1) :
      ∃ P : ZhaoForestPartition T root (freshBranchBound α W.clusterSize),
        (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize ∧
        ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize := by
    subst hostN
    exact exists_freshPartition hα hα1 W ho T hT hc root
  obtain ⟨P, hroots, hsmall⟩ := hgeneral Z (by omega) horder (by omega)
  exact ⟨P, hroots, hsmall, exists_output_of_notEC1 hT P H Z R C hα hα1 horder
    hlarge hnotEC1 hcard hnot hsmall hroots⟩

end Erdos547b.ZhaoSourceNearFullFromHost

#print axioms Erdos547b.ZhaoSourceNearFullFromHost.support_bounds
#print axioms Erdos547b.ZhaoSourceNearFullFromHost.degreeB_order_of_largeMinor
#print axioms Erdos547b.ZhaoSourceNearFullFromHost.exists_partition_and_output_of_notEC1
