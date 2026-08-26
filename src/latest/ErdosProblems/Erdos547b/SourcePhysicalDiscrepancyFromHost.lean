/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePhysicalUnbalanced
import ErdosProblems.Erdos547b.SourcePhysicalUnbalancedNumerics
import ErdosProblems.Erdos547b.SourceExceptionalRestrictions

/-! # Actual physical discrepancy at every adjacent large pair in the original O -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePhysicalDiscrepancyFromHost

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourcePhysicalUnbalanced Erdos547b.ZhaoSourcePhysicalUnbalancedNumerics
open Erdos547b.ZhaoSourceTwoSidedRows Erdos547b.ZhaoSourceExceptionalRestrictions
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim617BranchCount

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

/-- Only the distinguished pair and its high reservoirs change. -/
def retargetCertificate (C D : Index W) (hC : C ∈ large W) (hD : D ∈ large W)
    (hCO : (Sum.inl C : EvenPadding (Index W)) ∈ Q.claim67.O)
    (hDO : (Sum.inl D : EvenPadding (Index W)) ∈ Q.claim67.O)
    (hCD : (reduced W).Adj C D) : Certificate W :=
  let hC0 := exists_reservoir_card_eq (assignment W) G q (sourceQuota W) hC
  let hD0 := exists_reservoir_card_eq (assignment W) G q (sourceQuota W) hD
  { A := C
    B := D
    adj := hCD
    A_mem := hC
    B_mem := hD
    A₀ := Classical.choose hC0
    B₀ := Classical.choose hD0
    A₀_subset := (Classical.choose_spec hC0).1
    B₀_subset := (Classical.choose_spec hD0).1
    A₀_card := (Classical.choose_spec hC0).2.1
    B₀_card := (Classical.choose_spec hD0).2.1
    A₀_high := (Classical.choose_spec hC0).2.2
    B₀_high := (Classical.choose_spec hD0).2.2
    claim67 := Q.claim67
    A_in_claim67O := hCO
    B_in_claim67O := hDO
    matching_edge_meets_large := Q.matching_edge_meets_large }

variable {n : ℕ} (H : SimpleGraph (Fin (2 * n - 2))) [DecidableRel H.Adj]
variable (Z : Witness α (n - 1) M H) (R : Certificate Z)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem physicalUnbalanced_A_lt_of_notEC1
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ n - 1)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α Z.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * Z.clusterSize) :
    ((physicalUnbalanced Z R (Sum.inl R.A)).card : ℝ) <
      2 * (eta α : ℝ) * paddedHalf (Index Z) := by
  have hn : 2 ≤ n := by
    have hh := Z.five_ordinaryParts_le_host
    have hp := Z.ordinaryParts_pos
    omega
  obtain ⟨S⟩ := exists_twoSidedSource Z hα hα1 R (by omega) horder
  have hsource := (exceptional_card_bounds_of_notEC1 H Z R S.clean hT P hα hα1 horder
    hlarge hnotEC1 hcard hnot hsmall hroots 0).1
  have htransfer := physicalUnbalanced_A_card_le Z R S hα (error_separation hα hα1).1
  have hmargin := exceptional_target_margin Z hα hα1
  linarith only [hsource, htransfer, hmargin]

include hT in
theorem physicalUnbalanced_lt_of_large_neighbor
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ n - 1)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α Z.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * Z.clusterSize)
    (C : EvenPadding (Index Z)) (hC : C ∈ padFinset (large Z) ∩ R.claim67.O)
    (hneighbor : ∃ D ∈ padFinset (large Z) ∩ R.claim67.O, (padGraph (reduced Z)).Adj C D) :
    ((physicalUnbalanced Z R C).card : ℝ) < 2 * (eta α : ℝ) * paddedHalf (Index Z) := by
  obtain ⟨D, hD, hCD⟩ := hneighbor
  cases C with
  | inr c => exact (not_mem_padFinset_inr c (Finset.mem_inter.mp hC).1).elim
  | inl c =>
    cases D with
    | inr d => exact (not_mem_padFinset_inr d (Finset.mem_inter.mp hD).1).elim
    | inl d =>
      let Q' := retargetCertificate Z R c d
        (mem_padFinset_inl.mp (Finset.mem_inter.mp hC).1)
        (mem_padFinset_inl.mp (Finset.mem_inter.mp hD).1)
        (Finset.mem_inter.mp hC).2 (Finset.mem_inter.mp hD).2
        ((padGraph_adj_inl (reduced Z) c d).mp hCD)
      exact physicalUnbalanced_A_lt_of_notEC1 H Z Q' hT P hα hα1 horder hlarge hnotEC1
        hcard hnot hsmall hroots

end Erdos547b.ZhaoSourcePhysicalDiscrepancyFromHost

#print axioms Erdos547b.ZhaoSourcePhysicalDiscrepancyFromHost.retargetCertificate
#print axioms Erdos547b.ZhaoSourcePhysicalDiscrepancyFromHost.physicalUnbalanced_A_lt_of_notEC1
#print axioms Erdos547b.ZhaoSourcePhysicalDiscrepancyFromHost.physicalUnbalanced_lt_of_large_neighbor
