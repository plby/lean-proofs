/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim618Numerics
import ErdosProblems.Erdos547b.SourcePhysicalDiscrepancyFromHost
import ErdosProblems.Erdos547b.SourceClaim617FromHost
import ErdosProblems.Erdos547b.Claim618TwoThreshold
import ErdosProblems.Erdos547b.Lemma611Claim618Adapter

/-! # Actual-host Claim 6.18 and the full high-density crossing bound -/

open scoped SimpleGraph Classical
noncomputable section
namespace Erdos547b.ZhaoSourceClaim618FromHost

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoSourceNearFullNumerics Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSourceThresholdGraphs Erdos547b.ZhaoSourcePhysicalUnbalanced
open Erdos547b.ZhaoSourcePhysicalDiscrepancyFromHost Erdos547b.ZhaoSourceClaim618Numerics
open Erdos547b.ZhaoClaim618RoundedNumerics Erdos547b.ZhaoSourceClaim617FromHost
open Erdos547b.ZhaoClaim618TwoThreshold Erdos547b.ZhaoLemma611Claim618Adapter
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim615SourceSelection

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

theorem initial_large_neighbor {fb : ℝ} (O : Output W Q S fb)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (C : EvenPadding (Index W)) (hC : C ∈ O.D.L1) :
    ∃ D ∈ padFinset (large W) ∩ Q.claim67.O, (padGraph (reduced W)).Adj C D := by
  refine ⟨Sum.inl Q.A, Finset.mem_inter.mpr ⟨mem_padFinset_inl.mpr Q.A_mem, Q.A_in_claim67O⟩, ?_⟩
  have he := O.D.edgeOf_mem_minEdges Q.matching_edge_meets_large hC
  have hclean := (Finset.mem_inter.mp (O.min_subset he)).1
  have hη := (parameter_bounds hα hα1).1
  have hd := (sourceCleanEdges_density Q.claim67.M (padFinset (large W)) Q.claim67.O
    (rootDensity W S) (Sum.inl Q.A) (eta α : ℝ) hη O.reserved.edges hclean).1
  have heq := (O.D.edgeOf_spec Q.matching_edge_meets_large hC).2.1
  rw [heq] at hd
  exact ((S.source_rows W).supportA C (by
    linarith only [hd, (parameter_bounds hα hα1).2.1])).symm

variable {n : ℕ} (H : SimpleGraph (Fin (2 * n - 2))) [DecidableRel H.Adj]
variable (Z : Witness α (n - 1) M H) (R : Certificate Z) (F : CleanSourceWitness Z R)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U}
variable (P : ZhaoForestPartition T globalRoot (freshBranchBound α Z.clusterSize))
variable (O : Output Z R F (branchMass P (sideBranches P 1)))

include hT in
theorem sourceL1_highDensity_crossing_lt
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ n - 1)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α Z.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * Z.clusterSize) :
    (((threshold Z (4 * (eta α : ℝ))).interedges O.D.L1 O.D.V2).card : ℝ) <
      16 * (rhoOne α : ℝ) * (paddedHalf (Index Z) : ℝ) ^ 2 := by
  have hn : 2 ≤ n := by
    have hh := Z.five_ordinaryParts_le_host
    have hp := Z.ordinaryParts_pos
    omega
  have h617 := sourceS1_crossing_lt Z R F hT P O hα hα1 (by omega) horder (by omega) hnot
  obtain ⟨hk, haPos, ha, hlocal, hpartner, hdouble, hfinal⟩ := actual_gates Z R F O hα hα1
  obtain ⟨hinj, hedge, hlargeEnd, hpairs, hcovered, hedgeOf⟩ :=
    claim618_indexing_of_decomposition O.D R.matching_edge_meets_large
  have hL1 := O.D.L1_subset_large_inter R.matching_edge_meets_large
  have hcut : O.D.L1.card + O.D.V2.card ≤ 2 * paddedHalf (Index Z) := by
    have hc := Finset.card_le_card (Finset.sdiff_subset : O.D.L1 ⊆ O.D.V1)
    change O.D.L1.card ≤ O.D.V1.card at hc
    have hV := O.D.V2_card
    rw [card_evenPadding] at hV
    change O.D.V2.card = 2 * paddedHalf (Index Z) - O.D.V1.card at hV
    have hV1 : O.D.V1.card ≤ paddedHalf (Index Z) := O.D.V1_card_upper
    omega
  have hη : 0 < 2 * (eta α : ℝ) := by
    have hh : (0 : ℝ) < eta α := by exact_mod_cast (parameter_pos hα).2.2.1
    positivity
  have hbound (C : EvenPadding (Index Z)) (hC : C ∈ padFinset (large Z) ∩ R.claim67.O)
      (hneighbor : ∃ D ∈ padFinset (large Z) ∩ R.claim67.O, (padGraph (reduced Z)).Adj C D) :
      (physicalUnbalanced Z R C).card ≤ exceptionalCount (eta α : ℝ) (paddedHalf (Index Z)) := by
    have hb := (physicalUnbalanced_lt_of_large_neighbor H Z R hT P hα hα1 horder hlarge hnotEC1
      hcard hnot hsmall hroots C hC hneighbor).le
    have hc := hb.trans (Nat.le_ceil (2 * (eta α : ℝ) * paddedHalf (Index Z)))
    exact Nat.cast_le.mp hc
  apply crossing_lt_of_local_twoThresholds
    (padGraph (reduced Z)) (threshold Z (2 * (eta α : ℝ))) (threshold Z (4 * (eta α : ℝ)))
    (threshold_le Z _) (threshold_antitone Z (by linarith only [hη]))
    (padFinset (large Z)) O.D.L1 O.D.V2 O.D.S1 (allMatchingEdges R.claim67.M)
    (orientedEndpoint R.claim67.M (padFinset (large Z))) O.D.edgeOf (density Z)
    (2 * (eta α : ℝ)) (rho α : ℝ) (rhoOne α : ℝ) (paddedHalf (Index Z))
    (initialCount (rhoOne α : ℝ) (paddedHalf (Index Z)))
    (neighborCount (rhoOne α : ℝ) (paddedHalf (Index Z)))
    (exceptionalCount (eta α : ℝ) (paddedHalf (Index Z))) (missed Z)
    (auxiliaryDegree (rhoOne α : ℝ) (paddedHalf (Index Z)))
    (partnerDegree (rhoOne α : ℝ) (paddedHalf (Index Z)))
    (terminalCount (rhoOne α : ℝ) (paddedHalf (Index Z))) R.claim67
    hη hk haPos ha hcut hlocal hpartner hdouble hfinal h617 hL1
    hinj hedge hlargeEnd hpairs hcovered hedgeOf
  · intro A B hAB
    have h := hAB.2
    linarith only [h]
  · exact fun _ _ h => h.2
  · exact fun A B h => (threshold_adj_iff Z hη A B).mpr h
  · exact fun _ _ h => density_nonadj_zero Z h
  · intro C hC
    exact hbound C (hL1 hC) (initial_large_neighbor Z R F O hα hα1 C hC)
  · exact hbound

include hT in
theorem sourceV1_highDensity_crossing_lt
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ n - 1)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α Z.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * Z.clusterSize) :
    (((threshold Z (4 * (eta α : ℝ))).interedges O.D.V1 O.D.V2).card : ℝ) <
      16 * ((rho α : ℝ) + (rhoOne α : ℝ)) * (paddedHalf (Index Z) : ℝ) ^ 2 := by
  have hn : 2 ≤ n := by
    have hh := Z.five_ordinaryParts_le_host
    have hp := Z.ordinaryParts_pos
    omega
  exact reducedCross_lt_of_claim617_claim618 O.D (threshold Z (4 * (eta α : ℝ)))
    (threshold_le Z _) (rho α : ℝ) (rhoOne α : ℝ) (paddedHalf (Index Z))
    (sourceS1_crossing_lt Z R F hT P O hα hα1 (by omega) horder (by omega) hnot)
    (sourceL1_highDensity_crossing_lt H Z R F hT P O hα hα1 horder hlarge hnotEC1
      hcard hnot hsmall hroots)

end Erdos547b.ZhaoSourceClaim618FromHost

#print axioms Erdos547b.ZhaoSourceClaim618FromHost.initial_large_neighbor
#print axioms Erdos547b.ZhaoSourceClaim618FromHost.sourceL1_highDensity_crossing_lt
#print axioms Erdos547b.ZhaoSourceClaim618FromHost.sourceV1_highDensity_crossing_lt
