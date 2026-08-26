/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceNearFullNumerics
import ErdosProblems.Erdos547b.SourceLargeExceptionalForcing
import ErdosProblems.Erdos547b.SourceMatchingVolume

/-!
# Actual near-full source filters

All discarded families and both distinguished root clusters are charged.
The generic Claim-6.11 deletion estimate is used with the actual counts,
not an independently assumed deletion budget.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceNearFullFilters

open Finset SimpleGraph
open Erdos547b.ZhaoSourceNearFullNumerics Erdos547b.ZhaoSourceLargeExceptionalForcing
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoSourceMatchingVolume
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma615

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

abbrev cleanAway (Eb : Finset (MatchingEdge Q.claim67.M)) :=
  sourceCleanEdges Q.claim67.M (padFinset (large W)) Q.claim67.O
    (rootDensity W S) (Sum.inl Q.A) (eta α : ℝ) Eb ∩ awayEdges W Q

theorem sum_inter_away_lower (F : Finset (MatchingEdge Q.claim67.M)) (s : Fin 2) :
    (∑ e ∈ F, sideWeight W Q S s e) ≤
      (∑ e ∈ F ∩ awayEdges W Q, sideWeight W Q S s e) + 4 * W.clusterSize := by
  let I := distinguishedIncidentEdges Q.claim67.M (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)
  have hsub : F \ (F ∩ awayEdges W Q) ⊆ I := by
    intro e he
    have heF := (Finset.mem_sdiff.mp he).1
    have hn := (Finset.mem_sdiff.mp he).2
    by_contra heI
    apply hn
    exact Finset.mem_inter.mpr ⟨heF, Finset.mem_sdiff.mpr ⟨mem_allMatchingEdges _ e, heI⟩⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun e _ _ => sideWeight_nonneg W Q S s e)
  have hI := sideWeight_sum_le W Q S s I
  have hcard : I.card ≤ 2 := distinguishedIncidentEdges_card_le_two
    Q.claim67.M Q.claim67.isMatching (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)
  have hcardR : (I.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_left hcardR (show 0 ≤ (2 : ℝ) * W.clusterSize by positivity)
  have hsplit := Finset.sum_sdiff (Finset.inter_subset_left : F ∩ awayEdges W Q ⊆ F)
    (f := sideWeight W Q S s)
  linarith only [hsum, hI, hmul, hsplit]

theorem cleanAway_weight_gt (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hu : ((unbalancedAway W Q S 0).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W))
    (hx : ((nonextremeAway W Q S 0).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W))
    (Eb : Finset (MatchingEdge Q.claim67.M))
    (hEb : Eb ⊆ allMatchingEdges Q.claim67.M)
    (hEbcount : (Eb.card : ℝ) ≤ 2 * (fourthRoot α : ℝ) * (awayEdges W Q).card) :
    targetA W < ∑ e ∈ cleanAway W Q S Eb, sideWeight W Q S 0 e := by
  let U := unbalancedEdges (allMatchingEdges Q.claim67.M) (sideDensity W Q S 0) (eta α : ℝ)
  let X := nonextremeEdges (allMatchingEdges Q.claim67.M) (sideDensity W Q S 0) (eta α : ℝ)
  let C := sourceCleanEdges Q.claim67.M (padFinset (large W)) Q.claim67.O
    (rootDensity W S) (Sum.inl Q.A) (eta α : ℝ) Eb
  have hrows := CleanSourceWitness.source_rows W S
  obtain ⟨he, heSmall, _, _⟩ := parameter_bounds hα hα1
  have hU : (U.card : ℝ) ≤ (eta α : ℝ) * paddedHalf (Index W) + 2 := by
    have h := unbalanced_all_card_le_away_add_two Q.claim67 (Sum.inl Q.A) (Sum.inl Q.B)
      (rootDensity W S) (eta α : ℝ)
    have hR : (U.card : ℝ) ≤ ((unbalancedAway W Q S 0).card : ℝ) + 2 := by exact_mod_cast h
    linarith only [hR, hu]
  have hX : (X.card : ℝ) ≤ (eta α : ℝ) * paddedHalf (Index W) + 2 := by
    have h := nonextreme_all_card_le_away_add_two Q.claim67 (Sum.inl Q.A) (Sum.inl Q.B)
      (rootDensity W S) (eta α : ℝ)
    have hR : (X.card : ℝ) ≤ ((nonextremeAway W Q S 0).card : ℝ) + 2 := by exact_mod_cast h
    linarith only [hR, hx]
  have hdelete := source_filter_deletion_sum_le Q.claim67 (Sum.inl Q.A) (Sum.inl Q.B)
    Q.A_in_claim67O (rootDensity W S) W.clusterSize (eta α : ℝ) (by positivity) he
    (by linarith only [heSmall]) (fun e c => hrows.density_nonneg _) hrows.weightA_le hrows.supportA
    U.card X.card Eb.card (le_refl _) (le_refl _) Eb hEb (le_refl _)
  change (∑ e ∈ allMatchingEdges Q.claim67.M \ C, sideWeight W Q S 0 e) ≤ _ at hdelete
  have hUscaled := mul_le_mul_of_nonneg_left hU (show 0 ≤ (2 : ℝ) * W.clusterSize by positivity)
  have hXscaled := mul_le_mul_of_nonneg_left hX (show 0 ≤ (2 : ℝ) * W.clusterSize by positivity)
  have hEbscaled := mul_le_mul_of_nonneg_left hEbcount (show 0 ≤ (2 : ℝ) * W.clusterSize by positivity)
  have ht : (0 : ℝ) ≤ fourthRoot α := by exact_mod_cast (parameter_pos hα).2.2.2.1.le
  have hvolume := mul_le_mul_of_nonneg_left (matchingVolume_bound W Q hhost (allMatchingEdges Q.claim67.M))
    (show 0 ≤ 3 * (eta α : ℝ) by positivity)
  have hreserve := mul_le_mul_of_nonneg_left (matchingVolume_bound W Q hhost (awayEdges W Q))
    (show 0 ≤ 4 * (fourthRoot α : ℝ) by positivity)
  have hdeleted : (∑ e ∈ allMatchingEdges Q.claim67.M \ C, sideWeight W Q S 0 e) ≤
      4 * (eta α : ℝ) * ((paddedHalf (Index W) : ℝ) * W.clusterSize) +
        3 * (eta α : ℝ) * q + 4 * (fourthRoot α : ℝ) * q + 10 * W.clusterSize := by
    nlinarith only [hdelete, hUscaled, hXscaled, hEbscaled, hvolume, hreserve]
  have hsplit := Finset.sum_sdiff
    (sourceCleanEdges_subset_all Q.claim67.M (padFinset (large W)) Q.claim67.O
      (rootDensity W S) (Sum.inl Q.A) (eta α : ℝ) Eb)
    (f := sideWeight W Q S 0)
  have hclean := sum_inter_away_lower W Q S C 0
  have hall := Finset.sum_le_sum_of_subset_of_nonneg
    (edgesAwayFromDistinguished_subset Q.claim67.M (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (fun e _ _ => sideWeight_nonneg W Q S 0 e)
  have htotal := awayWeight_lower W Q S hα hα1 hhost horder 0
  have hgate := (actual_matching_gates W hα hα1 hhost horder).2.1
  change targetA W < ∑ e ∈ C ∩ awayEdges W Q, sideWeight W Q S 0 e
  change (∑ e ∈ allMatchingEdges Q.claim67.M \ C, sideWeight W Q S 0 e) +
    (∑ e ∈ C, sideWeight W Q S 0 e) = _ at hsplit
  linarith only [hdeleted, hsplit, hclean, hall, htotal, hgate]

end Erdos547b.ZhaoSourceNearFullFilters

#print axioms Erdos547b.ZhaoSourceNearFullFilters.sum_inter_away_lower
#print axioms Erdos547b.ZhaoSourceNearFullFilters.cleanAway_weight_gt
