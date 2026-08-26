/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.ThresholdClusterCut
import ErdosProblems.Erdos547b.SourceClaim618FromHost

/-! # The actual pair-pruned ordinary crossing, including low-density pairs -/

open scoped SimpleGraph Classical
noncomputable section
namespace Erdos547b.ZhaoSourceOrdinaryCut

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceNearFullNumerics
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceThresholdGraphs
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoThresholdClusterCut

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)

def coefficient : ℝ := 16 * ((rho α : ℝ) + (rhoOne α : ℝ)) + 4 * (eta α : ℝ)

theorem side_product_le : (O.D.V1.card : ℝ) * O.D.V2.card ≤ (paddedHalf (Index W) : ℝ) ^ 2 := by
  have hv2 := O.D.V2_card
  rw [card_evenPadding] at hv2
  change O.D.V2.card = 2 * paddedHalf (Index W) - O.D.V1.card at hv2
  have hv1 : O.D.V1.card ≤ paddedHalf (Index W) := O.D.V1_card_upper
  have hs : O.D.V1.card + O.D.V2.card = 2 * paddedHalf (Index W) := by omega
  have hsR : (O.D.V1.card : ℝ) + O.D.V2.card = 2 * paddedHalf (Index W) := by exact_mod_cast hs
  nlinarith only [hsR, sq_nonneg ((O.D.V1.card : ℝ) - O.D.V2.card)]

theorem padded_volume_square_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    ((paddedHalf (Index W) : ℝ) * W.clusterSize) ^ 2 ≤ 2 * (q : ℝ) ^ 2 := by
  have hvol := (sharp_paddedVolume W hα hα1 hhost horder).2
  have hN : (W.clusterSize : ℝ) ≤ (degreeError α : ℝ) * q / 500 := by
    subst hostN
    exact (degreeForm_source_bounds hα hα1 W horder).2.2
  have hd : (degreeError α : ℝ) ≤ 1 := by
    exact_mod_cast (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
  have hdq := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hvol' : (paddedHalf (Index W) : ℝ) * W.clusterSize ≤ (501 / 500 : ℝ) * q := by
    linarith only [hvol, hN, hdq]
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (paddedHalf (Index W) : ℝ) * W.clusterSize) hvol' 2
  nlinarith only [hsq, sq_nonneg (q : ℝ)]

theorem ordinary_crossing_lt (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hcross : (((threshold W (4 * (eta α : ℝ))).interedges O.D.V1 O.D.V2).card : ℝ) <
      16 * ((rho α : ℝ) + (rhoOne α : ℝ)) * (paddedHalf (Index W) : ℝ) ^ 2) :
    (((host W).interedges (clusterUnion (padAssignment (assignment W)) O.D.V1)
      (clusterUnion (padAssignment (assignment W)) O.D.V2)).card : ℝ) <
      2 * coefficient (α := α) * (q : ℝ) ^ 2 := by
  have he : (0 : ℝ) < eta α := by exact_mod_cast (parameter_pos hα).2.2.1
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hcoef : 0 ≤ coefficient (α := α) := by
    have hr : (0 : ℝ) < rho α := by exact_mod_cast (parameter_pos hα).2.1
    have hr1 : (0 : ℝ) < rhoOne α := by exact_mod_cast (parameter_pos hα).1
    unfold coefficient
    positivity
  have hcluster (i : EvenPadding (Index W)) :
      (clusterVertices (padAssignment (assignment W)) i).card ≤ W.clusterSize := by
    cases i with
    | inl i =>
      rw [clusterVertices_padAssignment_inl, clusterVertices_partitionAssignment]
      exact (W.equal_clusters i.val i.property).le
    | inr d => simp only [clusterVertices_padAssignment_inr, Finset.card_empty]; omega
  have hlow (i j : EvenPadding (Index W)) (hij : ¬(threshold W (4 * (eta α : ℝ))).Adj i j) :
      ((host W).edgeDensity (clusterVertices (padAssignment (assignment W)) i)
        (clusterVertices (padAssignment (assignment W)) j) : ℝ) ≤ 4 * (eta α : ℝ) := by
    change density W i j ≤ _
    exact (lt_of_not_ge (fun h => hij ((threshold_adj_iff W (by positivity) i j).mpr h))).le
  have hlift := thresholded_clusterUnion_crossing_le (padAssignment (assignment W)) (host W)
    (threshold W (4 * (eta α : ℝ))) O.D.V1 O.D.V2 W.clusterSize (4 * (eta α : ℝ))
    (by positivity) hcluster hlow
  have hpair := mul_le_mul_of_nonneg_left (side_product_le W Q S O) (by positivity : 0 ≤ 4 * (eta α : ℝ))
  have hslots : (((threshold W (4 * (eta α : ℝ))).interedges O.D.V1 O.D.V2).card : ℝ) +
      4 * (eta α : ℝ) * O.D.V1.card * O.D.V2.card <
        coefficient (α := α) * (paddedHalf (Index W) : ℝ) ^ 2 := by
    unfold coefficient
    nlinarith only [hcross, hpair]
  have hstrict := mul_lt_mul_of_pos_right hslots (sq_pos_of_pos hN)
  have hvolume := mul_le_mul_of_nonneg_left (padded_volume_square_le W hα hα1 hhost horder) hcoef
  have hresult := hlift.trans_lt hstrict
  have hscale : coefficient (α := α) * (paddedHalf (Index W) : ℝ) ^ 2 * (W.clusterSize : ℝ) ^ 2 ≤
      2 * coefficient (α := α) * (q : ℝ) ^ 2 := by
    nlinarith only [hvolume]
  exact hresult.trans_le hscale

end Erdos547b.ZhaoSourceOrdinaryCut

#print axioms Erdos547b.ZhaoSourceOrdinaryCut.side_product_le
#print axioms Erdos547b.ZhaoSourceOrdinaryCut.padded_volume_square_le
#print axioms Erdos547b.ZhaoSourceOrdinaryCut.ordinary_crossing_lt
