/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceExceptionalNumerics
import ErdosProblems.Erdos547b.SourceExceptionalRowBounds
import ErdosProblems.Erdos547b.SourceMatchingVolume
import ErdosProblems.Erdos547b.Lemma612

/-!
# The actual preliminary matching in the small-family case

Use the cardinal allowance twice t times the actual available matching
count. Actual matching volume then pays the opposite-row weight cost;
the possibly padded half is used only for the exceptional exclusion.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSmallReservation

open Finset SimpleGraph
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceExceptionalNumerics
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoSourceMatchingVolume
open Erdos547b.ZhaoLemma612 Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoEvenReducedPadding

theorem small_prefix_gate (t g q N fb : ℝ)
    (ht : 0 ≤ t) (htSmall : t ≤ 1 / 100) (hgSmall : g ≤ t ^ 2 / 1000000)
    (hq : 0 ≤ q) (hNsmall : N ≤ t ^ 2 * q / 500) (hfb : fb ≤ t * q) :
    fb + 3 * g * q + 2 * N ≤ 2 * t * ((1 - 10 * t ^ 2) * q) := by
  have h2 : t ^ 2 ≤ t / 100 := by
    nlinarith only [mul_nonneg ht (sub_nonneg.mpr htSmall)]
  have h3 : t ^ 3 ≤ t / 10000 := by
    have h := mul_le_mul_of_nonneg_right h2 ht
    nlinarith only [h, h2]
  have h2q := mul_le_mul_of_nonneg_right h2 hq
  have h3q := mul_le_mul_of_nonneg_right h3 hq
  have hgq := mul_le_mul_of_nonneg_right hgSmall hq
  nlinarith only [hfb, hNsmall, hgq, h2q, h3q, mul_nonneg ht hq]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

theorem actual_small_prefix_gate (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (fb : ℝ) (hfb : fb ≤ (fourthRoot α : ℝ) * q) :
    fb + 3 * (gamma α : ℝ) * q + 2 * W.clusterSize ≤
      2 * (fourthRoot α : ℝ) * ((1 - 10 * (fourthRoot α : ℝ) ^ 2) * q) := by
  subst hostN
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  have he1 := (parameter_gates hα hα1).2.1
  have he3 : eta α ^ 3 ≤ 1 := pow_le_one₀ hp.2.2.1.le he1
  have htSmallQ : 100 * fourthRoot α ≤ 1 := by linarith only [hu.2.2.2.1, he3]
  have htSmall : (100 : ℝ) * (fourthRoot α : ℝ) ≤ 1 := by exact_mod_cast htSmallQ
  have hd := (reservoir_cleanup_bounds hα hα1).2.2.2.1
  have hgQ : gamma α ≤ fourthRoot α ^ 2 / 1000000 := by
    linarith only [hd, hu.2.2.2.2.2.1, sq_nonneg (fourthRoot α)]
  have hdQ : degreeError α ≤ fourthRoot α ^ 2 := by linarith only [hd, sq_nonneg (fourthRoot α)]
  have hdR : (degreeError α : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 := by exact_mod_cast hdQ
  have hdq := mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  apply small_prefix_gate (fourthRoot α : ℝ) (gamma α : ℝ) q W.clusterSize fb
    (by exact_mod_cast hp.2.2.2.1.le) (by linarith only [htSmall]) (by exact_mod_cast hgQ)
    (Nat.cast_nonneg _)
  · linarith only [hdq, hN]
  · exact hfb

theorem exists_smallReservation (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (s : Fin 2) (fb : ℝ) (hfb0 : 0 ≤ fb) (hfb : fb ≤ (fourthRoot α : ℝ) * q) :
    ∃ Eb : Finset (MatchingEdge Q.claim67.M), Eb ⊆ awayEdges W Q ∧
      fb + 3 * (gamma α : ℝ) * q ≤ ∑ e ∈ Eb, sideWeight W Q S s e ∧
      (∑ e ∈ Eb, sideWeight W Q S s e) < fb + 3 * (gamma α : ℝ) * q + 2 * W.clusterSize ∧
      (Eb.card : ℝ) ≤ 2 * (fourthRoot α : ℝ) * (awayEdges W Q).card ∧
      (Eb.card : ℝ) ≤ (eta α : ℝ) * paddedHalf (Index W) / 2 ∧
      (∀ u : Fin 2, (∑ e ∈ Eb, sideWeight W Q S u e) ≤ 4 * (fourthRoot α : ℝ) * q) := by
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  have hq : (0 : ℝ) < q := by
    have hh := W.five_ordinaryParts_le_host
    have hparts := W.ordinaryParts_pos
    have hqn : 0 < q := by omega
    exact_mod_cast hqn
  have ht : (0 : ℝ) < fourthRoot α := by exact_mod_cast hp.2.2.2.1
  have hg : (0 : ℝ) < gamma α := by exact_mod_cast hp.2.2.2.2.2.2.1
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have he1 := (parameter_gates hα hα1).2.1
  have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self hp.2.2.1.le he1 2
  have h4tQ : 4 * fourthRoot α ≤ eta α := by linarith only [hu.2.2.2.1, he3, hp.2.2.1]
  have h4t : (4 : ℝ) * (fourthRoot α : ℝ) ≤ eta α := by exact_mod_cast h4tQ
  have he1R : (eta α : ℝ) ≤ 1 := by exact_mod_cast he1
  have h2t : 2 * (fourthRoot α : ℝ) ≤ 1 := by linarith only [h4t, he1R, ht]
  have hδ : 10 * (fourthRoot α : ℝ) ^ 2 < 1 := by
    have htQ : fourthRoot α ≤ 1 / 100 := by
      have he31 : eta α ^ 3 ≤ 1 := he3.trans he1
      linarith only [hu.2.2.2.1, he31]
    have ht100Q : 100 * fourthRoot α ≤ 1 := by linarith only [htQ]
    have ht100 : (100 : ℝ) * (fourthRoot α : ℝ) ≤ 1 := by exact_mod_cast ht100Q
    nlinarith only [ht100, ht, sq_nonneg (fourthRoot α : ℝ)]
  have hD : 0 < (1 - 10 * (fourthRoot α : ℝ) ^ 2) * q := mul_pos (sub_pos.mpr hδ) hq
  have htotal := awayWeight_lower W Q S hα hα1 hhost horder s
  have hgate := actual_small_prefix_gate W hα hα1 hhost horder fb hfb
  have htarget : fb + 3 * (gamma α : ℝ) * q ≤ ∑ e ∈ awayEdges W Q, sideWeight W Q S s e := by
    have h2D := mul_le_mul_of_nonneg_right h2t hD.le
    nlinarith only [hgate, h2D, htotal, hN]
  have hcardGate : ((awayEdges W Q).card : ℝ) * (fb + 3 * (gamma α : ℝ) * q + 2 * W.clusterSize) ≤
      (2 * (fourthRoot α : ℝ) * (awayEdges W Q).card) *
        (∑ e ∈ awayEdges W Q, sideWeight W Q S s e) := by
    have hsum := mul_le_mul_of_nonneg_left htotal (show 0 ≤ 2 * (fourthRoot α : ℝ) by positivity)
    have hgate' := hgate.trans hsum
    have h := mul_le_mul_of_nonneg_left hgate' (Nat.cast_nonneg (awayEdges W Q).card : (0 : ℝ) ≤ (awayEdges W Q).card)
    nlinarith only [h]
  obtain ⟨Eb, hEb, hlo, hup, hcount⟩ := exists_small_submatching (awayEdges W Q) (sideWeight W Q S s)
    (fb + 3 * (gamma α : ℝ) * q) (2 * W.clusterSize) (2 * (fourthRoot α : ℝ) * (awayEdges W Q).card)
    (fun e _ => sideWeight_nonneg W Q S s e) (by positivity) (by positivity)
    (fun e _ => sideWeight_le W Q S s e) htarget (hD.trans_le htotal) hcardGate
  have hawayCount : (awayEdges W Q).card ≤ paddedHalf (Index W) :=
    (Finset.card_le_card (edgesAwayFromDistinguished_subset _ _ _ _)).trans
      (allMatchingEdges_card_le_paddedHalf Q.claim67.M Q.claim67.isMatching (padFinset (large W)))
  have hawayCountR : ((awayEdges W Q).card : ℝ) ≤ paddedHalf (Index W) := by exact_mod_cast hawayCount
  have hcountHalf : (Eb.card : ℝ) ≤ (eta α : ℝ) * paddedHalf (Index W) / 2 := by
    have hc := mul_le_mul_of_nonneg_left hawayCountR (show 0 ≤ 2 * (fourthRoot α : ℝ) by positivity)
    have htK := mul_le_mul_of_nonneg_right h4t (Nat.cast_nonneg (paddedHalf (Index W)) : (0 : ℝ) ≤ paddedHalf (Index W))
    nlinarith only [hcount, hc, htK]
  refine ⟨Eb, hEb, hlo, hup, hcount, hcountHalf, ?_⟩
  intro u
  have hsum : (∑ e ∈ Eb, sideWeight W Q S u e) ≤ (2 * W.clusterSize : ℝ) * Eb.card := by
    have h := Finset.sum_le_sum (fun e (_ : e ∈ Eb) => sideWeight_le W Q S u e)
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm (Eb.card : ℝ)] using h
  have hc := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 2 * (W.clusterSize : ℝ) by positivity)
  have hv := mul_le_mul_of_nonneg_left (matchingVolume_bound W Q hhost (awayEdges W Q))
    (show 0 ≤ 4 * (fourthRoot α : ℝ) by positivity)
  nlinarith only [hsum, hc, hv]

end Erdos547b.ZhaoSourceSmallReservation

#print axioms Erdos547b.ZhaoSourceSmallReservation.small_prefix_gate
#print axioms Erdos547b.ZhaoSourceSmallReservation.actual_small_prefix_gate
#print axioms Erdos547b.ZhaoSourceSmallReservation.exists_smallReservation
