/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceParameterSchedule
import ErdosProblems.Erdos547b.DegreeFormQuantitative
import ErdosProblems.Erdos547b.EvenReducedPadding

/-!
# Finite order thresholds for the source-faithful degree-form parameters

The definitions are `(PAR-order)` in `tex/547.tex`. The inequalities below
apply to every actual degree-form witness; they do not postulate small
cleanup errors or additional graph structure.
-/

noncomputable section

namespace Erdos547b.ZhaoSourceDegreeFormBounds

open SimpleGraph
open Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoEvenReducedPadding

def reducedHalfLower (α : ℚ) : ℕ :=
  1 + ⌈(1000000 : ℚ) / (densityCutoff α * epsilon α)⌉₊

def requestedClusters (α : ℚ) : ℕ := 2 * reducedHalfLower α

def orderThreshold (α : ℚ) (M : ℕ) : ℕ :=
  5 * M + 1 + ⌈(1000000 : ℚ) * ((M : ℚ) + 1) ^ 2 / epsilon α ^ 4⌉₊

theorem reducedHalfLower_product {α : ℚ} (hα : 0 < α) :
    1000000 < densityCutoff α * epsilon α * (reducedHalfLower α : ℚ) := by
  obtain ⟨_, _, _, _, _, hd, _, he⟩ := parameter_pos hα
  have hp : 0 < densityCutoff α * epsilon α := mul_pos hd he
  have hc := Nat.le_ceil ((1000000 : ℚ) / (densityCutoff α * epsilon α))
  have hfrac : (1000000 : ℚ) / (densityCutoff α * epsilon α) <
      (reducedHalfLower α : ℚ) := by
    unfold reducedHalfLower
    push_cast
    linarith only [hc]
  simpa only [mul_comm] using (div_lt_iff₀ hp).mp hfrac

theorem orderThreshold_product {α : ℚ} (hα : 0 < α) {M q : ℕ}
    (hq : orderThreshold α M ≤ q) :
    (1000000 : ℚ) * ((M : ℚ) + 1) ^ 2 < epsilon α ^ 4 * q := by
  obtain ⟨_, _, _, _, _, _, _, he⟩ := parameter_pos hα
  have hc := Nat.le_ceil ((1000000 : ℚ) * ((M : ℚ) + 1) ^ 2 / epsilon α ^ 4)
  have hceil : ⌈(1000000 : ℚ) * ((M : ℚ) + 1) ^ 2 / epsilon α ^ 4⌉₊ < q := by
    unfold orderThreshold at hq
    omega
  have hceilR : (⌈(1000000 : ℚ) * ((M : ℚ) + 1) ^ 2 / epsilon α ^ 4⌉₊ : ℚ) < q := by
    exact_mod_cast hceil
  have hfrac := hc.trans_lt hceilR
  have hp : 0 < epsilon α ^ 4 := by positivity
  simpa only [mul_comm] using (div_lt_iff₀ hp).mp hfrac

/-- Cleanup estimates with a separate, smaller regular-pair density cutoff.
Only two finite scale comparisons are used, both discharged below from the
explicit cluster-count and order thresholds. -/
theorem degreeForm_cleanup_bounds
    {q m₀ M : ℕ} {ε d : ℚ}
    {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G ε (d / 100) m₀ M)
    (hε : 0 < ε) (hd : 0 < d)
    (hεsmall : (ε : ℝ) ≤ (d : ℝ) / 1000000)
    (hKlarge : 1000 ≤ (d : ℝ) * W.ordinaryParts)
    (hKsmall : 1000000 * (W.ordinaryParts : ℝ) ≤ (d : ℝ) * q) :
    (W.exceptional.card : ℝ) < (d : ℝ) * q ∧
      (W.loss : ℝ) < (d : ℝ) * q ∧
      (W.clusterSize : ℝ) ≤ (d : ℝ) * q / 500 := by
  let K := W.ordinaryParts
  let a := 2 * q / K
  let f := 2 * cleanupFraction ε + (d : ℝ) / 100 + 2 * ordinaryError ε
  have hKpos : (0 : ℝ) < K := by exact_mod_cast W.ordinaryParts_pos
  have hqpos : (0 : ℝ) < q := by
    have h := W.five_ordinaryParts_le_host
    have hk := W.ordinaryParts_pos
    have : 0 < q := by omega
    exact_mod_cast this
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdq : 0 < (d : ℝ) * q := mul_pos hdR hqpos
  have hKhost : (K : ℝ) ≤ (q : ℝ) := by
    have h : (5 : ℝ) * K ≤ 2 * q := by exact_mod_cast W.five_ordinaryParts_le_host
    linarith only [h, hqpos]
  have havgMul : (a : ℝ) * K ≤ 2 * q := by
    exact_mod_cast Nat.div_mul_le_self (2 * q) K
  have havg : (a : ℝ) ≤ (d : ℝ) * q / 500 := by
    have h₁ := mul_le_mul_of_nonneg_right hKlarge (show (0 : ℝ) ≤ a by positivity)
    have h₂ := mul_le_mul_of_nonneg_left havgMul hdR.le
    change 1000 * (a : ℝ) ≤ (d : ℝ) * K * a at h₁
    nlinarith only [h₁, h₂]
  have hm : (W.clusterSize : ℝ) ≤ (a : ℝ) := by exact_mod_cast W.clusterSize_le_average
  have hclean0 : 0 ≤ cleanupFraction ε := (cleanupFraction_pos hε).le
  have hclean : cleanupFraction ε ≤ (ε : ℝ) / 64 := cleanupFraction_le_eps_div
  have hξ := twice_ordinaryError_le_eps hε
  have hf : f ≤ (d : ℝ) / 50 := by
    dsimp only [f]
    linarith only [hclean, hξ, hεsmall, hdR]
  have htotal : (2 : ℝ) * q + K ≤ 3 * q := by linarith only [hKhost]
  have hfTotal : f * ((2 : ℝ) * q + K) ≤ (3 / 50 : ℝ) * d * q := by
    calc
      f * ((2 : ℝ) * q + K) ≤ ((d : ℝ) / 50) * ((2 : ℝ) * q + K) :=
        mul_le_mul_of_nonneg_right hf (by positivity)
      _ ≤ ((d : ℝ) / 50) * (3 * q) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = (3 / 50 : ℝ) * d * q := by ring
  have hone : (1 : ℝ) ≤ (d : ℝ) * q / 1000000 := by
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast W.ordinaryParts_pos
    change 1000000 * (K : ℝ) ≤ (d : ℝ) * q at hKsmall
    linarith only [hKone, hKsmall]
  have hloss := loss_lt_average_add_cleanup W hε (by positivity : 0 < d / 100)
  have hloss' : (W.loss : ℝ) < (a : ℝ) + f * ((2 : ℝ) * q + K) + 1 := by
    simpa only [a, f, K, Nat.cast_mul, Nat.cast_ofNat, Rat.cast_div,
      Rat.cast_ofNat] using hloss
  have hlossBound : (W.loss : ℝ) < (d : ℝ) * q := by
    linarith only [hloss', havg, hfTotal, hone, hdq]
  have hKA : (K : ℝ) * ((a : ℝ) + 1) ≤ 3 * q := by
    nlinarith only [havgMul, hKhost]
  have hcleanupMul := mul_le_mul_of_nonneg_right hclean
    (show (0 : ℝ) ≤ (K : ℝ) * ((a : ℝ) + 1) by positivity)
  have hεMul := mul_le_mul_of_nonneg_left hKA
    (show 0 ≤ (ε : ℝ) / 32 by positivity)
  have hεq := mul_le_mul_of_nonneg_right hεsmall (show (0 : ℝ) ≤ q by positivity)
  have hE := exceptional_card_lt_cleanup_bound W
  have hE' : (W.exceptional.card : ℝ) <
      2 * cleanupFraction ε * ((K : ℝ) * ((a : ℝ) + 1)) + 2 * K := by
    simp only [Nat.cast_add, Nat.cast_one] at hE
    change (W.exceptional.card : ℝ) <
      (K : ℝ) * (cleanupFraction ε * ((a : ℝ) + 1) + 2) +
        cleanupFraction ε * K * ((a : ℝ) + 1) at hE
    nlinarith only [hE]
  have hEBound : (W.exceptional.card : ℝ) < (d : ℝ) * q := by
    change 1000000 * (K : ℝ) ≤ (d : ℝ) * q at hKsmall
    nlinarith only [hE', hcleanupMul, hεMul, hεq, hKsmall, hdq]
  exact ⟨hEBound, hlossBound, hm.trans havg⟩

/-- Both finite scale comparisons follow from the specified thresholds,
uniformly in the host graph and in the chosen regularity witness. -/
theorem ordinary_scale_bounds
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) :
    1000 ≤ (degreeError α : ℝ) * W.ordinaryParts ∧
      1000000 * (W.ordinaryParts : ℝ) ≤ (degreeError α : ℝ) * q := by
  obtain ⟨_, _, _, _, hd, hcut, _, he⟩ := parameter_pos hα
  obtain ⟨_, _, _, _, heSmall, hd1⟩ := reservoir_cleanup_bounds hα hα1
  have he1 : epsilon α ≤ 1 := by linarith only [heSmall, hd1]
  have hk : reducedHalfLower α ≤ W.ordinaryParts := by
    have h := W.twice_requested_le_ordinary
    dsimp only [requestedClusters] at h
    omega
  have hkQ : (reducedHalfLower α : ℚ) ≤ W.ordinaryParts := by exact_mod_cast hk
  have hprod := reducedHalfLower_product hα
  have hcutE : densityCutoff α * epsilon α ≤ degreeError α / 100 := by
    dsimp only [densityCutoff]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he1
      (show 0 ≤ degreeError α / 100 by positivity)
  have hprodUpper := mul_le_mul_of_nonneg_right hcutE
    (show (0 : ℚ) ≤ reducedHalfLower α by positivity)
  have hdegreeK := mul_le_mul_of_nonneg_left hkQ hd.le
  have hlargeQ : (1000 : ℚ) ≤ degreeError α * W.ordinaryParts := by
    linarith only [hprod, hprodUpper, hdegreeK]
  have horder := orderThreshold_product hα hq
  have he4 : epsilon α ^ 4 ≤ degreeError α := by
    have hpow : epsilon α ^ 4 ≤ epsilon α := pow_succ_le_self he.le he1 3
    linarith only [hpow, heSmall, hd]
  have horderUpper := mul_le_mul_of_nonneg_right he4 (show (0 : ℚ) ≤ q by positivity)
  have hMquad : (M : ℚ) ≤ ((M : ℚ) + 1) ^ 2 := by
    nlinarith only [sq_nonneg (M : ℚ), show (0 : ℚ) ≤ M by positivity]
  have hKM : (W.ordinaryParts : ℚ) ≤ M := by exact_mod_cast W.upper_parts
  have hsmallQ : (1000000 : ℚ) * W.ordinaryParts ≤ degreeError α * q := by
    linarith only [horder, horderUpper, hMquad, hKM]
  exact ⟨by exact_mod_cast hlargeQ, by exact_mod_cast hsmallQ⟩

/-- Actual cleanup at the source parameters and explicit order threshold. -/
theorem degreeForm_source_bounds
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) :
    (W.exceptional.card : ℝ) < (degreeError α : ℝ) * q ∧
      (W.loss : ℝ) < (degreeError α : ℝ) * q ∧
      (W.clusterSize : ℝ) ≤ (degreeError α : ℝ) * q / 500 := by
  obtain ⟨_, _, _, _, hd, _, _, he⟩ := parameter_pos hα
  obtain ⟨_, _, _, _, heSmall, _⟩ := reservoir_cleanup_bounds hα hα1
  obtain ⟨hKlarge, hKsmall⟩ := ordinary_scale_bounds hα hα1 W hq
  exact degreeForm_cleanup_bounds W he hd (by exact_mod_cast heSmall) hKlarge hKsmall

/-- The remaining analytic-looking gates in the source-scale Claim-6.1
entry are concrete consequences of the finite order threshold. -/
theorem degreeForm_reservoir_gates
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) :
    (W.exceptional.card : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 * q / 4 ∧
      (W.loss : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 * q / 4 ∧
      (W.clusterSize : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 * q := by
  obtain ⟨hE, hloss, hm⟩ := degreeForm_source_bounds hα hα1 W hq
  obtain ⟨_, _, _, hdSmall, _, _⟩ := reservoir_cleanup_bounds hα hα1
  have hdSmallR : (degreeError α : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 / 100 := by
    exact_mod_cast hdSmall
  have hdq := mul_le_mul_of_nonneg_right hdSmallR (show (0 : ℝ) ≤ q by positivity)
  have hnonneg : 0 ≤ (fourthRoot α : ℝ) ^ 2 * q := by positivity
  refine ⟨?_, ?_, ?_⟩
  · linarith only [hE, hdq, hnonneg]
  · linarith only [hloss, hdq, hnonneg]
  · linarith only [hm, hdq, hnonneg]

/-- The almost-all-target root mask, including its two extra incident
edges at other roots, fits in the final reserved square-root loss budget.
Using all genuine clusters avoids any assumption on an empty padded part. -/
theorem root_truncation_budget
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) :
    (rootTypicality α : ℝ) * W.partition.parts.card * W.clusterSize + 2 <
      (fourthRoot α : ℝ) ^ 2 * q := by
  obtain ⟨hδposQ, hmarginQ⟩ := rootTypicality_margin hα hα1
  have hδpos : (0 : ℝ) < rootTypicality α := by exact_mod_cast hδposQ
  have hmarginQ' : 8 * rootTypicality α < fourthRoot α ^ 2 := by
    linarith only [hmarginQ]
  have hmargin : (8 : ℝ) * rootTypicality α < (fourthRoot α : ℝ) ^ 2 := by
    exact_mod_cast hmarginQ'
  have hqpos : (0 : ℝ) < q := by
    have h := W.five_ordinaryParts_le_host
    have hk := W.ordinaryParts_pos
    have : 0 < q := by omega
    exact_mod_cast this
  have hhost : (W.exceptional.card : ℝ) +
      (W.partition.parts.card : ℝ) * W.clusterSize = 2 * q := by
    exact_mod_cast exceptional_add_clusters_eq_host W
  have hvolume : (W.partition.parts.card : ℝ) * W.clusterSize ≤ 2 * q := by
    linarith only [hhost, show (0 : ℝ) ≤ W.exceptional.card by positivity]
  have hcost := mul_le_mul_of_nonneg_left hvolume hδpos.le
  have hsmall := (ordinary_scale_bounds hα hα1 W hq).2
  have hKone : (1 : ℝ) ≤ W.ordinaryParts := by exact_mod_cast W.ordinaryParts_pos
  obtain ⟨_, _, _, hdSmallQ, _, _⟩ := reservoir_cleanup_bounds hα hα1
  have hdSmall : (degreeError α : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 / 100 := by
    exact_mod_cast hdSmallQ
  have hdq := mul_le_mul_of_nonneg_right hdSmall hqpos.le
  have hlarge : (100000000 : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 * q := by
    linarith only [hsmall, hKone, hdq]
  have hmarginq := mul_lt_mul_of_pos_right hmargin hqpos
  nlinarith only [hcost, hlarge, hmarginq]

end Erdos547b.ZhaoSourceDegreeFormBounds

#print axioms Erdos547b.ZhaoSourceDegreeFormBounds.reducedHalfLower_product
#print axioms Erdos547b.ZhaoSourceDegreeFormBounds.orderThreshold_product
#print axioms Erdos547b.ZhaoSourceDegreeFormBounds.degreeForm_cleanup_bounds
#print axioms Erdos547b.ZhaoSourceDegreeFormBounds.ordinary_scale_bounds
#print axioms Erdos547b.ZhaoSourceDegreeFormBounds.degreeForm_source_bounds
#print axioms Erdos547b.ZhaoSourceDegreeFormBounds.degreeForm_reservoir_gates
#print axioms Erdos547b.ZhaoSourceDegreeFormBounds.root_truncation_budget
