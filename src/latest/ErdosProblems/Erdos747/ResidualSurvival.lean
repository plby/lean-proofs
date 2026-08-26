import ErdosProblems.Erdos747.ThinningGlobal

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Completion-survival means from residual present spreading -/

lemma iidCompletionThinning_mean_bounds_of_residual_presentSpread
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (delta eta : ℝ)
    (hn : 2 ≤ n) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hspread : PresentWeightSpread
      (reindexGraphAway H Z hZ) delta eta)
    (hs : (H \ completionHeavyEdges H Z
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))).Nonempty)
    (hm : ((n - 1 : ℕ) : ℝ) <
      ((H \ completionHeavyEdges H Z
        ((1 + delta) * matchingWeightTarget (n - 1)
          (reindexGraphAway H Z hZ))).card : ℝ)) :
    let J := reindexGraphAway H Z hZ
    let b := (1 + delta) * matchingWeightTarget (n - 1) J
    let s := H \ completionHeavyEdges H Z b
    let w := ((completionMatchings n H Z).card : ℝ)
    w * (1 - ((n - 1 : ℕ) : ℝ) / s.card)^t ≤
        finsetAverage (Finset.univ : Finset (IidSample s t))
          (iidFamilySurvivalCount (completionMatchings n H Z) t) ∧
      finsetAverage (Finset.univ : Finset (IidSample s t))
          (iidFamilySurvivalCount (completionMatchings n H Z) t) ≤
        w * Real.exp
            (-((t : ℝ) * ((n - 1 : ℕ) : ℝ) / s.card)) +
          (eta * (J.card : ℝ) * w) / ((n - 1 : ℕ) : ℝ) := by
  let J := reindexGraphAway H Z hZ
  let b := (1 + delta) * matchingWeightTarget (n - 1) J
  let B := completionHeavyEdges H Z b
  let s := H \ B
  let w := ((completionMatchings n H Z).card : ℝ)
  have hBcard : (B.card : ℝ) ≤ eta * J.card := by
    simpa only [B, b, J] using
      completionHeavyEdges_card_le_of_residual_presentSpread
        H hZ delta eta hdelta hspread
  have hsumBase := sum_completionHeavyEdges_le_card_mul_completionWeight
    H Z b
  have hsumHeavy :
      ∑ A ∈ B, (completionEdgeWeight H Z A : ℝ) ≤
        eta * (J.card : ℝ) * w := by
    calc
      ∑ A ∈ B, (completionEdgeWeight H Z A : ℝ) ≤
          (B.card : ℝ) * w := by
        simpa only [B, w] using hsumBase
      _ ≤ (eta * (J.card : ℝ)) * w :=
        mul_le_mul_of_nonneg_right hBcard (by positivity)
  have hmean := iidCompletionThinning_mean_bounds
    (t := t) H Z b (eta * (J.card : ℝ) * w)
      (by simpa only [s, B, b, J] using hs) hn
      (by simpa only [B] using hsumHeavy)
      (by simpa only [s, B, b, J] using hm)
  simpa only [J, b, B, s, w] using hmean

lemma completionThinning_relative_lower_failure_probability_le
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (delta eta r theta u : ℝ)
    (hn : 2 ≤ n) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hH : H.Nonempty)
    (hspread : PresentWeightSpread
      (reindexGraphAway H Z hZ) delta eta)
    (hs : (H \ completionHeavyEdges H Z
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))).Nonempty)
    (hb : 0 < (1 + delta) * matchingWeightTarget (n - 1)
      (reindexGraphAway H Z hZ))
    (hm : ((n - 1 : ℕ) : ℝ) <
      ((H \ completionHeavyEdges H Z
        ((1 + delta) * matchingWeightTarget (n - 1)
          (reindexGraphAway H Z hZ))).card : ℝ))
    (htheta0 : 0 ≤ theta)
    (htheta : |theta *
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))| ≤ 1 / 2)
    (htCard : t ≤ (H \ completionHeavyEdges H Z
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))).card)
    (hcollision : 2 * t * t ≤
      (H \ completionHeavyEdges H Z
        ((1 + delta) * matchingWeightTarget (n - 1)
          (reindexGraphAway H Z hZ))).card)
    (hbudget :
      r * ((completionMatchings n H Z).card : ℝ) + u ≤
        ((completionMatchings n H Z).card : ℝ) *
          (1 - ((n - 1 : ℕ) : ℝ) /
            (H \ completionHeavyEdges H Z
              ((1 + delta) * matchingWeightTarget (n - 1)
                (reindexGraphAway H Z hZ))).card)^t) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ (completionWeight (H \ T) Z : ℝ) <
          r * ((completionMatchings n H Z).card : ℝ)) ≤
      (t : ℝ) *
          ((completionHeavyEdges H Z
            ((1 + delta) * matchingWeightTarget (n - 1)
              (reindexGraphAway H Z hZ))).card : ℝ) / H.card +
        2 * Real.exp
          (theta^2 * ((t : ℝ) *
            (((completionMatchings n H Z).card : ℝ) *
              ((n - 1 : ℕ) : ℝ) /
                (H \ completionHeavyEdges H Z
                  ((1 + delta) * matchingWeightTarget (n - 1)
                    (reindexGraphAway H Z hZ))).card)) *
              ((1 + delta) * matchingWeightTarget (n - 1)
                (reindexGraphAway H Z hZ)) - theta * u) := by
  let J := reindexGraphAway H Z hZ
  let b := (1 + delta) * matchingWeightTarget (n - 1) J
  let s := H \ completionHeavyEdges H Z b
  let w := ((completionMatchings n H Z).card : ℝ)
  let avg := finsetAverage (Finset.univ : Finset (IidSample s t))
    (iidFamilySurvivalCount (completionMatchings n H Z) t)
  have hmeans := iidCompletionThinning_mean_bounds_of_residual_presentSpread
    (t := t) H hZ delta eta hn hdelta heta hspread hs hm
  have hlower : w * (1 - ((n - 1 : ℕ) : ℝ) / s.card)^t ≤ avg := by
    simpa only [J, b, s, w, avg] using hmeans.1
  have htail := powersetCard_completionThinning_lower_tail_full_le
    H Z b theta u (by omega) hZ hH (by simpa only [s, b, J] using hs)
      (by simpa only [b, J] using hb) htheta0
      (by simpa only [b, J] using htheta)
      (by simpa only [s, b, J] using htCard)
      (by simpa only [s, b, J] using hcollision)
  calc
    finsetProbability (H.powersetCard t)
        (fun T ↦ (completionWeight (H \ T) Z : ℝ) < r * w) ≤
      finsetProbability (H.powersetCard t)
        (fun T ↦ u ≤ avg - (completionWeight (H \ T) Z : ℝ)) := by
      apply finsetProbability_mono_event
      intro T hT hbad
      have hb' : r * w + u ≤
          w * (1 - ((n - 1 : ℕ) : ℝ) / s.card)^t := by
        simpa only [J, b, s, w] using hbudget
      linarith
    _ ≤ _ := by simpa only [J, b, s, w, avg] using htail

lemma completionThinning_relative_upper_failure_probability_le
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (delta eta r theta u : ℝ)
    (hn : 2 ≤ n) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hH : H.Nonempty)
    (hspread : PresentWeightSpread
      (reindexGraphAway H Z hZ) delta eta)
    (hs : (H \ completionHeavyEdges H Z
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))).Nonempty)
    (hb : 0 < (1 + delta) * matchingWeightTarget (n - 1)
      (reindexGraphAway H Z hZ))
    (hm : ((n - 1 : ℕ) : ℝ) <
      ((H \ completionHeavyEdges H Z
        ((1 + delta) * matchingWeightTarget (n - 1)
          (reindexGraphAway H Z hZ))).card : ℝ))
    (htheta0 : 0 ≤ theta)
    (htheta : |theta *
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))| ≤ 1 / 2)
    (htCard : t ≤ (H \ completionHeavyEdges H Z
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))).card)
    (hcollision : 2 * t * t ≤
      (H \ completionHeavyEdges H Z
        ((1 + delta) * matchingWeightTarget (n - 1)
          (reindexGraphAway H Z hZ))).card)
    (hbudget :
      ((completionMatchings n H Z).card : ℝ) *
          Real.exp (-((t : ℝ) * ((n - 1 : ℕ) : ℝ) /
            (H \ completionHeavyEdges H Z
              ((1 + delta) * matchingWeightTarget (n - 1)
                (reindexGraphAway H Z hZ))).card)) +
        (eta * ((reindexGraphAway H Z hZ).card : ℝ) *
            ((completionMatchings n H Z).card : ℝ)) /
          ((n - 1 : ℕ) : ℝ) + u ≤
        r * ((completionMatchings n H Z).card : ℝ)) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ r * ((completionMatchings n H Z).card : ℝ) <
          (completionWeight (H \ T) Z : ℝ)) ≤
      (t : ℝ) *
          ((completionHeavyEdges H Z
            ((1 + delta) * matchingWeightTarget (n - 1)
              (reindexGraphAway H Z hZ))).card : ℝ) / H.card +
        2 * Real.exp
          (theta^2 * ((t : ℝ) *
            (((completionMatchings n H Z).card : ℝ) *
              ((n - 1 : ℕ) : ℝ) /
                (H \ completionHeavyEdges H Z
                  ((1 + delta) * matchingWeightTarget (n - 1)
                    (reindexGraphAway H Z hZ))).card)) *
              ((1 + delta) * matchingWeightTarget (n - 1)
                (reindexGraphAway H Z hZ)) - theta * u) := by
  let J := reindexGraphAway H Z hZ
  let b := (1 + delta) * matchingWeightTarget (n - 1) J
  let s := H \ completionHeavyEdges H Z b
  let w := ((completionMatchings n H Z).card : ℝ)
  let avg := finsetAverage (Finset.univ : Finset (IidSample s t))
    (iidFamilySurvivalCount (completionMatchings n H Z) t)
  have hmeans := iidCompletionThinning_mean_bounds_of_residual_presentSpread
    (t := t) H hZ delta eta hn hdelta heta hspread hs hm
  have hupper : avg ≤
      w * Real.exp (-((t : ℝ) * ((n - 1 : ℕ) : ℝ) / s.card)) +
        (eta * (J.card : ℝ) * w) / ((n - 1 : ℕ) : ℝ) := by
    simpa only [J, b, s, w, avg] using hmeans.2
  have htail := powersetCard_completionThinning_upper_tail_full_le
    H Z b theta u (by omega) hZ hH (by simpa only [s, b, J] using hs)
      (by simpa only [b, J] using hb) htheta0
      (by simpa only [b, J] using htheta)
      (by simpa only [s, b, J] using htCard)
      (by simpa only [s, b, J] using hcollision)
  calc
    finsetProbability (H.powersetCard t)
        (fun T ↦ r * w < (completionWeight (H \ T) Z : ℝ)) ≤
      finsetProbability (H.powersetCard t)
        (fun T ↦ u ≤ (completionWeight (H \ T) Z : ℝ) - avg) := by
      apply finsetProbability_mono_event
      intro T hT hbad
      have hb' :
          w * Real.exp (-((t : ℝ) * ((n - 1 : ℕ) : ℝ) / s.card)) +
              (eta * (J.card : ℝ) * w) / ((n - 1 : ℕ) : ℝ) + u ≤
            r * w := by
        simpa only [J, b, s, w] using hbudget
      linarith
    _ ≤ _ := by simpa only [J, b, s, w, avg] using htail

end

end Erdos747
