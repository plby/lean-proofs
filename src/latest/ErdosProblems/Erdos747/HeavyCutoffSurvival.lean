import ErdosProblems.Erdos747.ResidualHeavyWeightMass

open scoped BigOperators

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Completion survival with an adjustable heavy cutoff -/

lemma completionThinning_relative_lower_failure_le_of_heavy_bounds
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hn : 2 ≤ n) (hZ : Z ∈ allEdges n)
    (b E theta u r pHit : ℝ)
    (hH : H.Nonempty) (hs : (H \ completionHeavyEdges H Z b).Nonempty)
    (hb : 0 < b) (htheta0 : 0 ≤ theta) (htheta : |theta * b| ≤ 1 / 2)
    (htCard : t ≤ (H \ completionHeavyEdges H Z b).card)
    (hcollision : 2 * t * t ≤ (H \ completionHeavyEdges H Z b).card)
    (hm : ((n - 1 : ℕ) : ℝ) < (H \ completionHeavyEdges H Z b).card)
    (hheavy : ∑ A ∈ completionHeavyEdges H Z b,
      (completionEdgeWeight H Z A : ℝ) ≤ E)
    (hhit : (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card ≤ pHit)
    (hbudget :
      r * (completionWeight H Z : ℝ) + u ≤
        (completionWeight H Z : ℝ) *
          (1 - ((n - 1 : ℕ) : ℝ) / (H \ completionHeavyEdges H Z b).card)^t) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ (completionWeight (H \ T) Z : ℝ) <
          r * (completionWeight H Z : ℝ)) ≤
      pHit + 2 * Real.exp
        (theta^2 * ((t : ℝ) * ((completionWeight H Z : ℝ) *
          ((n - 1 : ℕ) : ℝ) / (H \ completionHeavyEdges H Z b).card)) * b -
          theta * u) := by
  let s := H \ completionHeavyEdges H Z b
  let w := (completionWeight H Z : ℝ)
  let avg := finsetAverage (Finset.univ : Finset (IidSample s t))
    (iidFamilySurvivalCount (completionMatchings n H Z) t)
  have hcount : ((completionMatchings n H Z).card : ℝ) = w := by
    dsimp only [w]
    exact_mod_cast (completionWeight_eq_card_completionMatchings
      H Z (by omega) hZ).symm
  have hmean := (iidCompletionThinning_mean_bounds (t := t)
    H Z b E hs hn hheavy hm).1
  have hmean' : w * (1 - ((n - 1 : ℕ) : ℝ) / s.card)^t ≤ avg := by
    simpa only [hcount] using hmean
  have htail := powersetCard_completionThinning_lower_tail_full_le
    H Z b theta u (by omega) hZ hH hs hb htheta0 htheta htCard hcollision
  calc
    finsetProbability (H.powersetCard t)
        (fun T ↦ (completionWeight (H \ T) Z : ℝ) < r * w) ≤
      finsetProbability (H.powersetCard t)
        (fun T ↦ u ≤ avg - (completionWeight (H \ T) Z : ℝ)) := by
      apply finsetProbability_mono_event
      intro T hT hbad
      have hb' : r * w + u ≤
          w * (1 - ((n - 1 : ℕ) : ℝ) / s.card)^t := hbudget
      linarith
    _ ≤ (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card +
        2 * Real.exp
          (theta^2 * ((t : ℝ) * (w * ((n - 1 : ℕ) : ℝ) / s.card)) * b -
            theta * u) := by
      simpa only [hcount] using htail
    _ ≤ pHit + 2 * Real.exp
        (theta^2 * ((t : ℝ) * (w * ((n - 1 : ℕ) : ℝ) / s.card)) * b -
          theta * u) := add_le_add hhit le_rfl

lemma completionThinning_relative_upper_failure_le_of_heavy_bounds
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hn : 2 ≤ n) (hZ : Z ∈ allEdges n)
    (b E theta u r pHit : ℝ)
    (hH : H.Nonempty) (hs : (H \ completionHeavyEdges H Z b).Nonempty)
    (hb : 0 < b) (htheta0 : 0 ≤ theta) (htheta : |theta * b| ≤ 1 / 2)
    (htCard : t ≤ (H \ completionHeavyEdges H Z b).card)
    (hcollision : 2 * t * t ≤ (H \ completionHeavyEdges H Z b).card)
    (hm : ((n - 1 : ℕ) : ℝ) < (H \ completionHeavyEdges H Z b).card)
    (hheavy : ∑ A ∈ completionHeavyEdges H Z b,
      (completionEdgeWeight H Z A : ℝ) ≤ E)
    (hhit : (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card ≤ pHit)
    (hbudget :
      (completionWeight H Z : ℝ) *
          Real.exp (-((t : ℝ) * ((n - 1 : ℕ) : ℝ) /
            (H \ completionHeavyEdges H Z b).card)) +
        E / ((n - 1 : ℕ) : ℝ) + u ≤ r * (completionWeight H Z : ℝ)) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ r * (completionWeight H Z : ℝ) <
          (completionWeight (H \ T) Z : ℝ)) ≤
      pHit + 2 * Real.exp
        (theta^2 * ((t : ℝ) * ((completionWeight H Z : ℝ) *
          ((n - 1 : ℕ) : ℝ) / (H \ completionHeavyEdges H Z b).card)) * b -
          theta * u) := by
  let s := H \ completionHeavyEdges H Z b
  let w := (completionWeight H Z : ℝ)
  let avg := finsetAverage (Finset.univ : Finset (IidSample s t))
    (iidFamilySurvivalCount (completionMatchings n H Z) t)
  have hcount : ((completionMatchings n H Z).card : ℝ) = w := by
    dsimp only [w]
    exact_mod_cast (completionWeight_eq_card_completionMatchings
      H Z (by omega) hZ).symm
  have hmean := (iidCompletionThinning_mean_bounds (t := t)
    H Z b E hs hn hheavy hm).2
  have hmean' : avg ≤
      w * Real.exp (-((t : ℝ) * ((n - 1 : ℕ) : ℝ) / s.card)) +
        E / ((n - 1 : ℕ) : ℝ) := by
    simpa only [hcount] using hmean
  have htail := powersetCard_completionThinning_upper_tail_full_le
    H Z b theta u (by omega) hZ hH hs hb htheta0 htheta htCard hcollision
  calc
    finsetProbability (H.powersetCard t)
        (fun T ↦ r * w < (completionWeight (H \ T) Z : ℝ)) ≤
      finsetProbability (H.powersetCard t)
        (fun T ↦ u ≤ (completionWeight (H \ T) Z : ℝ) - avg) := by
      apply finsetProbability_mono_event
      intro T hT hbad
      have hb' : w * Real.exp (-((t : ℝ) * ((n - 1 : ℕ) : ℝ) / s.card)) +
          E / ((n - 1 : ℕ) : ℝ) + u ≤ r * w := hbudget
      linarith
    _ ≤ (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card +
        2 * Real.exp
          (theta^2 * ((t : ℝ) * (w * ((n - 1 : ℕ) : ℝ) / s.card)) * b -
            theta * u) := by
      simpa only [hcount] using htail
    _ ≤ pHit + 2 * Real.exp
        (theta^2 * ((t : ℝ) * (w * ((n - 1 : ℕ) : ℝ) / s.card)) * b -
          theta * u) := add_le_add hhit le_rfl

end

end Erdos747
