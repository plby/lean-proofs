import ErdosProblems.Erdos747.SampleRestriction

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

/-! ## Completion survival under thinning from the full edge set -/

lemma powersetCard_completionThinning_lower_tail_full_le {n t : ℕ}
    (H : Finset (Edge n)) (Z : Edge n) (b theta u : ℝ)
    (hn : 0 < n) (hZ : Z ∈ allEdges n)
    (hH : H.Nonempty)
    (hs : (H \ completionHeavyEdges H Z b).Nonempty)
    (hb : 0 < b) (htheta0 : 0 ≤ theta)
    (htheta : |theta * b| ≤ 1 / 2)
    (htCard : t ≤ (H \ completionHeavyEdges H Z b).card)
    (hcollision : 2 * t * t ≤
      (H \ completionHeavyEdges H Z b).card) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ u ≤
          finsetAverage
            (Finset.univ : Finset
              (IidSample (H \ completionHeavyEdges H Z b) t))
            (iidFamilySurvivalCount (completionMatchings n H Z) t) -
          (completionWeight (H \ T) Z : ℝ)) ≤
      (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card +
        2 * Real.exp
          (theta^2 * ((t : ℝ) *
            (((completionMatchings n H Z).card : ℝ) *
              ((n - 1 : ℕ) : ℝ) /
                (H \ completionHeavyEdges H Z b).card)) * b - theta * u) := by
  let P : Finset (Edge n) → Prop := fun T ↦ u ≤
    finsetAverage (Finset.univ : Finset
        (IidSample (H \ completionHeavyEdges H Z b) t))
        (iidFamilySurvivalCount (completionMatchings n H Z) t) -
      (completionWeight (H \ T) Z : ℝ)
  letI : DecidablePred P := fun T ↦ Classical.propDecidable (P T)
  have hsplit := powersetCard_probability_le_hit_add_restriction
    H (completionHeavyEdges H Z b)
      (by exact Finset.filter_subset _ _) t P htCard hH
  have htail := powersetCard_completionThinning_lower_tail_le
    H Z b theta u hn hZ hs hb htheta0 htheta htCard hcollision
  calc
    finsetProbability (H.powersetCard t) P ≤
        (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card +
          finsetProbability
            ((H \ completionHeavyEdges H Z b).powersetCard t) P := hsplit
    _ ≤ (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card +
        2 * Real.exp
          (theta^2 * ((t : ℝ) *
            (((completionMatchings n H Z).card : ℝ) *
              ((n - 1 : ℕ) : ℝ) /
                (H \ completionHeavyEdges H Z b).card)) * b - theta * u) :=
      add_le_add_right (by simpa only [P] using htail) _
    _ = _ := by rfl

lemma powersetCard_completionThinning_upper_tail_full_le {n t : ℕ}
    (H : Finset (Edge n)) (Z : Edge n) (b theta u : ℝ)
    (hn : 0 < n) (hZ : Z ∈ allEdges n)
    (hH : H.Nonempty)
    (hs : (H \ completionHeavyEdges H Z b).Nonempty)
    (hb : 0 < b) (htheta0 : 0 ≤ theta)
    (htheta : |theta * b| ≤ 1 / 2)
    (htCard : t ≤ (H \ completionHeavyEdges H Z b).card)
    (hcollision : 2 * t * t ≤
      (H \ completionHeavyEdges H Z b).card) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ u ≤
          (completionWeight (H \ T) Z : ℝ) -
            finsetAverage
              (Finset.univ : Finset
                (IidSample (H \ completionHeavyEdges H Z b) t))
              (iidFamilySurvivalCount (completionMatchings n H Z) t)) ≤
      (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card +
        2 * Real.exp
          (theta^2 * ((t : ℝ) *
            (((completionMatchings n H Z).card : ℝ) *
              ((n - 1 : ℕ) : ℝ) /
                (H \ completionHeavyEdges H Z b).card)) * b - theta * u) := by
  let s := H \ completionHeavyEdges H Z b
  let a := ((completionMatchings n H Z).card : ℝ) *
    ((n - 1 : ℕ) : ℝ) / s.card
  let P : Finset (Edge n) → Prop := fun T ↦ u ≤
    (completionWeight (H \ T) Z : ℝ) -
      finsetAverage (Finset.univ : Finset (IidSample s t))
        (iidFamilySurvivalCount (completionMatchings n H Z) t)
  letI : DecidablePred P := fun T ↦ Classical.propDecidable (P T)
  have hsplit := powersetCard_probability_le_hit_add_restriction
    H (completionHeavyEdges H Z b)
      (by exact Finset.filter_subset _ _) t P htCard hH
  have hmean : finsetAverage (Finset.univ : Finset ↥s)
      (fun A ↦ (completionEdgeWeight H Z A.1 : ℝ)) ≤ a := by
    exact average_completionEdgeWeight_pool_le H
      (completionHeavyEdges H Z b) Z hs
  have hcap : ∀ A : ↥s,
      (completionEdgeWeight H Z A.1 : ℝ) ≤ b := by
    intro A
    exact completionEdgeWeight_le_of_mem_nonheavy H Z b A.2
  have htail := powersetCard_completionThinning_upper_tail_le
    H Z s a b theta u hs hb hn hZ htheta0 htheta hmean hcap
      Finset.sdiff_subset htCard hcollision
  calc
    finsetProbability (H.powersetCard t) P ≤
        (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card +
          finsetProbability (s.powersetCard t) P := hsplit
    _ ≤ (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card +
        2 * Real.exp
          (theta^2 * ((t : ℝ) * a) * b - theta * u) :=
      add_le_add_right (by simpa only [P] using htail) _
    _ = _ := by rfl

end

end Erdos747
