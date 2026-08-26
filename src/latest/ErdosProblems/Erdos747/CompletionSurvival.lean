import ErdosProblems.Erdos747.WeightBlocks

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Completion-survival bounds for unordered thinning samples -/

lemma embeddingCompletionThinning_upper_tail_le {n t : ℕ}
    (H : Finset (Edge n)) (Z : Edge n) (s : Finset (Edge n))
    (a b theta u : ℝ) (hs : s.Nonempty) (hb : 0 < b)
    (htheta0 : 0 ≤ theta) (htheta : |theta * b| ≤ 1 / 2)
    (hmean : finsetAverage (Finset.univ : Finset ↥s)
        (fun A ↦ (completionEdgeWeight H Z A.1 : ℝ)) ≤ a)
    (hcap : ∀ A : ↥s, (completionEdgeWeight H Z A.1 : ℝ) ≤ b)
    (ht : 2 * t * t ≤ s.card) :
    finsetProbability
        (Finset.univ : Finset (Fin t ↪ ↥s))
        (fun e ↦ u ≤
          embeddingFamilySurvivalCount (completionMatchings n H Z) e -
            finsetAverage
              (Finset.univ : Finset (IidSample s t))
              (iidFamilySurvivalCount (completionMatchings n H Z) t)) ≤
      2 * Real.exp (theta^2 * ((t : ℝ) * a) * b - theta * u) := by
  let P : (Fin t ↪ ↥s) → Prop := fun e ↦ u ≤
    embeddingFamilySurvivalCount (completionMatchings n H Z) e -
      finsetAverage (Finset.univ : Finset (IidSample s t))
        (iidFamilySurvivalCount (completionMatchings n H Z) t)
  let Q : IidSample s t → Prop := fun omega ↦ u ≤
    iidFamilySurvivalCount (completionMatchings n H Z) t omega -
      finsetAverage (Finset.univ : Finset (IidSample s t))
        (iidFamilySurvivalCount (completionMatchings n H Z) t)
  have hinj := half_le_iid_injective_probability s t ht
  have hcondition := probability_embedding_le_iid_div s t P (1 / 2)
    (by norm_num) hinj
  have hlift :
      finsetProbability (Finset.univ : Finset (IidSample s t))
          (iidLiftedEvent P) ≤
        finsetProbability (Finset.univ : Finset (IidSample s t)) Q := by
    apply finsetProbability_mono_event
    intro omega homega hP
    rcases hP with ⟨hinjOmega, hP⟩
    exact hP
  have htail := iidCompletionSurvival_upper_tail_le
    (t := t) H Z s a b theta u hs hb htheta0 htheta hmean hcap
  calc
    finsetProbability (Finset.univ : Finset (Fin t ↪ ↥s)) P ≤
        finsetProbability (Finset.univ : Finset (IidSample s t))
          (iidLiftedEvent P) / (1 / 2) := hcondition
    _ ≤ finsetProbability (Finset.univ : Finset (IidSample s t)) Q /
          (1 / 2) := by gcongr
    _ ≤ Real.exp (theta^2 * ((t : ℝ) * a) * b - theta * u) /
          (1 / 2) := by
      exact div_le_div_of_nonneg_right htail (by norm_num)
    _ = 2 * Real.exp
          (theta^2 * ((t : ℝ) * a) * b - theta * u) := by ring

lemma powersetCard_completionThinning_lower_tail_le {n t : ℕ}
    (H : Finset (Edge n)) (Z : Edge n) (b theta u : ℝ)
    (hn : 0 < n) (hZ : Z ∈ allEdges n)
    (hs : (H \ completionHeavyEdges H Z b).Nonempty)
    (hb : 0 < b) (htheta0 : 0 ≤ theta)
    (htheta : |theta * b| ≤ 1 / 2)
    (htCard : t ≤ (H \ completionHeavyEdges H Z b).card)
    (hcollision : 2 * t * t ≤
      (H \ completionHeavyEdges H Z b).card) :
    finsetProbability
        ((H \ completionHeavyEdges H Z b).powersetCard t)
        (fun T ↦ u ≤
          finsetAverage
            (Finset.univ : Finset
              (IidSample (H \ completionHeavyEdges H Z b) t))
            (iidFamilySurvivalCount (completionMatchings n H Z) t) -
          (completionWeight (H \ T) Z : ℝ)) ≤
      2 * Real.exp
        (theta^2 * ((t : ℝ) *
          (((completionMatchings n H Z).card : ℝ) *
            ((n - 1 : ℕ) : ℝ) /
              (H \ completionHeavyEdges H Z b).card)) * b - theta * u) := by
  let s := H \ completionHeavyEdges H Z b
  let P : Finset (Edge n) → Prop := fun T ↦ u ≤
    finsetAverage (Finset.univ : Finset (IidSample s t))
        (iidFamilySurvivalCount (completionMatchings n H Z) t) -
      (completionWeight (H \ T) Z : ℝ)
  rw [← historyEdges_probability_eq_sample s htCard P]
  have htail := embeddingCompletionThinning_lower_tail_le
    (t := t) H Z b theta u hs hb htheta0 htheta hcollision
  calc
    finsetProbability
          (Finset.univ : Finset (DeletionHistory s t))
          (fun e ↦ P (historyEdges e)) =
        finsetProbability
          (Finset.univ : Finset (Fin t ↪ ↥s))
          (fun e ↦ u ≤
            finsetAverage (Finset.univ : Finset (IidSample s t))
                (iidFamilySurvivalCount (completionMatchings n H Z) t) -
              embeddingFamilySurvivalCount
                (completionMatchings n H Z) e) := by
      apply finsetProbability_congr_event
      intro e he
      dsimp only [P]
      rw [completionWeight_eq_card_completionMatchings _ Z hn hZ,
        embeddingFamilySurvivalCount_completion_eq H Z s
          (by exact Finset.sdiff_subset) e]
    _ ≤ _ := by simpa only [s] using htail

lemma powersetCard_completionThinning_upper_tail_le {n t : ℕ}
    (H : Finset (Edge n)) (Z : Edge n) (s : Finset (Edge n))
    (a b theta u : ℝ) (hs : s.Nonempty) (hb : 0 < b)
    (hn : 0 < n) (hZ : Z ∈ allEdges n)
    (htheta0 : 0 ≤ theta) (htheta : |theta * b| ≤ 1 / 2)
    (hmean : finsetAverage (Finset.univ : Finset ↥s)
        (fun A ↦ (completionEdgeWeight H Z A.1 : ℝ)) ≤ a)
    (hcap : ∀ A : ↥s, (completionEdgeWeight H Z A.1 : ℝ) ≤ b)
    (hsH : s ⊆ H) (htCard : t ≤ s.card)
    (hcollision : 2 * t * t ≤ s.card) :
    finsetProbability (s.powersetCard t)
        (fun T ↦ u ≤
          (completionWeight (H \ T) Z : ℝ) -
            finsetAverage (Finset.univ : Finset (IidSample s t))
              (iidFamilySurvivalCount (completionMatchings n H Z) t)) ≤
      2 * Real.exp (theta^2 * ((t : ℝ) * a) * b - theta * u) := by
  let P : Finset (Edge n) → Prop := fun T ↦ u ≤
    (completionWeight (H \ T) Z : ℝ) -
      finsetAverage (Finset.univ : Finset (IidSample s t))
        (iidFamilySurvivalCount (completionMatchings n H Z) t)
  rw [← historyEdges_probability_eq_sample s htCard P]
  have htail := embeddingCompletionThinning_upper_tail_le
    (t := t) H Z s a b theta u hs hb htheta0 htheta hmean hcap hcollision
  calc
    finsetProbability
          (Finset.univ : Finset (DeletionHistory s t))
          (fun e ↦ P (historyEdges e)) =
        finsetProbability
          (Finset.univ : Finset (Fin t ↪ ↥s))
          (fun e ↦ u ≤
            embeddingFamilySurvivalCount
                (completionMatchings n H Z) e -
              finsetAverage (Finset.univ : Finset (IidSample s t))
                (iidFamilySurvivalCount
                  (completionMatchings n H Z) t)) := by
      apply finsetProbability_congr_event
      intro e he
      dsimp only [P]
      rw [completionWeight_eq_card_completionMatchings _ Z hn hZ,
        embeddingFamilySurvivalCount_completion_eq H Z s hsH e]
    _ ≤ _ := htail

end

end Erdos747
