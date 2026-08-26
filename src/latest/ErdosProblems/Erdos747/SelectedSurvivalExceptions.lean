import ErdosProblems.Erdos747.SelectedThinning

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Thinning diagnostics with sample-size-scaled exception counts -/

lemma presentUpperWeightException_probability_le_markov
    {n k e : ℕ} (H : Finset (Edge n)) (delta eta : ℝ)
    (hk : k + 1 ≤ H.card) (hspread : PresentWeightSpread H delta eta) :
    finsetProbability (H.powersetCard (k + 1))
        (fun T ↦ e + 1 ≤ (T.filter fun Z ↦
          (1 + delta) * matchingWeightTarget n H <
            (completionWeight (H \ T) Z : ℝ)).card) ≤
      (((k + 1 : ℕ) : ℝ) * eta) / (e + 1 : ℕ) := by
  let E := presentUpperWeightExceptions H delta
  have hmarkov := powersetCard_exception_probability_le_markov
    H E k (e + 1) eta (Finset.filter_subset _ _) hk (by omega)
      (presentUpperWeightExceptions_card_le_of_spread H delta eta hspread)
  calc
    _ ≤ finsetProbability (H.powersetCard (k + 1))
        (fun T ↦ ((e + 1 : ℕ) : ℝ) ≤ (T.filter fun Z ↦ Z ∈ E).card) := by
      apply finsetProbability_mono_event
      intro T hT hbig
      have hTH := (Finset.mem_powersetCard.mp hT).1
      have hsub : (T.filter fun Z ↦
          (1 + delta) * matchingWeightTarget n H <
            (completionWeight (H \ T) Z : ℝ)) ⊆ T.filter (fun Z ↦ Z ∈ E) := by
        intro Z hZ
        rcases Finset.mem_filter.mp hZ with ⟨hZT, hhigh⟩
        have hmono : (completionWeight (H \ T) Z : ℝ) ≤ completionWeight H Z := by
          exact_mod_cast completionWeight_mono (Finset.sdiff_subset : H \ T ⊆ H) Z
        exact Finset.mem_filter.mpr ⟨hZT,
          Finset.mem_filter.mpr ⟨hTH hZT, hhigh.trans_le hmono⟩⟩
      exact_mod_cast hbig.trans (Finset.card_le_card hsub)
    _ ≤ _ := hmarkov

/-- The lower diagnostic only needs a small conditional failure
probability for each *selected*, initially typical edge. -/
lemma presentLowerWeightException_probability_le_selected
    {n k eLow eFail : ℕ} (H : Finset (Edge n)) (delta eta r a p : ℝ)
    (hk : k + 1 ≤ H.card) (hr : 0 ≤ r) (hp : 0 ≤ p)
    (hspread : PresentWeightSpread H delta eta)
    (ha : a ≤ r * ((1 - delta) * matchingWeightTarget n H))
    (hpoint : ∀ Z ∈ H, Z ∉ presentLowerWeightExceptions H delta →
      finsetProbability ((H.erase Z).powersetCard k)
        (fun U ↦ (completionWeight ((H.erase Z) \ U) Z : ℝ) <
          r * (completionWeight (H.erase Z) Z : ℝ)) ≤ p) :
    finsetProbability (H.powersetCard (k + 1))
        (fun T ↦ eLow + eFail + 1 ≤
          (T.filter fun Z ↦ (completionWeight (H \ T) Z : ℝ) < a).card) ≤
      (((k + 1 : ℕ) : ℝ) * eta) / (eLow + 1 : ℕ) +
        (((k + 1 : ℕ) : ℝ) * p) / (eFail + 1 : ℕ) := by
  let E := presentLowerWeightExceptions H delta
  let P := fun Z T ↦ Z ∉ E ∧ (completionWeight (H \ T) Z : ℝ) <
    r * (completionWeight H Z : ℝ)
  letI : ∀ Z, DecidablePred (P Z) := fun _ ↦ Classical.decPred _
  have hLow := powersetCard_exception_probability_le_markov
    H E k (eLow + 1) eta (Finset.filter_subset _ _) hk (by omega)
      (presentLowerWeightExceptions_card_le_of_spread H delta eta hspread)
  have hLowNat : finsetProbability (H.powersetCard (k + 1))
      (fun T ↦ eLow + 1 ≤ (T.filter fun Z ↦ Z ∈ E).card) ≤
        (((k + 1 : ℕ) : ℝ) * eta) / (eLow + 1 : ℕ) := by
    refine (@finsetProbability_congr_event _ _ _ _ _ _ ?_).le.trans hLow
    intro T hT
    exact_mod_cast Iff.rfl
  have hpoint' : ∀ Z ∈ H,
      finsetProbability ((H.erase Z).powersetCard k) (fun U ↦ P Z (insert Z U)) ≤ p := by
    intro Z hZH
    by_cases hZE : Z ∈ E
    · have hzero : finsetProbability ((H.erase Z).powersetCard k)
          (fun U ↦ P Z (insert Z U)) = 0 := by
        unfold finsetProbability
        have hempty : (((H.erase Z).powersetCard k).filter
            (fun U ↦ P Z (insert Z U))) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro U hU
          exact (Finset.mem_filter.mp hU).2.1 hZE
        rw [hempty]
        simp
      rw [hzero]
      exact hp
    · calc
        _ = finsetProbability ((H.erase Z).powersetCard k)
            (fun U ↦ (completionWeight ((H.erase Z) \ U) Z : ℝ) <
              r * (completionWeight (H.erase Z) Z : ℝ)) := by
          apply finsetProbability_congr_event
          intro U hU
          simp only [P, hZE, not_false_eq_true, true_and,
            completionWeight_sdiff_insert_self, completionWeight_erase_self]
        _ ≤ _ := hpoint Z hZH hZE
  have hFail := powersetCard_many_selected_failures_le H k (eFail + 1) p hk (by omega) P hpoint'
  have hFailNat : finsetProbability (H.powersetCard (k + 1))
      (fun T ↦ eFail + 1 ≤ (T.filter fun Z ↦ P Z T).card) ≤
        (((k + 1 : ℕ) : ℝ) * p) / (eFail + 1 : ℕ) := by
    refine (@finsetProbability_congr_event _ _ _ _ _ _ ?_).le.trans hFail
    intro T hT
    exact_mod_cast Iff.rfl
  calc
    _ ≤ finsetProbability (H.powersetCard (k + 1))
        (fun T ↦ eLow + 1 ≤ (T.filter fun Z ↦ Z ∈ E).card ∨
          eFail + 1 ≤ (T.filter fun Z ↦ P Z T).card) := by
      apply finsetProbability_mono_event
      intro T hT hlarge
      by_contra hnone
      push Not at hnone
      have hTH := (Finset.mem_powersetCard.mp hT).1
      have hsub : (T.filter fun Z ↦ (completionWeight (H \ T) Z : ℝ) < a) ⊆
          (T.filter fun Z ↦ Z ∈ E) ∪ (T.filter fun Z ↦ P Z T) := by
        intro Z hZ
        rcases Finset.mem_filter.mp hZ with ⟨hZT, hlow⟩
        by_cases hZE : Z ∈ E
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hZT, hZE⟩)
        · apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨hZT, hZE, ?_⟩
          have htyp : (1 - delta) * matchingWeightTarget n H ≤ completionWeight H Z := by
            by_contra hbad
            apply hZE
            exact Finset.mem_filter.mpr ⟨hTH hZT, lt_of_not_ge hbad⟩
          exact hlow.trans_le (ha.trans (mul_le_mul_of_nonneg_left htyp hr))
      have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    _ ≤ finsetProbability (H.powersetCard (k + 1))
          (fun T ↦ eLow + 1 ≤ (T.filter fun Z ↦ Z ∈ E).card) +
        finsetProbability (H.powersetCard (k + 1))
          (fun T ↦ eFail + 1 ≤ (T.filter fun Z ↦ P Z T).card) :=
      finsetProbability_or_le_add _ _ _
    _ ≤ _ := add_le_add hLowNat hFailNat

end

end Erdos747
