import ErdosProblems.Erdos747.ThinningSpread

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Present-edge exception bounds for the lower thinning diagnostic -/

lemma presentLowerWeightException_probability_le
    {n t eLow eFail : ℕ} (H : Finset (Edge n))
    (delta r a p : ℝ)
    (htH : t ≤ H.card) (hH : H.Nonempty)
    (hcollision : 2 * t * t ≤ H.card)
    (hr : 0 ≤ r)
    (ha : a ≤ r * ((1 - delta) * matchingWeightTarget n H))
    (hpoint : ∀ Z ∈ H,
      finsetProbability (H.powersetCard t)
          (fun T ↦ (completionWeight (H \ T) Z : ℝ) <
            r * (completionWeight H Z : ℝ)) ≤ p)
    (hLowThreshold : (5 / 4 : ℝ) * (t : ℝ) *
      (((presentLowerWeightExceptions H delta).card : ℝ) / H.card) ≤
        (eLow + 1 : ℕ)) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ eLow + eFail + 1 ≤
          (T.filter fun Z ↦
            (completionWeight (H \ T) Z : ℝ) < a).card) ≤
      2 * Real.exp
          (-((t : ℝ) *
            (((presentLowerWeightExceptions H delta).card : ℝ) / H.card)) /
              64) +
        (((H.card : ℝ) * p) / (eFail + 1 : ℕ)) := by
  let E := presentLowerWeightExceptions H delta
  let Fail : Edge n → Finset (Edge n) → Prop := fun Z T ↦
    (completionWeight (H \ T) Z : ℝ) <
      r * (completionWeight H Z : ℝ)
  letI : ∀ Z, DecidablePred (Fail Z) := fun _ ↦ Classical.decPred _
  have hEH : E ⊆ H := Finset.filter_subset _ _
  have hLow := powersetCard_exception_probability_le H E hEH htH hH
    hcollision (by simpa only [E] using hLowThreshold)
  have hpoint' : ∀ Z ∈ H,
      finsetProbability (H.powersetCard t) (Fail Z) ≤ p := by
    intro Z hZH
    exact (finsetProbability_decidable_irrel
      (H.powersetCard t) (Fail Z) _ _).le.trans (hpoint Z hZH)
  have hmany := finsetProbability_many_finite_events_le
    (H.powersetCard t) H Fail (eFail + 1) p (by omega) hpoint'
  have hmany' :
      finsetProbability (H.powersetCard t)
          (fun T ↦ ((eFail + 1 : ℕ) : ℝ) ≤
            (H.filter fun Z ↦ Fail Z T).card) ≤
        (((H.card : ℝ) * p) / (eFail + 1 : ℕ)) := by
    refine (finsetProbability_congr_event (H.powersetCard t) _ _ ?_).le.trans
      hmany
    intro T hT
    exact Iff.rfl
  calc
    finsetProbability (H.powersetCard t)
        (fun T ↦ eLow + eFail + 1 ≤
          (T.filter fun Z ↦
            (completionWeight (H \ T) Z : ℝ) < a).card) ≤
      finsetProbability (H.powersetCard t)
        (fun T ↦
          eLow + 1 ≤ (T.filter fun Z ↦ Z ∈ E).card ∨
          eFail + 1 ≤ (H.filter fun Z ↦ Fail Z T).card) := by
        apply finsetProbability_mono_event
        intro T hT hlarge
        by_contra hnot
        push Not at hnot
        rcases hnot with ⟨hLowCard, hFailCard⟩
        have hTsub : T ⊆ H := (Finset.mem_powersetCard.mp hT).1
        let Exc := T.filter fun Z ↦
          (completionWeight (H \ T) Z : ℝ) < a
        have hsub : Exc ⊆
            (T.filter fun Z ↦ Z ∈ E) ∪
              (H.filter fun Z ↦ Fail Z T) := by
          intro Z hZ
          rcases Finset.mem_filter.mp hZ with ⟨hZT, hZexc⟩
          by_cases hZE : Z ∈ E
          · exact Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hZT, hZE⟩)
          · apply Finset.mem_union_right
            apply Finset.mem_filter.mpr
            refine ⟨hTsub hZT, ?_⟩
            by_contra hnotFail
            have hsurv : r * (completionWeight H Z : ℝ) ≤
                completionWeight (H \ T) Z := le_of_not_gt hnotFail
            have hnotLow : (1 - delta) * matchingWeightTarget n H ≤
                (completionWeight H Z : ℝ) := by
              have hZE' : ¬ (completionWeight H Z : ℝ) <
                  (1 - delta) * matchingWeightTarget n H := by
                intro hlow
                apply hZE
                exact Finset.mem_filter.mpr ⟨hTsub hZT, hlow⟩
              exact le_of_not_gt hZE'
            have hscaled :
                r * ((1 - delta) * matchingWeightTarget n H) ≤
                  r * (completionWeight H Z : ℝ) :=
              mul_le_mul_of_nonneg_left hnotLow hr
            exact (not_lt_of_ge (ha.trans (hscaled.trans hsurv))) hZexc
        have hcard := Finset.card_le_card hsub
        have hunion := Finset.card_union_le
          (T.filter fun Z ↦ Z ∈ E) (H.filter fun Z ↦ Fail Z T)
        have hLowCard' : (T.filter fun Z ↦ Z ∈ E).card ≤ eLow := by omega
        have hFailCard' : (H.filter fun Z ↦ Fail Z T).card ≤ eFail := by omega
        have hExcCard : Exc.card ≤ eLow + eFail :=
          hcard.trans (hunion.trans (Nat.add_le_add hLowCard' hFailCard'))
        have hlarge' : eLow + eFail < Exc.card := by
          simpa only [Exc] using (show eLow + eFail <
            (T.filter fun Z ↦
              (completionWeight (H \ T) Z : ℝ) < a).card by omega)
        exact (not_lt_of_ge hExcCard) hlarge'
    _ ≤ finsetProbability (H.powersetCard t)
          (fun T ↦ eLow + 1 ≤ (T.filter fun Z ↦ Z ∈ E).card) +
        finsetProbability (H.powersetCard t)
          (fun T ↦ eFail + 1 ≤ (H.filter fun Z ↦ Fail Z T).card) :=
      finsetProbability_or_le_add _ _ _
    _ ≤ 2 * Real.exp
          (-((t : ℝ) *
            (((presentLowerWeightExceptions H delta).card : ℝ) / H.card)) /
              64) +
        (((H.card : ℝ) * p) / (eFail + 1 : ℕ)) := by
      apply add_le_add
      · simpa only [E] using hLow
      · have hcast : ∀ T,
            (eFail + 1 ≤ (H.filter fun Z ↦ Fail Z T).card) ↔
              (((eFail + 1 : ℕ) : ℝ) ≤
                ((H.filter fun Z ↦ Fail Z T).card : ℝ)) := by
          intro T
          exact_mod_cast Iff.rfl
        refine (finsetProbability_congr_event (H.powersetCard t) _ _ ?_).le.trans
          hmany'
        intro T hT
        exact hcast T

end

end Erdos747
