import ErdosProblems.Erdos747.AggregateResidualPointwise

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Aggregate top-fibre estimates -/

/-- The lower present-edge exception estimate only needs pointwise survival
for the initially lower-typical edges.  The atypical edges are already paid
for by the hypergeometric exception term. -/
lemma presentLowerWeightException_probability_le_typical
    {n t eLow eFail : ℕ} (H : Finset (Edge n))
    (delta r a p : ℝ)
    (htH : t ≤ H.card) (hH : H.Nonempty)
    (hcollision : 2 * t * t ≤ H.card)
    (hr : 0 ≤ r)
    (ha : a ≤ r * ((1 - delta) * matchingWeightTarget n H))
    (hpoint : ∀ Z ∈ H, Z ∉ presentLowerWeightExceptions H delta →
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
        ((((H \ presentLowerWeightExceptions H delta).card : ℝ) * p) /
          (eFail + 1 : ℕ)) := by
  let E := presentLowerWeightExceptions H delta
  let A := H \ E
  let Fail : Edge n → Finset (Edge n) → Prop := fun Z T ↦
    (completionWeight (H \ T) Z : ℝ) <
      r * (completionWeight H Z : ℝ)
  let : ∀ Z, DecidablePred (Fail Z) := fun _ ↦ Classical.decPred _
  have hEH : E ⊆ H := Finset.filter_subset _ _
  have hLow := powersetCard_exception_probability_le H E hEH htH hH
    hcollision (by simpa only [E] using hLowThreshold)
  have hpoint' : ∀ Z ∈ A,
      finsetProbability (H.powersetCard t) (Fail Z) ≤ p := by
    intro Z hZA
    rcases Finset.mem_sdiff.mp hZA with ⟨hZH, hZE⟩
    exact (finsetProbability_decidable_irrel
      (H.powersetCard t) (Fail Z) _ _).le.trans (hpoint Z hZH hZE)
  have hmany := finsetProbability_many_finite_events_le
    (H.powersetCard t) A Fail (eFail + 1) p (by omega) hpoint'
  have hmany' :
      finsetProbability (H.powersetCard t)
          (fun T ↦ ((eFail + 1 : ℕ) : ℝ) ≤
            (A.filter fun Z ↦ Fail Z T).card) ≤
        (((A.card : ℝ) * p) / (eFail + 1 : ℕ)) := by
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
          eFail + 1 ≤ (A.filter fun Z ↦ Fail Z T).card) := by
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
              (A.filter fun Z ↦ Fail Z T) := by
          intro Z hZ
          rcases Finset.mem_filter.mp hZ with ⟨hZT, hZexc⟩
          by_cases hZE : Z ∈ E
          · exact Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hZT, hZE⟩)
          · apply Finset.mem_union_right
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_sdiff.mpr ⟨hTsub hZT, hZE⟩, ?_⟩
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
          (T.filter fun Z ↦ Z ∈ E) (A.filter fun Z ↦ Fail Z T)
        have hLowCard' : (T.filter fun Z ↦ Z ∈ E).card ≤ eLow := by
          omega
        have hFailCard' : (A.filter fun Z ↦ Fail Z T).card ≤ eFail := by
          omega
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
          (fun T ↦ eFail + 1 ≤ (A.filter fun Z ↦ Fail Z T).card) :=
      finsetProbability_or_le_add _ _ _
    _ ≤ 2 * Real.exp
          (-((t : ℝ) *
            (((presentLowerWeightExceptions H delta).card : ℝ) / H.card)) /
              64) +
        ((((H \ presentLowerWeightExceptions H delta).card : ℝ) * p) /
          (eFail + 1 : ℕ)) := by
      apply add_le_add
      · simpa only [E] using hLow
      · have hcast : ∀ T,
            (eFail + 1 ≤ (A.filter fun Z ↦ Fail Z T).card) ↔
              (((eFail + 1 : ℕ) : ℝ) ≤
                ((A.filter fun Z ↦ Fail Z T).card : ℝ)) := by
          intro T
          exact_mod_cast Iff.rfl
        refine (finsetProbability_congr_event (H.powersetCard t) _ _ ?_).le.trans
          hmany'
        intro T hT
        exact hcast T

/-- A globally upper-bad aggregate predecessor supplies the top-fibre
diagnostic once pointwise relative survival is known for its bad nonedges. -/
lemma upperWeightBlockDiagnostic_top_of_global_failure_and_presentSpread
    {n t d e : ℕ} {H : Finset (Edge n)}
    {L deltaPresent deltaSurvive etaPresent etaGlobal r p topError : ℝ}
    (hL : 1 + deltaPresent ≤ L)
    (hspread : PresentWeightSpread H deltaPresent etaPresent)
    (hglobalBudget : ((2 * d : ℕ) : ℝ) + etaPresent * H.card ≤
      etaGlobal * (allEdges n).card)
    (hglobal : ¬ GlobalUpperWeightSpread n H L etaGlobal)
    (htH : t ≤ H.card) (hHne : H.Nonempty)
    (hcollision : 2 * t * t ≤ H.card)
    (hdiagnostic : ∀ T ∈ H.powersetCard t,
      (e : ℝ) ≤ (3 / 4 : ℝ) * (t : ℝ) *
        ((d : ℝ) / (allEdges n \ (H \ T)).card))
    (hr : 0 < r)
    (hscale : 1 + deltaSurvive ≤ r * L)
    (hrelative : ∀ Z ∈ coarseUpperBadNonedges n H L,
      finsetProbability (H.powersetCard t)
          (fun T ↦ (completionWeight (H \ T) Z : ℝ) <
            r * (completionWeight H Z : ℝ)) ≤ p)
    (hexceptionThreshold : (5 / 4 : ℝ) * (t : ℝ) *
      (((presentUpperWeightExceptions H deltaSurvive).card : ℝ) / H.card) ≤
        (e + 1 : ℕ))
    (htopError :
      (((coarseUpperBadNonedges n H L).card : ℝ) * p) /
          (((coarseUpperBadNonedges n H L).card - d : ℕ) : ℝ) +
        2 * Real.exp
          (-((t : ℝ) *
            (((presentUpperWeightExceptions H deltaSurvive).card : ℝ) /
              H.card)) / 64) ≤ topError) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
      topError := by
  have hlarge : 2 * d < (coarseUpperBadNonedges n H L).card :=
    coarseUpperBadNonedges_card_gt_two_mul_of_not_global_of_spread
      hL hspread hglobalBudget hglobal
  have hpoint : ∀ Z ∈ coarseUpperBadNonedges n H L,
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ (1 + deltaSurvive) * matchingWeightTarget n H <
            (completionWeight (H \ T) Z : ℝ)) ≤ p := by
    intro Z hZ
    apply upperBad_absolute_failure_probability_le_of_relative
      H L ((1 + deltaSurvive) * matchingWeightTarget n H) r p hZ hr
    · have htarget : 0 ≤ matchingWeightTarget n H := by
        unfold matchingWeightTarget
        positivity
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right hscale htarget)
    · exact hrelative Z hZ
  exact upperWeightBlockDiagnostic_top_of_many_badNonedges
    hlarge htH hHne hcollision hdiagnostic hpoint hexceptionThreshold htopError

/-- The lower analogue: present-edge spreading pays for initially atypical
edges, while pointwise survival is required only on the typical present
edges. -/
lemma lowerWeightBlockDiagnostic_top_of_global_failure_and_presentSpread
    {n t d eLow eFail : ℕ} {H : Finset (Edge n)}
    {L deltaPresent etaPresent etaGlobal r p topError : ℝ}
    (hL : L ≤ 1 - deltaPresent)
    (hspread : PresentWeightSpread H deltaPresent etaPresent)
    (hglobalBudget : ((2 * d : ℕ) : ℝ) + etaPresent * H.card ≤
      etaGlobal * (allEdges n).card)
    (hglobal : ¬ GlobalLowerWeightSpread n H L etaGlobal)
    (htH : t ≤ H.card) (hHne : H.Nonempty)
    (hcollision : 2 * t * t ≤ H.card)
    (hdiagnostic : ∀ T ∈ H.powersetCard t,
      ((eLow + eFail : ℕ) : ℝ) ≤
        (3 / 4 : ℝ) * (t : ℝ) *
          ((d : ℝ) / (allEdges n \ (H \ T)).card))
    (hr : 0 ≤ r)
    (hscale : L ≤ r * (1 - deltaPresent))
    (hrelative : ∀ Z ∈ H,
      Z ∉ presentLowerWeightExceptions H deltaPresent →
      finsetProbability (H.powersetCard t)
          (fun T ↦ (completionWeight (H \ T) Z : ℝ) <
            r * (completionWeight H Z : ℝ)) ≤ p)
    (hLowThreshold : (5 / 4 : ℝ) * (t : ℝ) *
      (((presentLowerWeightExceptions H deltaPresent).card : ℝ) / H.card) ≤
        (eLow + 1 : ℕ))
    (htopError :
      2 * Real.exp
          (-((t : ℝ) *
            (((presentLowerWeightExceptions H deltaPresent).card : ℝ) /
              H.card)) / 64) +
        ((((H \ presentLowerWeightExceptions H deltaPresent).card : ℝ) * p) /
          (eFail + 1 : ℕ)) ≤ topError) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
      topError := by
  have hlarge : 2 * d < (predicateLowerBadNonedges H L).card :=
    predicateLowerBadNonedges_card_gt_two_mul_of_not_global_of_spread
      hL hspread hglobalBudget hglobal
  have ha : L * matchingWeightTarget n H ≤
      r * ((1 - deltaPresent) * matchingWeightTarget n H) := by
    have htarget : 0 ≤ matchingWeightTarget n H := by
      unfold matchingWeightTarget
      positivity
    calc
      L * matchingWeightTarget n H ≤
          (r * (1 - deltaPresent)) * matchingWeightTarget n H :=
        mul_le_mul_of_nonneg_right hscale htarget
      _ = r * ((1 - deltaPresent) * matchingWeightTarget n H) := by ring
  have hExc := presentLowerWeightException_probability_le_typical
    (eFail := eFail) H deltaPresent r (L * matchingWeightTarget n H) p htH hHne
      hcollision hr ha hrelative hLowThreshold
  exact lowerWeightBlockDiagnostic_top_of_many_badNonedges
    hlarge hdiagnostic hExc htopError

end

end Erdos747
