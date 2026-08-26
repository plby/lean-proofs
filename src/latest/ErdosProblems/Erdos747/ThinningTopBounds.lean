import ErdosProblems.Erdos747.ThinningParameterBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def coarseUpperFactor (T : ℝ) : ℝ := 2 / coarseSurvivalFraction T

def coarseLowerFactor (T : ℝ) : ℝ := coarseSurvivalFraction T / 2

lemma coarseSurvivalFraction_le_one (T : ℝ) (hT : 0 ≤ T) :
    coarseSurvivalFraction T ≤ 1 := by
  have he : Real.exp (-8 * T) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith only [hT])
  unfold coarseSurvivalFraction
  linarith only [he]

lemma coarseUpperFactor_ge_two (T : ℝ) (hT : 0 ≤ T) : 2 ≤ coarseUpperFactor T := by
  have hr := coarseSurvivalFraction_pos T
  have hr1 := coarseSurvivalFraction_le_one T hT
  unfold coarseUpperFactor
  apply (le_div_iff₀ hr).mpr
  linarith only [hr1]

lemma coarseUpperBadNonedge_weight_lower_quarter {n : ℕ} (H : Finset (Edge n))
    (T : ℝ) (hT : 0 ≤ T) {Z : Edge n} (hZ : Z ∈ coarseUpperBadNonedges n H (coarseUpperFactor T)) :
    (1 / 2 : ℝ)^2 * matchingWeightTarget n H ≤ completionWeight H Z := by
  have hbad := (Finset.mem_filter.mp hZ).2
  unfold CompletionWeightUpperBound at hbad
  have hhigh := lt_of_not_ge hbad
  have htarget : 0 ≤ matchingWeightTarget n H := by unfold matchingWeightTarget; positivity
  have hfactor := coarseUpperFactor_ge_two T hT
  have h := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ)^2 ≤ coarseUpperFactor T by nlinarith only [hfactor]) htarget
  exact h.trans hhigh.le

lemma presentTypical_weight_lower_quarter {n : ℕ} (H : Finset (Edge n))
    (alpha : ℝ) (halpha : alpha ≤ 1 / 2) {Z : Edge n}
    (hZH : Z ∈ H) (hZtyp : Z ∉ presentLowerWeightExceptions H alpha) :
    (1 / 2 : ℝ)^2 * matchingWeightTarget n H ≤ completionWeight H Z := by
  have hlow : (1 - alpha) * matchingWeightTarget n H ≤ completionWeight H Z := by
    by_contra hbad
    exact hZtyp (Finset.mem_filter.mpr ⟨hZH, lt_of_not_ge hbad⟩)
  have htarget : 0 ≤ matchingWeightTarget n H := by unfold matchingWeightTarget; positivity
  exact (mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ)^2 ≤ 1 - alpha by linarith only [halpha]) htarget).trans hlow

lemma upper_thinning_diagnostic_miss_le
    {n k : ℕ} {H : Finset (Edge n)} (alpha eta T p : ℝ)
    (hH : H ⊆ allEdges n) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (heta : 0 < eta) (halphaEta : alpha ≤ eta / 2) (hT : 0 ≤ T) (hp : 0 ≤ p)
    (hlarge : 16 ≤ eta * (allEdges n).card) (hk : k + 1 ≤ H.card)
    (hspread : PresentWeightSpread H alpha alpha)
    (hglobal : ¬ GlobalUpperWeightSpread n H (coarseUpperFactor T) eta)
    (hrelative : ∀ Z ∈ coarseUpperBadNonedges n H (coarseUpperFactor T),
      finsetProbability (H.powersetCard (k + 1))
        (fun U ↦ (completionWeight (H \ U) Z : ℝ) <
          coarseSurvivalFraction T * (completionWeight H Z : ℝ)) ≤ p) :
    finsetProbability (H.powersetCard (k + 1))
        (fun U ↦ ¬ UpperWeightBlockDiagnostic n (thinningBlockSize (allEdges n).card eta) (k + 1) ⟨H, U⟩) ≤
      2 * p + 100 * alpha / eta := by
  let e := thinningExceptionCount (k + 1) eta
  have hfactor := coarseUpperFactor_ge_two T hT
  have hr := coarseSurvivalFraction_pos T
  have hscale : 1 + alpha ≤ coarseSurvivalFraction T * coarseUpperFactor T := by
    unfold coarseUpperFactor
    rw [mul_div_cancel₀ _ hr.ne']
    linarith only [halphaHalf]
  have hbudget := thinning_global_budget (allEdges n).card H.card eta alpha heta.le hlarge
    (Finset.card_le_card hH) halpha0 halphaEta
  have hdiag : ∀ U ∈ H.powersetCard (k + 1), (e : ℝ) ≤
      (3 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((thinningBlockSize (allEdges n).card eta : ℝ) / (allEdges n \ (H \ U)).card) := by
    intro U hU
    have he := thinning_diagnostic_exception_budget (allEdges n).card
      (allEdges n \ (H \ U)).card (k + 1) eta heta.le hlarge
      (thinning_bottom_card_pos_of_sample hH hU (by omega))
      (Finset.card_le_card (Finset.sdiff_subset : allEdges n \ (H \ U) ⊆ allEdges n))
    have he0 : (0 : ℝ) ≤ e := by positivity
    change 2 * (e : ℝ) ≤ _ at he
    linarith only [he, he0]
  have hraw := upperWeightBlockDiagnostic_top_miss_le_selected
    (d := thinningBlockSize (allEdges n).card eta) (e := e)
    (show 1 + alpha ≤ coarseUpperFactor T by linarith only [halphaHalf, hfactor])
    hspread hbudget hglobal hk hp hr hscale hdiag hrelative
  exact hraw.trans (add_le_add le_rfl (thinningExceptionCount_scaled_ratio_le (k + 1) eta alpha heta halpha0))

lemma lower_thinning_diagnostic_miss_le
    {n k : ℕ} {H : Finset (Edge n)} (alpha eta T p : ℝ)
    (hH : H ⊆ allEdges n) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (heta : 0 < eta) (halphaEta : alpha ≤ eta / 2) (hT : 0 ≤ T) (hp : 0 ≤ p)
    (hlarge : 16 ≤ eta * (allEdges n).card) (hk : k + 1 ≤ H.card)
    (hspread : PresentWeightSpread H alpha alpha)
    (hglobal : ¬ GlobalLowerWeightSpread n H (coarseLowerFactor T) eta)
    (hrelative : ∀ Z ∈ H, Z ∉ presentLowerWeightExceptions H alpha →
      finsetProbability ((H.erase Z).powersetCard k)
        (fun U ↦ (completionWeight ((H.erase Z) \ U) Z : ℝ) <
          coarseSurvivalFraction T * (completionWeight (H.erase Z) Z : ℝ)) ≤ p) :
    finsetProbability (H.powersetCard (k + 1))
        (fun U ↦ ¬ LowerWeightBlockDiagnostic n (thinningBlockSize (allEdges n).card eta) (k + 1) ⟨H, U⟩) ≤
      100 * (alpha + p) / eta := by
  let e := thinningExceptionCount (k + 1) eta
  have hr := coarseSurvivalFraction_pos T
  have hr1 := coarseSurvivalFraction_le_one T hT
  have hfactor : coarseLowerFactor T ≤ 1 - alpha := by
    unfold coarseLowerFactor
    linarith only [hr1, halphaHalf]
  have hscale : coarseLowerFactor T ≤ coarseSurvivalFraction T * (1 - alpha) := by
    unfold coarseLowerFactor
    nlinarith only [mul_le_mul_of_nonneg_left halphaHalf hr.le]
  have hbudget := thinning_global_budget (allEdges n).card H.card eta alpha heta.le hlarge
    (Finset.card_le_card hH) halpha0 halphaEta
  have hdiag : ∀ U ∈ H.powersetCard (k + 1), ((e + e : ℕ) : ℝ) ≤
      (3 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((thinningBlockSize (allEdges n).card eta : ℝ) / (allEdges n \ (H \ U)).card) := by
    intro U hU
    have he := thinning_diagnostic_exception_budget (allEdges n).card
      (allEdges n \ (H \ U)).card (k + 1) eta heta.le hlarge
      (thinning_bottom_card_pos_of_sample hH hU (by omega))
      (Finset.card_le_card (Finset.sdiff_subset : allEdges n \ (H \ U) ⊆ allEdges n))
    change 2 * (e : ℝ) ≤ _ at he
    rw [Nat.cast_add]
    linarith only [he]
  have hraw := lowerWeightBlockDiagnostic_top_miss_le_selected
    (d := thinningBlockSize (allEdges n).card eta) (eLow := e) (eFail := e)
    hfactor hspread hbudget hglobal hk hp hr.le hscale hdiag hrelative
  apply hraw.trans
  calc
    _ ≤ 100 * alpha / eta + 100 * p / eta :=
      add_le_add (thinningExceptionCount_scaled_ratio_le (k + 1) eta alpha heta halpha0)
        (thinningExceptionCount_scaled_ratio_le (k + 1) eta p heta hp)
    _ = _ := by ring

end

end Erdos747
