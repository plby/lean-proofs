import ErdosProblems.Erdos747.DeletionClosure

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## One fixed-edge structural layer -/

def KahnLayerInput (n d D codegCap Q b B e₁ : ℕ)
    (C₀ L eta cTransfer : ℝ) (H : Finset (Edge n)) : Prop :=
  KahnCountLower H C₀ →
    GlobalUpperWeightSpread n H L eta ∧
      CoordinateTransferRegularAwayAboveMax
        n H cTransfer d D codegCap Q b B e₁

lemma maximumWeightDominated_mono
    {n : ℕ} {H : Finset (Edge n)} {q c q' c' : ℝ}
    (hq : q' ≤ q) (hc : c' ≤ c)
    (h : MaximumWeightDominated n H q c) :
    MaximumWeightDominated n H q' c' := by
  rcases h with ⟨Z₀, hZ₀, hmax, hlarge⟩
  refine ⟨Z₀, hZ₀, hmax, ?_⟩
  have hsub :
      (allEdges n).filter (fun U ↦
        c * (completionWeight H Z₀ : ℝ) ≤ completionWeight H U) ⊆
      (allEdges n).filter (fun U ↦
        c' * (completionWeight H Z₀ : ℝ) ≤ completionWeight H U) := by
    intro U hU
    rcases Finset.mem_filter.mp hU with ⟨hUall, hUc⟩
    apply Finset.mem_filter.mpr
    refine ⟨hUall, ?_⟩
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans hUc
  have hcard := Finset.card_le_card hsub
  calc
    q' * (allEdges n).card ≤ q * (allEdges n).card :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ (((allEdges n).filter fun U ↦
        c * (completionWeight H Z₀ : ℝ) ≤ completionWeight H U).card : ℝ) :=
      hlarge
    _ ≤ (((allEdges n).filter fun U ↦
        c' * (completionWeight H Z₀ : ℝ) ≤ completionWeight H U).card : ℝ) := by
      exact_mod_cast hcard

lemma kahnLayerInput_implies_bootstrap_conclusion
    {n d D codegCap Q b B e₀ e₁ : ℕ}
    {H : Finset (Edge n)} {C₀ L eta q c cTransfer : ℝ}
    (hn : 2 ≤ n) (hc0 : 0 ≤ cTransfer) (hc1 : cTransfer ≤ 1)
    (hdb : b < d) (hB : 3 * B ≤ e₀ * (Q + 1))
    (he : 2 * (e₀ + e₁) + 12 ≤ n)
    (hq : q ≤ (((n / 2 : ℕ) : ℝ)^3 / (allEdges n).card))
    (hcPow : c ≤ cTransfer^3)
    (hcount : KahnCountLower H C₀)
    (hinput : KahnLayerInput n d D codegCap Q b B e₁
      C₀ L eta cTransfer H) :
    GlobalUpperWeightSpread n H L eta ∧
      MaximumWeightDominated n H q c := by
  rcases hinput hcount with ⟨hupper, hregular⟩
  refine ⟨hupper, ?_⟩
  have hmax := maximumWeightDominated_of_coordinateTransferRegularAwayAboveMax
    hn hc0 hc1 hdb hB he hregular
  exact maximumWeightDominated_mono hq hcPow hmax

lemma kahnStructuralFailure_probability_le_layerInput_failure
    {n M d D codegCap Q b B e₀ e₁ : ℕ}
    {C₀ L eta q c cTransfer : ℝ}
    (hn : 2 ≤ n) (hc0 : 0 ≤ cTransfer) (hc1 : cTransfer ≤ 1)
    (hdb : b < d) (hB : 3 * B ≤ e₀ * (Q + 1))
    (he : 2 * (e₀ + e₁) + 12 ≤ n)
    (hq : q ≤ (((n / 2 : ℕ) : ℝ)^3 / (allEdges n).card))
    (hcPow : c ≤ cTransfer^3) :
    finsetProbability (sample n M)
        (KahnStructuralFailure n C₀ L eta q c) ≤
      finsetProbability (sample n M)
        (fun H ↦ ¬ KahnLayerInput n d D codegCap Q b B e₁
          C₀ L eta cTransfer H) := by
  apply finsetProbability_mono_event
  intro H hHs hfail
  by_contra hgood
  rcases kahnLayerInput_implies_bootstrap_conclusion
    hn hc0 hc1 hdb hB he hq hcPow hfail.1 hgood with
      ⟨hupper, hmax⟩
  unfold KahnStructuralFailure at hfail
  exact hfail.2.elim (fun h ↦ h hupper) (fun h ↦ h hmax)

lemma kahnLayerInput_failure_probability_le
    {n M d D codegCap Q b B e₁ : ℕ}
    {C₀ L eta cTransfer : ℝ} :
    finsetProbability (sample n M)
        (fun H ↦ ¬ KahnLayerInput n d D codegCap Q b B e₁
          C₀ L eta cTransfer H) ≤
      finsetProbability (sample n M)
        (fun H ↦ KahnCountLower H C₀ ∧
          ¬ GlobalUpperWeightSpread n H L eta) +
      finsetProbability (sample n M)
        (fun H ↦ KahnCountLower H C₀ ∧
          ¬ CoordinateTransferRegularAwayAboveMax
            n H cTransfer d D codegCap Q b B e₁) := by
  calc
    finsetProbability (sample n M)
        (fun H ↦ ¬ KahnLayerInput n d D codegCap Q b B e₁
          C₀ L eta cTransfer H) =
      finsetProbability (sample n M)
        (fun H ↦
          (KahnCountLower H C₀ ∧
            ¬ GlobalUpperWeightSpread n H L eta) ∨
          (KahnCountLower H C₀ ∧
            ¬ CoordinateTransferRegularAwayAboveMax
              n H cTransfer d D codegCap Q b B e₁)) := by
        apply finsetProbability_congr_event
        intro H hH
        unfold KahnLayerInput
        tauto
    _ ≤ _ := finsetProbability_or_le_add _ _ _

end

end Erdos747
