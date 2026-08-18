/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientSourceHierarchy

/-!
# Source-level high-coefficient post-CFP assembly

This is the finite source wrapper around the complete post-CFP constructor.
The two side witnesses are chosen internally from irreducibility and the
coefficient mass budget; the scalar hierarchy is packaged separately so the
asymptotic theorem can discharge it in one step.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

namespace Theorem4PostCFPData

/-- Complete finite source assembly.  Apart from the scalar hierarchy record,
whose fields are discharged by
`exists_sourceParameters_highCoefficientScalarHierarchies`, the only
remaining geometric premises are the two centered-zonotope thickness
inclusions. -/
def ofHighCoefficientSource
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {delta gamma mu theta : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ))
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (htheta : 0 ≤ theta) (hgamma : 0 < gamma)
    (hcap : 0 < (mu *
      (selector.chosen A hA).identifiedCore.card)⁻¹)
    (hmassBudget :
      (A.card : ℝ) * theta +
          delta * (A.card : ℝ) *
            (mu * (selector.chosen A hA).identifiedCore.card)⁻¹ <
        (1 - 2 *
          (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2) :
    let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
      hdelta htheta hcap hmassBudget
    HighCoefficientScalarHierarchies E →
    (∀ y : Fin (selector.chosen A hA).dimension → ℝ,
      (∀ i, |y i| ≤
        (3 * E.commonCoveringRadius + 2 : ℕ) + E.forwardCenterError) →
      y ∈ centeredZonotope E.forwardRoundingCore
        (D.scaledForwardCoefficient (highCoefficientZonotopeScale D))) →
    (∀ y : Fin (selector.chosen A hA).dimension → ℝ,
      (∀ i, |y i| ≤
        (3 * E.commonCoveringRadius + 2 : ℕ) + E.reverseCenterError) →
      y ∈ centeredZonotope E.reverseRoundingCore
        (D.scaledReverseCoefficient (highCoefficientZonotopeScale D))) →
    Theorem4PostCFPData (selector.chosen A hA).identifiedCore := by
  dsimp only
  intro H hthick₁ hthick₂
  let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
    hdelta htheta hcap hmassBudget
  exact ofHighCoefficientSideSelection D E
    (selectedDimension_pos_of_coreRetention selector hdelta hcoreRetention)
    hmu htheta hgamma H.full₁ H.full₂ H.anisotropic₁ H.anisotropic₂
    hthick₁ hthick₂

/-- Source-asymptotic form of the finite assembly.  The exponents and the
context-dependent population threshold are chosen first, the coefficient
cutoff is the fixed inverse-cardinality cutoff, and all four scalar
hierarchies are discharged internally.  Thus the exact residual after the
existing source parameter assumptions consists of the coefficient mass
budget and the two zonotope-thickness inclusions. -/
theorem exists_sourceParameters_ofHighCoefficientSource
    {beta eta : ℝ} (rankCeiling : ℕ) (heta : (1 : ℝ) / 2 < eta) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ (context : Reduction.HigherDimensionalContext beta eta),
      ∃ M : ℕ,
      ∀ (selector : Reduction.BoundedCFPSelector context)
        {ambient : ℕ} (A : Finset (LatticePoint ambient))
        (hA : selector.Eligible A)
        (hrank : (selector.chosen A hA).dimension ≤ rankCeiling)
        (delta gamma mu : ℝ)
        (hparams : Theorem4Parameters A beta C C' M delta gamma mu)
        (hclosed : selector.CandidateClosedAt A hA delta)
        (hcoreRetention : delta * (A.card : ℝ) ≤
          ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ))
        {a₀ : realImage (selector.chosen A hA).identifiedCore}
        {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
        (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
        (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
          delta gamma)
        (hmassBudget :
          (A.card : ℝ) * sourceCoefficientThreshold A.card +
              delta * (A.card : ℝ) *
                (mu * (selector.chosen A hA).identifiedCore.card)⁻¹ <
            (1 - 2 *
              (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2),
        let theta := sourceCoefficientThreshold A.card
        let hcap : 0 < (mu *
            (selector.chosen A hA).identifiedCore.card)⁻¹ :=
          inv_mu_mul_coreCard_pos_of_coreRetention
            (selector.eligible_nonempty hA).card_pos hparams.delta_pos
              hparams.mu_pos hcoreRetention
        let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
          hparams.delta_pos (sourceCoefficientThreshold_pos
            (selector.eligible_nonempty hA).card_pos).le hcap hmassBudget
        (∀ y : Fin (selector.chosen A hA).dimension → ℝ,
          (∀ i, |y i| ≤
            (3 * E.commonCoveringRadius + 2 : ℕ) + E.forwardCenterError) →
          y ∈ centeredZonotope E.forwardRoundingCore
            (D.scaledForwardCoefficient (highCoefficientZonotopeScale D))) →
        (∀ y : Fin (selector.chosen A hA).dimension → ℝ,
          (∀ i, |y i| ≤
            (3 * E.commonCoveringRadius + 2 : ℕ) + E.reverseCenterError) →
          y ∈ centeredZonotope E.reverseRoundingCore
            (D.scaledReverseCoefficient (highCoefficientZonotopeScale D))) →
        Nonempty (Theorem4PostCFPData
          (selector.chosen A hA).identifiedCore) := by
  obtain ⟨C, C', hC, hC', hcontexts⟩ :=
    exists_sourceParameters_highCoefficientScalarHierarchies rankCeiling heta
  refine ⟨C, C', hC, hC', ?_⟩
  intro context
  obtain ⟨M, hM⟩ := hcontexts context
  refine ⟨M, ?_⟩
  intro selector ambient A hA hrank delta gamma mu hparams hclosed
    hcoreRetention a₀ c D hirr hmassBudget
  dsimp only
  intro hthick₁ hthick₂
  have hN : 0 < A.card := (selector.eligible_nonempty hA).card_pos
  let theta := sourceCoefficientThreshold A.card
  have htheta : 0 ≤ theta := (sourceCoefficientThreshold_pos hN).le
  have hcap : 0 < (mu *
      (selector.chosen A hA).identifiedCore.card)⁻¹ :=
    inv_mu_mul_coreCard_pos_of_coreRetention hN hparams.delta_pos
      hparams.mu_pos hcoreRetention
  let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
    hparams.delta_pos htheta hcap hmassBudget
  have hcoreCard : (selector.chosen A hA).identifiedCore.card ≤ A.card := by
    rw [Reduction.SelectedCFP.card_identifiedCore]
    exact Finset.card_le_card (selector.chosen A hA).witness.core_subset
  have hdense₁ : delta * (A.card : ℝ) ≤ (D.largeA₁ theta).card :=
    D.card_largeA₁_of_budget A.card theta delta hcoreCard htheta hcap
      hparams.delta_pos.le hmassBudget
  have hdense₂ : delta * (A.card : ℝ) ≤ (D.largeA₂ theta).card :=
    D.card_largeA₂_of_budget A.card theta delta hcoreCard htheta hcap
      hparams.delta_pos.le hmassBudget
  have H : HighCoefficientScalarHierarchies E :=
    hM selector A hA hrank delta gamma mu hparams D theta E hdense₁ hdense₂
  exact ⟨ofHighCoefficientSource selector D hirr hclosed hcoreRetention
    hparams.delta_pos hparams.mu_pos htheta hparams.gamma_pos hcap hmassBudget
    H hthick₁ hthick₂⟩

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
