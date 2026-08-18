/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientPostCFPAssembly
import ErdosProblems.Erdos186.PZ.Intersection.SourceParameterNumerics

/-!
# Source hierarchies for the two high-coefficient sides

The finite post-CFP constructor exposes two full-rank and two anisotropic
scalar inequalities.  This file discharges all four simultaneously from the
source parameter hierarchy once the source exponent is larger than one half.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- The four scalar inequalities consumed by
`Theorem4PostCFPData.ofHighCoefficientSideSelection`. -/
structure HighCoefficientScalarHierarchies
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu theta gamma : ℝ}
    {D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu}
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) : Prop where
  full₁ :
    ((2 ^ (selector.chosen A hA).dimension *
      (2 * (selector.chosen A hA).dimension + 1) ^
        ((selector.chosen A hA).dimension - 1) *
      sourceControlCardMultiplier selector hA : ℕ) : ℝ) <
      (E.side₁.dilation : ℝ) * gamma
  full₂ :
    ((2 ^ (selector.chosen A hA).dimension *
      (2 * (selector.chosen A hA).dimension + 1) ^
        ((selector.chosen A hA).dimension - 1) *
      sourceControlCardMultiplier selector hA : ℕ) : ℝ) <
      (E.side₂.dilation : ℝ) * gamma
  anisotropic₁ :
    Real.sqrt (((((selector.chosen A hA).dimension *
        E.forwardRoundingCore.card : ℕ)) : ℝ)) *
      (((((selector.chosen A hA).dimension.factorial *
        (2 * sourceControlScale selector hA) ^
          ((selector.chosen A hA).dimension - 1) *
        3 ^ (selector.chosen A hA).dimension : ℕ)) : ℝ)) ≤
      gamma * E.side₁.dilation
  anisotropic₂ :
    Real.sqrt (((((selector.chosen A hA).dimension *
        E.reverseRoundingCore.card : ℕ)) : ℝ)) *
      (((((selector.chosen A hA).dimension.factorial *
        (2 * sourceControlScale selector hA) ^
          ((selector.chosen A hA).dimension - 1) *
        3 ^ (selector.chosen A hA).dimension : ℕ)) : ℝ)) ≤
      gamma * E.side₂.dilation

/-- Choosing the source exponents `C = 2`, `C' = 1` and then a context-
dependent population threshold supplies both scalar hierarchies on both
selected sides.  The displayed density estimates are finite consequences of
the high-coefficient mass budget used to construct `E`; they are kept here so
this numerical theorem is independent of that construction mechanism. -/
theorem exists_sourceParameters_highCoefficientScalarHierarchies
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
        {a₀ : realImage (selector.chosen A hA).identifiedCore}
        {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
        (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
        (theta : ℝ)
        (E : HighCoefficientSideSelectionData selector hA D theta gamma),
        delta * (A.card : ℝ) ≤ (D.largeA₁ theta).card →
        delta * (A.card : ℝ) ≤ (D.largeA₂ theta).card →
        HighCoefficientScalarHierarchies E := by
  refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
  intro context
  obtain ⟨M, hM⟩ := exists_cardThreshold_source_selectedSide_hierarchies
    context rankCeiling heta (by norm_num : (0 : ℝ) < 2)
  refine ⟨M, ?_⟩
  intro selector ambient A hA hrank delta gamma mu hparams a₀ c D theta E
    hdense₁ hdense₂
  let S := selector.chosen A hA
  have hsourceCore : S.identifiedCore.card ≤ A.card := by
    rw [Reduction.SelectedCFP.card_identifiedCore]
    exact Finset.card_le_card S.witness.core_subset
  have hlarge₁ : (D.largeA₁ theta).card ≤ A.card := by
    exact (Finset.card_le_card ((D.largeA₁_subset theta).trans
      (D.A₁_subset_erase.trans (Finset.erase_subset _ _)))).trans hsourceCore
  have hlarge₂ : (D.largeA₂ theta).card ≤ A.card := by
    exact (Finset.card_le_card ((D.largeA₂_subset theta).trans
      (D.A₂_subset_erase.trans (Finset.erase_subset _ _)))).trans hsourceCore
  have hround₁ : E.forwardRoundingCore.card ≤ A.card := by
    calc
      E.forwardRoundingCore.card ≤ E.forwardWitness.core.card :=
        Finset.card_le_card (canonicalRoundingCore_subset_core E.forwardWitness)
      _ ≤ (orientedTranslate .forward D.a (D.largeA₁ theta)).card :=
        Finset.card_le_card E.forwardWitness.core_subset
      _ = (D.largeA₁ theta).card := card_orientedTranslate _ _ _
      _ ≤ A.card := hlarge₁
  have hround₂ : E.reverseRoundingCore.card ≤ A.card := by
    calc
      E.reverseRoundingCore.card ≤ E.reverseWitness.core.card :=
        Finset.card_le_card (canonicalRoundingCore_subset_core E.reverseWitness)
      _ ≤ (orientedTranslate .reverse D.a (D.largeA₂ theta)).card :=
        Finset.card_le_card E.reverseWitness.core_subset
      _ = (D.largeA₂ theta).card := card_orientedTranslate _ _ _
      _ ≤ A.card := hlarge₂
  have H₁ := hM A delta gamma mu hparams
    (r := S.dimension)
    (X := Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
    (Y := E.forwardRoundingCore)
    (selector.input _ E.eligible₁) hrank hround₁
    (by simpa only [Reduction.card_identifiedTranslate] using hdense₁)
  have H₂ := hM A delta gamma mu hparams
    (r := S.dimension)
    (X := Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
    (Y := E.reverseRoundingCore)
    (selector.input _ E.eligible₂) hrank hround₂
    (by simpa only [Reduction.card_identifiedTranslate] using hdense₂)
  refine {
    full₁ := ?_
    full₂ := ?_
    anisotropic₁ := ?_
    anisotropic₂ := ?_ }
  · simpa only [sourceFullRankConstant, sourceControlBoxFactor,
      sourceControlDilation, sourceControlCardMultiplier, sourceControlScale,
      S, HighCoefficientSideSelectionData.side₁,
      Reduction.BoundedCFPSelector.chosen] using H₁.1
  · simpa only [sourceFullRankConstant, sourceControlBoxFactor,
      sourceControlDilation, sourceControlCardMultiplier, sourceControlScale,
      S, HighCoefficientSideSelectionData.side₂,
      Reduction.BoundedCFPSelector.chosen] using H₂.1
  · simpa only [sourceAnisotropicConstant, sourceControlDilation,
      sourceControlScale, S, HighCoefficientSideSelectionData.side₁,
      Reduction.BoundedCFPSelector.chosen, mul_comm] using H₁.2
  · simpa only [sourceAnisotropicConstant, sourceControlDilation,
      sourceControlScale, S, HighCoefficientSideSelectionData.side₂,
      Reduction.BoundedCFPSelector.chosen, mul_comm] using H₂.2

end

end Erdos186.PZ.Intersection
