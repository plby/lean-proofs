/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.BoundedSupportHighCoefficientSourceAssembly

/-!
# Source-specialized post-CFP assembly

The paper applies Theorem 4 only in a specialized small-parameter regime.  In
particular it uses `delta < mu / 4` and the fact that the CFP loss is
lower-order compared with the retained population.  These facts are stronger
than the fields of `Theorem4Parameters` alone.

This file keeps the public `ProducesTheorem4PostCFPData` proposition unchanged
and packages the source specialization separately.  Its two loss inequalities
are exactly what is needed to turn the selected-witness estimate
`|A| ≤ |core| + loss` into the coefficient-cap and surviving-mass bounds.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- The finite near-full-core specialization used by the source proof.

The first field records the explicit separation appearing in Lemma 14.  The
other two fields retain enough of `A` after the selected CFP loss to make the
coefficient cap small and to leave positive coefficient mass after deleting a
`delta * |A|` slab. -/
structure SourceSpecializedMassHierarchy
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {d : ℕ} (A : Finset (LatticePoint d))
    (hA : selector.Eligible A) (delta mu : ℝ) : Prop where
  delta_lt_mu_div_four : delta < mu / 4
  cap_after_selectedLoss :
    16 + mu * (selector.chosen A hA).loss ≤ mu * (A.card : ℝ)
  density_after_selectedLoss :
    4 * delta * (A.card : ℝ) +
        mu * (selector.chosen A hA).loss < mu * (A.card : ℝ)

namespace SourceSpecializedMassHierarchy

variable {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {d : ℕ} {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta mu : ℝ}

/-- The selected CFP loss estimate converts the source loss budget into the
literal lower bound `16 ≤ mu * |core|`. -/
theorem sixteen_le_mu_mul_coreCard
    (H : SourceSpecializedMassHierarchy selector A hA delta mu)
    (hmu : 0 < mu) :
    16 ≤ mu * (selector.chosen A hA).identifiedCore.card := by
  let S := selector.chosen A hA
  have hcoreNat : A.card ≤ S.identifiedCore.card + S.loss := by
    rw [S.card_identifiedCore]
    exact S.witness.core_large
  have hcore : (A.card : ℝ) ≤
      (S.identifiedCore.card : ℝ) + (S.loss : ℝ) := by
    exact_mod_cast hcoreNat
  have hmul := mul_le_mul_of_nonneg_left hcore hmu.le
  dsimp only [S] at hmul ⊢
  nlinarith [H.cap_after_selectedLoss]

/-- The same conversion for the source density/loss budget. -/
theorem four_mul_delta_mul_card_lt_mu_mul_coreCard
    (H : SourceSpecializedMassHierarchy selector A hA delta mu)
    (hmu : 0 < mu) :
    4 * delta * (A.card : ℝ) <
      mu * (selector.chosen A hA).identifiedCore.card := by
  let S := selector.chosen A hA
  have hcoreNat : A.card ≤ S.identifiedCore.card + S.loss := by
    rw [S.card_identifiedCore]
    exact S.witness.core_large
  have hcore : (A.card : ℝ) ≤
      (S.identifiedCore.card : ℝ) + (S.loss : ℝ) := by
    exact_mod_cast hcoreNat
  have hmul := mul_le_mul_of_nonneg_left hcore hmu.le
  dsimp only [S] at hmul ⊢
  nlinarith [H.density_after_selectedLoss]

/-- The source specialization discharges the exact high-coefficient mass
budget used by the bounded-support post-CFP constructor. -/
theorem highCoefficient_massBudget
    (H : SourceSpecializedMassHierarchy selector A hA delta mu)
    (hmu : 0 < mu) :
    (A.card : ℝ) * sourceCoefficientThreshold A.card +
          delta * (A.card : ℝ) *
            (mu * (selector.chosen A hA).identifiedCore.card)⁻¹ <
        (1 - 2 *
          (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 := by
  have hN : 0 < A.card := (selector.eligible_nonempty hA).card_pos
  have hcoreMass := H.sixteen_le_mu_mul_coreCard hmu
  have hcoreMassPos :
      0 < mu * (selector.chosen A hA).identifiedCore.card :=
    (by norm_num : (0 : ℝ) < 16).trans_le hcoreMass
  have hcap :
      (mu * (selector.chosen A hA).identifiedCore.card)⁻¹ ≤
        (1 : ℝ) / 16 := by
    rw [inv_le_iff_one_le_mul₀ hcoreMassPos]
    nlinarith
  have hdensity := H.four_mul_delta_mul_card_lt_mu_mul_coreCard hmu
  have hscaled :
      delta * (A.card : ℝ) *
          (mu * (selector.chosen A hA).identifiedCore.card)⁻¹ <
        (1 : ℝ) / 4 := by
    rw [mul_inv_lt_iff₀ hcoreMassPos]
    nlinarith
  rw [card_mul_sourceCoefficientThreshold hN]
  linarith

end SourceSpecializedMassHierarchy

namespace Theorem4PostCFPData

/-- Bounded-support post-CFP construction in the source-specialized regime.
The high-coefficient mass premise of
`ofHighCoefficientSource_boundedSupport` is derived internally. -/
def ofHighCoefficientSource_specialized
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {delta gamma mu : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ))
    (hdelta : 0 < delta) (hmu : 0 < mu) (hgamma : 0 < gamma)
    (Hsource : SourceSpecializedMassHierarchy selector A hA delta mu) :
    let theta := sourceCoefficientThreshold A.card
    let hcap : 0 < (mu *
        (selector.chosen A hA).identifiedCore.card)⁻¹ :=
      inv_mu_mul_coreCard_pos_of_coreRetention
        (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention
    let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
      hdelta (sourceCoefficientThreshold_pos
        (selector.eligible_nonempty hA).card_pos).le hcap
      (Hsource.highCoefficient_massBudget hmu)
    HighCoefficientBoundedSupportScalarHierarchies E →
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
    { Dout : Theorem4PostCFPData
        (selector.chosen A hA).identifiedCore // Dout.a = D.a } := by
  dsimp only
  intro Hscalar hthick₁ hthick₂
  exact ofHighCoefficientSource_boundedSupport selector D hirr hclosed
    hcoreRetention hdelta hmu
    (sourceCoefficientThreshold_pos
      (selector.eligible_nonempty hA).card_pos).le
    hgamma
    (inv_mu_mul_coreCard_pos_of_coreRetention
      (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention)
    (Hsource.highCoefficient_massBudget hmu) Hscalar hthick₁ hthick₂

/-- Uniform hierarchy wrapper in the source-specialized regime.  It removes
the mass-budget premise from the existing bounded-support theorem without
altering `Theorem4PostCFPStatement`.  The only remaining geometric inputs are
the two canonical thickness inclusions already exposed by the slab API. -/
theorem exists_sourceParameters_ofHighCoefficientSource_specialized
    {beta eta : ℝ} (rankCeiling : ℕ) (heta : 0 < eta) :
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
        (Hsource : SourceSpecializedMassHierarchy selector A hA delta mu)
        {a₀ : realImage (selector.chosen A hA).identifiedCore}
        {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
        (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
        (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
          delta gamma),
        let theta := sourceCoefficientThreshold A.card
        let hcap : 0 < (mu *
            (selector.chosen A hA).identifiedCore.card)⁻¹ :=
          inv_mu_mul_coreCard_pos_of_coreRetention
            (selector.eligible_nonempty hA).card_pos hparams.delta_pos
              hparams.mu_pos hcoreRetention
        let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
          hparams.delta_pos (sourceCoefficientThreshold_pos
            (selector.eligible_nonempty hA).card_pos).le hcap
          (Hsource.highCoefficient_massBudget hparams.mu_pos)
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
        ∃ Dout : Theorem4PostCFPData
            (selector.chosen A hA).identifiedCore,
          latticeEuclidean Dout.a =
            (a₀ : EuclideanSpace ℝ
              (Fin (selector.chosen A hA).dimension)) := by
  obtain ⟨C, C', hC, hC', hcontexts⟩ :=
    exists_sourceParameters_ofHighCoefficientSource_boundedSupport
      rankCeiling heta
  refine ⟨C, C', hC, hC', ?_⟩
  intro context
  obtain ⟨M, hM⟩ := hcontexts context
  refine ⟨M, ?_⟩
  intro selector ambient A hA hrank delta gamma mu hparams hclosed
    hcoreRetention Hsource a₀ c D hirr
  dsimp only
  intro hthick₁ hthick₂
  exact hM selector A hA hrank delta gamma mu hparams hclosed
    hcoreRetention D hirr (Hsource.highCoefficient_massBudget hparams.mu_pos)
      hthick₁ hthick₂

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
