/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.BoxWeightedSlabThickness
import ErdosProblems.Erdos186.PZ.Intersection.BoxWeightedSourceSlabCardinality
import ErdosProblems.Erdos186.PZ.Intersection.WeightedHighCoefficientSourceThickness

/-!
# Source thickness with the anisotropic control-box norm

This is the width-preserving counterpart of the selected weighted thickness
theorem.  Both selected sides contain the coordinate box whose radii are the
same scalar multiple of the source control-box side lengths.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- Simultaneous forward and reverse selected thickness in the anisotropic
source control-box norm. -/
theorem exists_sourceBoxWeightedSelectedThicknessConstants
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (hA : selector.Eligible A)
    (hd : 0 < (selector.chosen A hA).dimension) :
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ {delta gamma mu theta scale radius t : ℝ}
        {a₀ : realImage (selector.chosen A hA).identifiedCore}
        {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
        (D : ConvexPoolsData
          (selector.chosen A hA).identifiedCore a₀ c mu)
        (E : HighCoefficientSideSelectionData selector hA D theta gamma)
        (slab : ℕ),
        Reduction.IsBoundedCoordinateIrreducible selector A hA
            delta gamma →
        selector.CandidateClosedAt A hA delta →
        0 < gamma → 0 < mu → 0 ≤ theta → 0 ≤ scale → 0 < t →
        delta * (A.card : ℝ) ≤ (slab : ℝ) →
        1 ≤ (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
          ((controlIntegerBox (selector.chosen A hA).progression
            (2 * context.scaleDen
              (selector.chosen A hA).dimension)).carrier.card : ℝ) →
        (∀ (Z : Finset
            (LatticePoint (selector.chosen A hA).dimension))
          (hZ : selector.Eligible Z),
          delta * (A.card : ℝ) ≤ (Z.card : ℝ) →
          (2 : ℝ) ^ (selector.chosen A hA).dimension *
              (2 * (context.scaleDen
                (selector.chosen A hA).dimension : ℝ)) ^
                  (selector.chosen A hA).dimension *
              (3 : ℝ) ^ (selector.chosen A hA).dimension * constant *
              (((2 * context.scaleDen
                  (selector.chosen A hA).dimension + 1) ^
                    (selector.chosen A hA).dimension *
                  2 ^ (selector.chosen A hA).dimension : ℕ) : ℝ) <
            ((selector.chosen Z hZ).dilation : ℝ) * gamma) →
        (2 : ℝ) ^ (selector.chosen A hA).dimension *
              (2 * (context.scaleDen
                (selector.chosen A hA).dimension : ℝ)) ^
                  (selector.chosen A hA).dimension *
              (3 : ℝ) ^ (selector.chosen A hA).dimension * constant *
              (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
              (((2 * context.scaleDen
                  (selector.chosen A hA).dimension + 1) ^
                    (selector.chosen A hA).dimension *
                  2 ^ (selector.chosen A hA).dimension : ℕ) : ℝ) <
            gamma →
        radius ≤ t *
          (scale * ((1 - 2 *
              (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 -
                ((selector.chosen A hA).identifiedCore.card : ℝ) * theta) -
            (((E.side₁.loss + E.side₁.reserveBound + slab : ℕ) : ℝ) *
              (scale *
                (mu * (selector.chosen A hA).identifiedCore.card)⁻¹))) →
        radius ≤ t *
          (scale * ((1 - 2 *
              (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 -
                ((selector.chosen A hA).identifiedCore.card : ℝ) * theta) -
            (((E.side₂.loss + E.side₂.reserveBound + slab : ℕ) : ℝ) *
              (scale *
                (mu * (selector.chosen A hA).identifiedCore.card)⁻¹))) →
        ({y : Fin (selector.chosen A hA).dimension → ℝ |
            ∀ i, |y i| ≤ radius * integerBoxSideLength
              (sourceFunctionalControlBox selector hA) i} ⊆
          centeredZonotope E.forwardRoundingCore
            (D.scaledForwardCoefficient scale)) ∧
        ({y : Fin (selector.chosen A hA).dimension → ℝ |
            ∀ i, |y i| ≤ radius * integerBoxSideLength
              (sourceFunctionalControlBox selector hA) i} ⊆
          centeredZonotope E.reverseRoundingCore
            (D.scaledReverseCoefficient scale)) := by
  obtain ⟨factorBound, constant, hconstant, hslabCard⟩ :=
    exists_boxWeightedSourceFunctionalSlabCardinalityConstants
      selector hA hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro delta gamma mu theta scale radius t a₀ c D E slab hirr hclosed
    hgamma hmu htheta hscale ht hdenseSlab hboxScale hlow hfull
    hradius₁ hradius₂
  let B := sourceFunctionalControlBox selector hA
  have hBbody : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B) := by
    apply isConvexBody_boxRealization_publicControlIntegerBox
    · exact Nat.mul_pos (by omega)
        (context.scaleDen_pos (selector.chosen A hA).dimension)
    · intro i
      exact ((selector.chosen A hA).witness.three_le_width i).trans'
        (by omega)
  have hBside : ∀ i, 0 < integerBoxSideLength B i :=
    integerBoxSideLength_pos_of_isConvexBody B hBbody
  constructor
  · let input := Reduction.identifiedTranslate (D.largeA₁ theta) D.a
    let core := canonicalRoundingCore E.side₁.witness
    let cap := scale *
      (mu * (selector.chosen A hA).identifiedCore.card)⁻¹
    let massLower := scale * ((1 - 2 *
      (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 -
        ((selector.chosen A hA).identifiedCore.card : ℝ) * theta)
    have hinputFull : input ⊆ Reduction.identifiedTranslate D.A₁ D.a := by
      dsimp only [input, Reduction.identifiedTranslate, PZ.translate]
      exact Finset.image_mono _ (D.largeA₁_subset theta)
    apply box_subset_centeredZonotope_of_boxWeighted_slabCard B hBside
      input core (canonicalRoundingCore_subset_input E.side₁.witness)
      (D.scaledForwardCoefficient scale)
      (cap := cap) (massLower := massLower) (radius := radius) (t := t)
      (missing := E.side₁.loss + E.side₁.reserveBound) (slab := slab)
    · intro x hx
      exact (D.scaledForwardCoefficient_bounds_on_identifiedTranslate
        hscale x (hinputFull
          (canonicalRoundingCore_subset_input E.side₁.witness hx))).1
    · exact mul_nonneg hscale (inv_nonneg.mpr (mul_nonneg hmu.le
        (by positivity)))
    · intro x hx
      exact (D.scaledForwardCoefficient_bounds_on_identifiedTranslate
        hscale x (hinputFull hx)).2
    · dsimp only [massLower]
      rw [D.sum_scaledForwardCoefficient_identifiedTranslate_largeA₁]
      exact mul_le_mul_of_nonneg_left
        (D.coefficient_mass_lower_largeA₁ htheta) hscale
    · exact card_sdiff_canonicalRoundingCore_le E.side₁.witness
    · exact ht
    · intro f hf
      simpa only [not_le, B] using
        hslabCard hirr hclosed hgamma (D.largeA₁ theta)
          ((D.largeA₁_subset theta).trans
            (D.A₁_subset_erase.trans (Finset.erase_subset _ _)))
          D.a
          ((selector.chosen A hA).identifiedCore_subset_coefficientBox
            D.a_mem)
          E.side₁.witness f t gamma slab rfl hf ht hdenseSlab hboxScale
            hlow hfull
    · simpa only [input, core, cap, massLower, Nat.cast_add,
        add_assoc] using hradius₁
  · let Wrev := reverseEnhancedCFPWitnessOfIdentifiedTranslate
      D.a (D.largeA₂ theta) E.side₂.witness
    let input := orientedTranslate .reverse D.a (D.largeA₂ theta)
    let core := canonicalRoundingCore Wrev
    let cap := scale *
      (mu * (selector.chosen A hA).identifiedCore.card)⁻¹
    let massLower := scale * ((1 - 2 *
      (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 -
        ((selector.chosen A hA).identifiedCore.card : ℝ) * theta)
    have hinputFull : input ⊆ orientedTranslate .reverse D.a D.A₂ := by
      dsimp only [input, orientedTranslate]
      exact Finset.image_mono _ (D.largeA₂_subset theta)
    rw [E.reverseRoundingCore_eq_side]
    apply box_subset_centeredZonotope_of_boxWeighted_slabCard B hBside
      input core (canonicalRoundingCore_subset_input Wrev)
      (D.scaledReverseCoefficient scale)
      (cap := cap) (massLower := massLower) (radius := radius) (t := t)
      (missing := E.side₂.loss + E.side₂.reserveBound) (slab := slab)
    · intro x hx
      exact (D.scaledReverseCoefficient_bounds_on_orientedTranslate
        hscale x (hinputFull
          (canonicalRoundingCore_subset_input Wrev hx))).1
    · exact mul_nonneg hscale (inv_nonneg.mpr (mul_nonneg hmu.le
        (by positivity)))
    · intro x hx
      exact (D.scaledReverseCoefficient_bounds_on_orientedTranslate
        hscale x (hinputFull hx)).2
    · dsimp only [massLower]
      rw [D.sum_scaledReverseCoefficient_orientedTranslate_largeA₂]
      exact mul_le_mul_of_nonneg_left
        (D.coefficient_mass_lower_largeA₂ htheta) hscale
    · exact card_sdiff_canonicalRoundingCore_le Wrev
    · exact ht
    · intro f hf
      have hforward := hslabCard hirr hclosed hgamma (D.largeA₂ theta)
        ((D.largeA₂_subset theta).trans
          (D.A₂_subset_erase.trans (Finset.erase_subset _ _))) D.a
        ((selector.chosen A hA).identifiedCore_subset_coefficientBox
          D.a_mem)
        E.side₂.witness f t gamma slab rfl hf ht hdenseSlab hboxScale
          hlow hfull
      simpa only [not_le, core, Wrev, B] using
        reverseCanonicalRoundingCore_slab_card_le_of_forward
          D.a E.side₂.witness f (t * boxCoefficientMass B f) hforward
    · simpa only [input, core, cap, massLower, Nat.cast_add,
        add_assoc] using hradius₂

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
