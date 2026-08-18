/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.BoxWeightedZeroCutoffAssembly
import ErdosProblems.Erdos186.PZ.Intersection.SourceUniformBoxWeightedSlabCardinality

/-! # Rank-uniform box-weighted source thickness -/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

namespace ConvexPoolsData

/-- Simultaneous forward and reverse thickness using the deterministic John
constant uniform up to `rankCeiling`. -/
theorem sourceUniformBoxWeightedSelectedThickness
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    (rankCeiling : ℕ)
    (hrank : (selector.chosen A hA).dimension ≤ rankCeiling)
    (hd : 0 < (selector.chosen A hA).dimension)
    {delta gamma mu : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData
      (selector.chosen A hA).identifiedCore a₀ c mu)
    (E : HighCoefficientSideSelectionData selector hA D 0 gamma)
    (slab : ℕ) (t radius : ℝ)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hgamma : 0 < gamma) (hmu : 0 < mu)
    (H : BoxWeightedZeroCutoffScalarHierarchies
      (delta := delta) E
        (sourceBoxWeightedJohnUniformConstant rankCeiling) slab t radius) :
    ({y : Fin (selector.chosen A hA).dimension → ℝ |
        ∀ i, |y i| ≤ radius * integerBoxSideLength
          (sourceFunctionalControlBox selector hA) i} ⊆
      centeredZonotope E.forwardRoundingCore
        (D.scaledForwardCoefficient (highCoefficientZonotopeScale D))) ∧
    ({y : Fin (selector.chosen A hA).dimension → ℝ |
        ∀ i, |y i| ≤ radius * integerBoxSideLength
          (sourceFunctionalControlBox selector hA) i} ⊆
      centeredZonotope E.reverseRoundingCore
        (D.scaledReverseCoefficient (highCoefficientZonotopeScale D))) := by
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
  have hscale : 0 ≤ highCoefficientZonotopeScale D :=
    D.highCoefficientZonotopeScale_nonneg hmu
  constructor
  · let input := Reduction.identifiedTranslate (D.largeA₁ 0) D.a
    let core := canonicalRoundingCore E.side₁.witness
    let cap := highCoefficientZonotopeScale D *
      (mu * (selector.chosen A hA).identifiedCore.card)⁻¹
    let massLower := highCoefficientZonotopeScale D * ((1 - 2 *
      (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 -
        ((selector.chosen A hA).identifiedCore.card : ℝ) * 0)
    have hinputFull : input ⊆ Reduction.identifiedTranslate D.A₁ D.a := by
      dsimp only [input, Reduction.identifiedTranslate, PZ.translate]
      exact Finset.image_mono _ (D.largeA₁_subset 0)
    apply box_subset_centeredZonotope_of_boxWeighted_slabCard B hBside
      input core (canonicalRoundingCore_subset_input E.side₁.witness)
      (D.scaledForwardCoefficient (highCoefficientZonotopeScale D))
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
        (D.coefficient_mass_lower_largeA₁ (show (0 : ℝ) ≤ 0 by rfl)) hscale
    · exact card_sdiff_canonicalRoundingCore_le E.side₁.witness
    · exact H.slab_hierarchy.t_pos
    · intro f hf
      simpa only [not_le, B] using
        sourceUniformBoxWeightedFunctionalSlabCardinality selector hA
          rankCeiling hrank hd hirr hclosed hgamma (D.largeA₁ 0)
          ((D.largeA₁_subset 0).trans
            (D.A₁_subset_erase.trans (Finset.erase_subset _ _)))
          D.a
          ((selector.chosen A hA).identifiedCore_subset_coefficientBox
            D.a_mem)
          E.side₁.witness f t gamma slab rfl hf H.slab_hierarchy.t_pos
          H.slab_hierarchy.density H.slab_hierarchy.box_scale
          H.slab_hierarchy.low_rank H.slab_hierarchy.full_rank
    · simpa only [input, core, cap, massLower, Nat.cast_add,
        add_assoc] using H.forward_mass_radius
  · let Wrev := reverseEnhancedCFPWitnessOfIdentifiedTranslate
      D.a (D.largeA₂ 0) E.side₂.witness
    let input := orientedTranslate .reverse D.a (D.largeA₂ 0)
    let core := canonicalRoundingCore Wrev
    let cap := highCoefficientZonotopeScale D *
      (mu * (selector.chosen A hA).identifiedCore.card)⁻¹
    let massLower := highCoefficientZonotopeScale D * ((1 - 2 *
      (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 -
        ((selector.chosen A hA).identifiedCore.card : ℝ) * 0)
    have hinputFull : input ⊆ orientedTranslate .reverse D.a D.A₂ := by
      dsimp only [input, orientedTranslate]
      exact Finset.image_mono _ (D.largeA₂_subset 0)
    rw [E.reverseRoundingCore_eq_side]
    apply box_subset_centeredZonotope_of_boxWeighted_slabCard B hBside
      input core (canonicalRoundingCore_subset_input Wrev)
      (D.scaledReverseCoefficient (highCoefficientZonotopeScale D))
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
        (D.coefficient_mass_lower_largeA₂ (show (0 : ℝ) ≤ 0 by rfl)) hscale
    · exact card_sdiff_canonicalRoundingCore_le Wrev
    · exact H.slab_hierarchy.t_pos
    · intro f hf
      have hforward :=
        sourceUniformBoxWeightedFunctionalSlabCardinality selector hA
          rankCeiling hrank hd hirr hclosed hgamma (D.largeA₂ 0)
          ((D.largeA₂_subset 0).trans
            (D.A₂_subset_erase.trans (Finset.erase_subset _ _)))
          D.a
          ((selector.chosen A hA).identifiedCore_subset_coefficientBox
            D.a_mem)
          E.side₂.witness f t gamma slab rfl hf H.slab_hierarchy.t_pos
          H.slab_hierarchy.density H.slab_hierarchy.box_scale
          H.slab_hierarchy.low_rank H.slab_hierarchy.full_rank
      simpa only [not_le, core, Wrev, B] using
        reverseCanonicalRoundingCore_slab_card_le_of_forward
          D.a E.side₂.witness f (t * boxCoefficientMass B f) hforward
    · simpa only [input, core, cap, massLower, Nat.cast_add,
        add_assoc] using H.reverse_mass_radius

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
