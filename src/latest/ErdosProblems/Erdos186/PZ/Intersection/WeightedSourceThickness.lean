/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.WeightedSlabThickness
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientReverseCoefficient
import ErdosProblems.Erdos186.PZ.Intersection.SourceReverseSlabCardinality

/-!
# Weighted source thickness on the two balanced sides

The CFP selector is now applied to the complete balanced pools `A₁` and
`A₂`.  No coefficient cutoff or high-coefficient mass budget is used.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

theorem scaledForwardCoefficient_bounds_on_identifiedTranslate
    (D : ConvexPoolsData A a₀ c mu) {scale : ℝ} (hscale : 0 ≤ scale) :
    ∀ y ∈ Reduction.identifiedTranslate D.A₁ D.a,
      0 ≤ D.scaledForwardCoefficient scale y ∧
        D.scaledForwardCoefficient scale y ≤
          scale * (mu * A.card)⁻¹ := by
  intro y hy
  have hy' : y ∈ orientedTranslate .forward D.a D.A₁ := by
    rwa [orientedTranslate_forward_eq_identifiedTranslate]
  have hb := D.forwardCoefficient_bounds hy'
  exact ⟨mul_nonneg hscale hb.1,
    mul_le_mul_of_nonneg_left hb.2 hscale⟩

theorem sum_scaledForwardCoefficient_identifiedTranslate
    (D : ConvexPoolsData A a₀ c mu) (scale : ℝ) :
    (∑ y ∈ Reduction.identifiedTranslate D.A₁ D.a,
        D.scaledForwardCoefficient scale y) =
      scale * ∑ x ∈ D.A₁, pullCoefficient A c x := by
  rw [← orientedTranslate_forward_eq_identifiedTranslate]
  change (∑ y ∈ D.A₁.image (orientedDeviation .forward D.a),
      scale * D.forwardCoefficient y) = _
  rw [Finset.sum_image (orientedDeviation_injective .forward D.a).injOn]
  simp_rw [orientedDeviation, D.forwardCoefficient_deviation]
  rw [Finset.mul_sum]

theorem scaledReverseCoefficient_bounds_on_orientedTranslate
    (D : ConvexPoolsData A a₀ c mu) {scale : ℝ} (hscale : 0 ≤ scale) :
    ∀ y ∈ orientedTranslate .reverse D.a D.A₂,
      0 ≤ D.scaledReverseCoefficient scale y ∧
        D.scaledReverseCoefficient scale y ≤
          scale * (mu * A.card)⁻¹ := by
  intro y hy
  have hb := D.reverseCoefficient_bounds hy
  exact ⟨mul_nonneg hscale hb.1,
    mul_le_mul_of_nonneg_left hb.2 hscale⟩

theorem sum_scaledReverseCoefficient_orientedTranslate
    (D : ConvexPoolsData A a₀ c mu) (scale : ℝ) :
    (∑ y ∈ orientedTranslate .reverse D.a D.A₂,
        D.scaledReverseCoefficient scale y) =
      scale * ∑ x ∈ D.A₂, pullCoefficient A c x := by
  change (∑ y ∈ D.A₂.image (orientedDeviation .reverse D.a),
      scale * D.reverseCoefficient y) = _
  rw [Finset.sum_image (orientedDeviation_injective .reverse D.a).injOn]
  simp_rw [orientedDeviation, D.reverseCoefficient_deviation]
  rw [Finset.mul_sum]

/-- Source slab cardinality gives weighted thickness on the complete forward
balanced pool.  The final scalar term is the retained coefficient mass after
paying the CFP complement and one `delta`-dense slab at the coefficient cap. -/
theorem exists_sourceWeightedForwardThicknessConstants
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (hA : selector.Eligible A)
    (hd : 0 < (selector.chosen A hA).dimension) :
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ {delta gamma mu scale radius t : ℝ}
        {a₀ : realImage (selector.chosen A hA).identifiedCore}
        {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
        (D : ConvexPoolsData
          (selector.chosen A hA).identifiedCore a₀ c mu)
        {s Dmax k loss slab : ℕ}
        (W : CFP.EnhancedCFPWitness
          (Reduction.identifiedTranslate D.A₁ D.a) s Dmax k loss),
        Reduction.IsBoundedCoordinateIrreducible selector A hA
            delta gamma →
        selector.CandidateClosedAt A hA delta →
        0 < gamma → 0 < mu → 0 ≤ scale → 0 < t →
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
              (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2) -
            (((loss + s + slab : ℕ) : ℝ) *
              (scale *
                (mu * (selector.chosen A hA).identifiedCore.card)⁻¹))) →
        {y : Fin (selector.chosen A hA).dimension → ℝ |
          ∀ i, |y i| ≤ radius} ⊆
          centeredZonotope (canonicalRoundingCore W)
            (D.scaledForwardCoefficient scale) := by
  obtain ⟨factorBound, constant, hconstant, hslabCard⟩ :=
    exists_sourceFunctionalSlabCardinalityConstants selector hA hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro delta gamma mu scale radius t a₀ c D s Dmax k loss slab W hirr
    hclosed hgamma hmu hscale ht hdenseSlab hboxScale hlow hfull hradius
  let input := Reduction.identifiedTranslate D.A₁ D.a
  let core := canonicalRoundingCore W
  let cap := scale *
    (mu * (selector.chosen A hA).identifiedCore.card)⁻¹
  let massLower := scale * ((1 - 2 *
    (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2)
  apply cube_subset_centeredZonotope_of_weighted_slabCard input core
    (canonicalRoundingCore_subset_input W)
    (D.scaledForwardCoefficient scale)
    (cap := cap) (massLower := massLower) (radius := radius) (t := t)
    (missing := loss + s) (slab := slab)
  · intro x hx
    exact (D.scaledForwardCoefficient_bounds_on_identifiedTranslate
      hscale x (canonicalRoundingCore_subset_input W hx)).1
  · exact mul_nonneg hscale (inv_nonneg.mpr (mul_nonneg hmu.le
      (by positivity)))
  · intro x hx
    exact (D.scaledForwardCoefficient_bounds_on_identifiedTranslate
      hscale x hx).2
  · dsimp only [massLower]
    rw [D.sum_scaledForwardCoefficient_identifiedTranslate]
    exact mul_le_mul_of_nonneg_left D.coefficient_mass_lower_uniform_A₁ hscale
  · exact card_sdiff_canonicalRoundingCore_le W
  · exact ht
  · intro f hf
    simpa only [not_le] using
      hslabCard hirr hclosed hgamma D.A₁
        (D.A₁_subset_erase.trans (Finset.erase_subset _ _)) D.a
        ((selector.chosen A hA).identifiedCore_subset_coefficientBox D.a_mem)
        W f t gamma slab rfl hf ht hdenseSlab hboxScale hlow hfull
  · simpa only [input, core, cap, massLower, Nat.cast_add,
      add_assoc] using hradius

/-- Reverse counterpart of `exists_sourceWeightedForwardThicknessConstants`.
The selected witness is negated only after applying the source slab theorem. -/
theorem exists_sourceWeightedReverseThicknessConstants
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (hA : selector.Eligible A)
    (hd : 0 < (selector.chosen A hA).dimension) :
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ {delta gamma mu scale radius t : ℝ}
        {a₀ : realImage (selector.chosen A hA).identifiedCore}
        {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
        (D : ConvexPoolsData
          (selector.chosen A hA).identifiedCore a₀ c mu)
        {s Dmax k loss slab : ℕ}
        (W : CFP.EnhancedCFPWitness
          (Reduction.identifiedTranslate D.A₂ D.a) s Dmax k loss),
        Reduction.IsBoundedCoordinateIrreducible selector A hA
            delta gamma →
        selector.CandidateClosedAt A hA delta →
        0 < gamma → 0 < mu → 0 ≤ scale → 0 < t →
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
              (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2) -
            (((loss + s + slab : ℕ) : ℝ) *
              (scale *
                (mu * (selector.chosen A hA).identifiedCore.card)⁻¹))) →
        {y : Fin (selector.chosen A hA).dimension → ℝ |
          ∀ i, |y i| ≤ radius} ⊆
          centeredZonotope
            (canonicalRoundingCore
              (reverseEnhancedCFPWitnessOfIdentifiedTranslate
                D.a D.A₂ W))
            (D.scaledReverseCoefficient scale) := by
  obtain ⟨factorBound, constant, hconstant, hslabCard⟩ :=
    exists_sourceFunctionalSlabCardinalityConstants selector hA hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro delta gamma mu scale radius t a₀ c D s Dmax k loss slab W hirr
    hclosed hgamma hmu hscale ht hdenseSlab hboxScale hlow hfull hradius
  let Wrev := reverseEnhancedCFPWitnessOfIdentifiedTranslate D.a D.A₂ W
  let input := orientedTranslate .reverse D.a D.A₂
  let core := canonicalRoundingCore Wrev
  let cap := scale *
    (mu * (selector.chosen A hA).identifiedCore.card)⁻¹
  let massLower := scale * ((1 - 2 *
    (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2)
  apply cube_subset_centeredZonotope_of_weighted_slabCard input core
    (canonicalRoundingCore_subset_input Wrev)
    (D.scaledReverseCoefficient scale)
    (cap := cap) (massLower := massLower) (radius := radius) (t := t)
    (missing := loss + s) (slab := slab)
  · intro x hx
    exact (D.scaledReverseCoefficient_bounds_on_orientedTranslate
      hscale x (canonicalRoundingCore_subset_input Wrev hx)).1
  · exact mul_nonneg hscale (inv_nonneg.mpr (mul_nonneg hmu.le
      (by positivity)))
  · intro x hx
    exact (D.scaledReverseCoefficient_bounds_on_orientedTranslate
      hscale x hx).2
  · dsimp only [massLower]
    rw [D.sum_scaledReverseCoefficient_orientedTranslate]
    exact mul_le_mul_of_nonneg_left D.coefficient_mass_lower_uniform_A₂ hscale
  · exact card_sdiff_canonicalRoundingCore_le Wrev
  · exact ht
  · intro f hf
    have hforward := hslabCard hirr hclosed hgamma D.A₂
      (D.A₂_subset_erase.trans (Finset.erase_subset _ _)) D.a
      ((selector.chosen A hA).identifiedCore_subset_coefficientBox D.a_mem)
      W f t gamma slab rfl hf ht hdenseSlab hboxScale hlow hfull
    simpa only [not_le, core, Wrev] using
      reverseCanonicalRoundingCore_slab_card_le_of_forward
        D.a W f (t * coefficientMass f) hforward
  · simpa only [input, core, cap, massLower, Nat.cast_add,
      add_assoc] using hradius

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
