/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.WeightedSourceThickness
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientSelectedSourceThickness

/-!
# Weighted thickness on the selected high-coefficient pools

The pointwise-minimum proof loses a factor `delta`: it only uses that every
surviving coefficient is at least `theta`.  The source argument has more
room.  Before CFP, each high pool retains the full alternating-side mass
minus at most `|core| * theta`.  This file feeds that total mass into the
weighted functional-slab criterion while keeping the same high-pool CFP
witnesses used by the post-CFP assembly.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Discarding all weights below `theta` loses at most `N * theta` total
mass, provided the original pool has at most `N` elements. -/
theorem massLower_sub_card_mul_le_sum_largeCoefficientPool
    {alpha : Type*} [DecidableEq alpha]
    (S : Finset alpha) (q : alpha → ℝ) (N : ℕ)
    (theta massLower : ℝ)
    (hcard : S.card ≤ N) (htheta : 0 ≤ theta)
    (hmass : massLower ≤ ∑ x ∈ S, q x) :
    massLower - (N : ℝ) * theta ≤
      ∑ x ∈ largeCoefficientPool S q theta, q x := by
  let H := largeCoefficientPool S q theta
  let L := S \ H
  have hHsub : H ⊆ S := largeCoefficientPool_subset S q theta
  have hsplit : H ∪ L = S := Finset.union_sdiff_of_subset hHsub
  have hdisj : Disjoint H L := Finset.disjoint_sdiff
  have hlow : ∀ x ∈ L, q x ≤ theta := by
    intro x hx
    have hxS := (Finset.mem_sdiff.mp hx).1
    have hxH := (Finset.mem_sdiff.mp hx).2
    have hnot : ¬(theta ≤ q x) := by
      intro hxq
      exact hxH (Finset.mem_filter.mpr ⟨hxS, hxq⟩)
    exact (lt_of_not_ge hnot).le
  have hsumLow : (∑ x ∈ L, q x) ≤ (N : ℝ) * theta := by
    calc
      (∑ x ∈ L, q x) ≤ ∑ _x ∈ L, theta :=
        Finset.sum_le_sum fun x hx ↦ hlow x hx
      _ = (L.card : ℝ) * theta := by simp
      _ ≤ (N : ℝ) * theta := by
        apply mul_le_mul_of_nonneg_right _ htheta
        exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans hcard
  have htotal : (∑ x ∈ S, q x) =
      (∑ x ∈ H, q x) + ∑ x ∈ L, q x := by
    rw [← Finset.sum_union hdisj, hsplit]
  dsimp only [H] at htotal ⊢
  linarith

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- Exact forward scaled-mass identity on the high-coefficient translated
pool. -/
theorem sum_scaledForwardCoefficient_identifiedTranslate_largeA₁
    (D : ConvexPoolsData A a₀ c mu) (theta scale : ℝ) :
    (∑ y ∈ Reduction.identifiedTranslate (D.largeA₁ theta) D.a,
        D.scaledForwardCoefficient scale y) =
      scale * ∑ x ∈ D.largeA₁ theta, pullCoefficient A c x := by
  rw [← orientedTranslate_forward_eq_identifiedTranslate]
  change (∑ y ∈ (D.largeA₁ theta).image
      (orientedDeviation .forward D.a),
      scale * D.forwardCoefficient y) = _
  rw [Finset.sum_image (orientedDeviation_injective .forward D.a).injOn]
  simp_rw [orientedDeviation, D.forwardCoefficient_deviation]
  rw [Finset.mul_sum]

/-- Exact reverse scaled-mass identity before negating the selected
witness. -/
theorem sum_scaledReverseCoefficient_orientedTranslate_largeA₂
    (D : ConvexPoolsData A a₀ c mu) (theta scale : ℝ) :
    (∑ y ∈ orientedTranslate .reverse D.a (D.largeA₂ theta),
        D.scaledReverseCoefficient scale y) =
      scale * ∑ x ∈ D.largeA₂ theta, pullCoefficient A c x := by
  change (∑ y ∈ (D.largeA₂ theta).image
      (orientedDeviation .reverse D.a),
      scale * D.reverseCoefficient y) = _
  rw [Finset.sum_image (orientedDeviation_injective .reverse D.a).injOn]
  simp_rw [orientedDeviation, D.reverseCoefficient_deviation]
  rw [Finset.mul_sum]

theorem coefficient_mass_lower_largeA₁
    (D : ConvexPoolsData A a₀ c mu) {theta : ℝ} (htheta : 0 ≤ theta) :
    (1 - 2 * (mu * A.card)⁻¹) / 2 - (A.card : ℝ) * theta ≤
      ∑ x ∈ D.largeA₁ theta, pullCoefficient A c x := by
  exact massLower_sub_card_mul_le_sum_largeCoefficientPool D.A₁
    (pullCoefficient A c) A.card theta
      ((1 - 2 * (mu * A.card)⁻¹) / 2)
    (Finset.card_le_card
      (D.A₁_subset_erase.trans (Finset.erase_subset _ _)))
    htheta D.coefficient_mass_lower_uniform_A₁

theorem coefficient_mass_lower_largeA₂
    (D : ConvexPoolsData A a₀ c mu) {theta : ℝ} (htheta : 0 ≤ theta) :
    (1 - 2 * (mu * A.card)⁻¹) / 2 - (A.card : ℝ) * theta ≤
      ∑ x ∈ D.largeA₂ theta, pullCoefficient A c x := by
  exact massLower_sub_card_mul_le_sum_largeCoefficientPool D.A₂
    (pullCoefficient A c) A.card theta
      ((1 - 2 * (mu * A.card)⁻¹) / 2)
    (Finset.card_le_card
      (D.A₂_subset_erase.trans (Finset.erase_subset _ _)))
    htheta D.coefficient_mass_lower_uniform_A₂

/-- Weighted source thickness on the packaged forward high-coefficient
selection. -/
theorem exists_sourceWeightedSelectedForwardThicknessConstants
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
        {y : Fin (selector.chosen A hA).dimension → ℝ |
          ∀ i, |y i| ≤ radius} ⊆
          centeredZonotope E.forwardRoundingCore
            (D.scaledForwardCoefficient scale) := by
  obtain ⟨factorBound, constant, hconstant, hslabCard⟩ :=
    exists_sourceFunctionalSlabCardinalityConstants selector hA hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro delta gamma mu theta scale radius t a₀ c D E slab hirr hclosed
    hgamma hmu htheta hscale ht hdenseSlab hboxScale hlow hfull hradius
  let input := Reduction.identifiedTranslate (D.largeA₁ theta) D.a
  let core := canonicalRoundingCore E.side₁.witness
  let cap := scale *
    (mu * (selector.chosen A hA).identifiedCore.card)⁻¹
  let massLower := scale * ((1 - 2 *
    (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 -
      ((selector.chosen A hA).identifiedCore.card : ℝ) * theta)
  have hinputFull : input ⊆ Reduction.identifiedTranslate D.A₁ D.a := by
    dsimp only [input, Reduction.identifiedTranslate, PZ.translate]
    exact Finset.image_mono _ (D.largeA₁_subset theta)
  apply cube_subset_centeredZonotope_of_weighted_slabCard input core
    (canonicalRoundingCore_subset_input E.side₁.witness)
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
    simpa only [not_le] using
      hslabCard hirr hclosed hgamma (D.largeA₁ theta)
        ((D.largeA₁_subset theta).trans
          (D.A₁_subset_erase.trans (Finset.erase_subset _ _)))
        D.a
        ((selector.chosen A hA).identifiedCore_subset_coefficientBox D.a_mem)
        E.side₁.witness f t gamma slab rfl hf ht hdenseSlab hboxScale
          hlow hfull
  · simpa only [input, core, cap, massLower, Nat.cast_add,
      add_assoc] using hradius

/-- Weighted source thickness on the packaged reverse high-coefficient
selection. -/
theorem exists_sourceWeightedSelectedReverseThicknessConstants
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
            (((E.side₂.loss + E.side₂.reserveBound + slab : ℕ) : ℝ) *
              (scale *
                (mu * (selector.chosen A hA).identifiedCore.card)⁻¹))) →
        {y : Fin (selector.chosen A hA).dimension → ℝ |
          ∀ i, |y i| ≤ radius} ⊆
          centeredZonotope E.reverseRoundingCore
            (D.scaledReverseCoefficient scale) := by
  obtain ⟨factorBound, constant, hconstant, hslabCard⟩ :=
    exists_sourceFunctionalSlabCardinalityConstants selector hA hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro delta gamma mu theta scale radius t a₀ c D E slab hirr hclosed
    hgamma hmu htheta hscale ht hdenseSlab hboxScale hlow hfull hradius
  let Wrev := reverseEnhancedCFPWitnessOfIdentifiedTranslate
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
  apply cube_subset_centeredZonotope_of_weighted_slabCard input core
    (canonicalRoundingCore_subset_input Wrev)
    (D.scaledReverseCoefficient scale)
    (cap := cap) (massLower := massLower) (radius := radius) (t := t)
    (missing := E.side₂.loss + E.side₂.reserveBound) (slab := slab)
  · intro x hx
    exact (D.scaledReverseCoefficient_bounds_on_orientedTranslate
      hscale x (hinputFull (canonicalRoundingCore_subset_input Wrev hx))).1
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
      ((selector.chosen A hA).identifiedCore_subset_coefficientBox D.a_mem)
      E.side₂.witness f t gamma slab rfl hf ht hdenseSlab hboxScale
        hlow hfull
    simpa only [not_le, core, Wrev] using
      reverseCanonicalRoundingCore_slab_card_le_of_forward
        D.a E.side₂.witness f (t * coefficientMass f) hforward
  · simpa only [input, core, cap, massLower, Nat.cast_add,
      add_assoc] using hradius

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
