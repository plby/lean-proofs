/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientReverseSourceThickness
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientPostCFPAssembly

/-!
# Source thickness specialized to packaged side selections

These adapters identify the witnesses used by the source slab theorem with
the transported forward and reverse witnesses stored in a
`HighCoefficientSideSelectionData` package.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Canonical cores are unchanged when their witness input type is rewritten
along an equality of finite sets. -/
@[simp] theorem canonicalRoundingCore_transportEnhancedCFPWitness
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (h : X = Y) (W : CFP.EnhancedCFPWitness X s D k loss) :
    canonicalRoundingCore (transportEnhancedCFPWitness h W) =
      canonicalRoundingCore W := by
  subst Y
  rfl

/-- `Eq.mpr`-form of the same input-transport invariance. -/
@[simp] theorem canonicalRoundingCore_eq_mpr
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (h : X = Y) (W : CFP.EnhancedCFPWitness Y s D k loss) :
    canonicalRoundingCore
        (Eq.mpr
          (congrArg (fun Z ↦ CFP.EnhancedCFPWitness Z s D k loss) h) W) =
      canonicalRoundingCore W := by
  subst Y
  rfl

namespace HighCoefficientSideSelectionData

variable {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu theta gamma : ℝ}
    {D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu}

@[simp] theorem forwardRoundingCore_eq_side
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    E.forwardRoundingCore = canonicalRoundingCore E.side₁.witness := by
  simp only [forwardRoundingCore, forwardWitness,
    canonicalRoundingCore_transportEnhancedCFPWitness]

@[simp] theorem reverseRoundingCore_eq_side
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    E.reverseRoundingCore = canonicalRoundingCore
      (reverseEnhancedCFPWitnessOfIdentifiedTranslate
        D.a (D.largeA₂ theta) E.side₂.witness) := by
  unfold reverseRoundingCore reverseWitness
  unfold reverseEnhancedCFPWitnessOfIdentifiedTranslate
  rw [canonicalRoundingCore_transportEnhancedCFPWitness,
    canonicalRoundingCore_eq_mpr]
  exact orientedTranslate_reverse_eq_image_neg_identifiedTranslate
    D.a (D.largeA₂ theta)

end HighCoefficientSideSelectionData

namespace ConvexPoolsData

/-- Forward source thickness, with the result expressed on the canonical
rounding core stored in the packaged selection. -/
theorem exists_sourceSelectedForwardZonotopeThicknessConstants
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
        0 < gamma → 0 ≤ theta → 0 ≤ scale → 0 < t →
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
        radius ≤ t * (scale * theta *
          (((Reduction.identifiedTranslate (D.largeA₁ theta) D.a).card -
            (E.side₁.loss + E.side₁.reserveBound + slab) : ℕ) : ℝ)) →
        {y : Fin (selector.chosen A hA).dimension → ℝ |
          ∀ i, |y i| ≤ radius} ⊆
          centeredZonotope E.forwardRoundingCore
            (D.scaledForwardCoefficient scale) := by
  obtain ⟨factorBound, constant, hconstant, H⟩ :=
    exists_sourceForwardZonotopeThicknessConstants selector hA hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro delta gamma mu theta scale radius t a₀ c D E slab hirr hclosed
    hgamma htheta hscale ht hdenseSlab hboxScale hlow hfull hradius
  have hthick := H D E.side₁.witness hirr hclosed hgamma htheta hscale ht
    hdenseSlab hboxScale hlow hfull hradius
  simpa only [E.forwardRoundingCore_eq_side] using hthick

/-- Reverse source thickness, with the result expressed on the canonical
reverse rounding core stored in the packaged selection. -/
theorem exists_sourceSelectedReverseZonotopeThicknessConstants
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
        0 < gamma → 0 ≤ theta → 0 ≤ scale → 0 < t →
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
        radius ≤ t * (scale * theta *
          (((Reduction.identifiedTranslate (D.largeA₂ theta) D.a).card -
            (E.side₂.loss + E.side₂.reserveBound + slab) : ℕ) : ℝ)) →
        {y : Fin (selector.chosen A hA).dimension → ℝ |
          ∀ i, |y i| ≤ radius} ⊆
          centeredZonotope E.reverseRoundingCore
            (D.scaledReverseCoefficient scale) := by
  obtain ⟨factorBound, constant, hconstant, H⟩ :=
    exists_sourceReverseZonotopeThicknessConstants selector hA hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro delta gamma mu theta scale radius t a₀ c D E slab hirr hclosed
    hgamma htheta hscale ht hdenseSlab hboxScale hlow hfull hradius
  have hthick := H D E.side₂.witness hirr hclosed hgamma htheta hscale ht
    hdenseSlab hboxScale hlow hfull hradius
  simpa only [E.reverseRoundingCore_eq_side] using hthick

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
