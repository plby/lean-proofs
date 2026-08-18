/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientSelectedSourceThickness
import ErdosProblems.Erdos186.PZ.Intersection.SourceSpecializedPostCFP

/-!
# Source-specialized assembly through the functional-slab theorem

This file replaces the two previously abstract centered-zonotope thickness premises in
`SourceSpecializedPostCFP.lean` by the exact scalar inequalities consumed by
the source functional-slab theorem.  No field is added to the public
`Theorem4PostCFPStatement`; this is an intermediate finite constructor for
the source parameter calculation.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- The four scalar hypotheses needed to turn irreducibility into a bound on
one functional slab.  They are separated from the final surviving-cardinality
inequality because the same slab size and thickness parameter are used on
both high-coefficient sides. -/
structure SourceFunctionalSlabScalarHierarchy
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} (A : Finset (LatticePoint ambient))
    (hA : selector.Eligible A) (delta gamma constant : ℝ)
    (slab : ℕ) (t : ℝ) : Prop where
  t_pos : 0 < t
  density : delta * (A.card : ℝ) ≤ (slab : ℝ)
  box_scale :
    1 ≤ (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
      ((controlIntegerBox (selector.chosen A hA).progression
        (2 * context.scaleDen
          (selector.chosen A hA).dimension)).carrier.card : ℝ)
  low_rank :
    ∀ (Z : Finset
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
        ((selector.chosen Z hZ).dilation : ℝ) * gamma
  full_rank :
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
        gamma

/-- Exact scalar residual after the forward and reverse functional-slab
cardinality theorems have been installed. -/
structure HighCoefficientSourceThicknessScalarHierarchies
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu theta gamma delta : ℝ}
    {D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu}
    (E : HighCoefficientSideSelectionData selector hA D theta gamma)
    (forwardConstant reverseConstant : ℝ) (slab : ℕ) (t : ℝ) : Prop where
  forward_slab : SourceFunctionalSlabScalarHierarchy selector A hA
    delta gamma forwardConstant slab t
  reverse_slab : SourceFunctionalSlabScalarHierarchy selector A hA
    delta gamma reverseConstant slab t
  forward_radius :
    (3 * E.commonCoveringRadius + 2 : ℕ) + E.forwardCenterError ≤
      t * (highCoefficientZonotopeScale D * theta *
        (((Reduction.identifiedTranslate (D.largeA₁ theta) D.a).card -
          (E.side₁.loss + E.side₁.reserveBound + slab) : ℕ) : ℝ))
  reverse_radius :
    (3 * E.commonCoveringRadius + 2 : ℕ) + E.reverseCenterError ≤
      t * (highCoefficientZonotopeScale D * theta *
        (((Reduction.identifiedTranslate (D.largeA₂ theta) D.a).card -
          (E.side₂.loss + E.side₂.reserveBound + slab) : ℕ) : ℝ))

namespace Theorem4PostCFPData

/-- The complete source-specialized finite constructor, with both geometric
thickness inclusions discharged by the forward and reverse functional-slab
theorems.  Its only residual hypotheses are explicit scalar inequalities. -/
theorem exists_sourceThicknessConstants_ofHighCoefficientSource_specialized
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
    ∃ forwardFactor reverseFactor : ℕ,
      ∃ forwardConstant reverseConstant : ℝ,
        1 ≤ forwardConstant ∧ 1 ≤ reverseConstant ∧
        ∀ (slab : ℕ) (t : ℝ),
          HighCoefficientBoundedSupportScalarHierarchies E →
          HighCoefficientSourceThicknessScalarHierarchies (delta := delta) E
            forwardConstant reverseConstant slab t →
          ∃ Dout : Theorem4PostCFPData
              (selector.chosen A hA).identifiedCore, Dout.a = D.a := by
  dsimp only
  let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
    hdelta (sourceCoefficientThreshold_pos
      (selector.eligible_nonempty hA).card_pos).le
    (inv_mu_mul_coreCard_pos_of_coreRetention
      (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention)
    (Hsource.highCoefficient_massBudget hmu)
  have hd : 0 < (selector.chosen A hA).dimension :=
    selectedDimension_pos_of_coreRetention selector hdelta hcoreRetention
  obtain ⟨forwardFactor, forwardConstant, hforwardConstant, hforward⟩ :=
    ConvexPoolsData.exists_sourceSelectedForwardZonotopeThicknessConstants
      selector hA hd
  obtain ⟨reverseFactor, reverseConstant, hreverseConstant, hreverse⟩ :=
    ConvexPoolsData.exists_sourceSelectedReverseZonotopeThicknessConstants
      selector hA hd
  refine ⟨forwardFactor, reverseFactor, forwardConstant, reverseConstant,
    hforwardConstant, hreverseConstant, ?_⟩
  intro slab t Hscalar Hthickness
  have hscale : 0 ≤ highCoefficientZonotopeScale D :=
    D.highCoefficientZonotopeScale_nonneg hmu
  have htheta : 0 ≤ sourceCoefficientThreshold A.card :=
    (sourceCoefficientThreshold_pos
      (selector.eligible_nonempty hA).card_pos).le
  have hthick₁ := hforward D E slab hirr hclosed hgamma htheta hscale
    Hthickness.forward_slab.t_pos Hthickness.forward_slab.density
    Hthickness.forward_slab.box_scale Hthickness.forward_slab.low_rank
    Hthickness.forward_slab.full_rank Hthickness.forward_radius
  have hthick₂ := hreverse D E slab hirr hclosed hgamma htheta hscale
    Hthickness.reverse_slab.t_pos Hthickness.reverse_slab.density
    Hthickness.reverse_slab.box_scale Hthickness.reverse_slab.low_rank
    Hthickness.reverse_slab.full_rank Hthickness.reverse_radius
  let assembled := ofHighCoefficientSource_specialized selector D hirr hclosed
    hcoreRetention hdelta hmu hgamma Hsource Hscalar
      (fun _y hy ↦ hthick₁ hy) (fun _y hy ↦ hthick₂ hy)
  exact ⟨assembled.1, assembled.2⟩

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
