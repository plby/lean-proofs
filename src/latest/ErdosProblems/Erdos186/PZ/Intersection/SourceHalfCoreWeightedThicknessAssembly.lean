/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceHalfCorePostCFP
import ErdosProblems.Erdos186.PZ.Intersection.SourceSpecializedThicknessAssembly
import ErdosProblems.Erdos186.PZ.Intersection.WeightedHighCoefficientSourceThickness

/-!
# Half-core assembly with weighted high-pool thickness

This is the source-scale version of the terminal post-CFP constructor.  The
functional-slab argument uses the total coefficient mass retained in each
high pool, rather than the minimum coefficient times its cardinality.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Exact scalar residual for the weighted forward and reverse high-pool
thickness theorems. -/
structure HighCoefficientWeightedSourceThicknessScalarHierarchies
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
    (3 * E.commonCoveringRadius + 2 : ℕ) + E.forwardCenterError ≤ t *
      (highCoefficientZonotopeScale D *
          ((1 - 2 *
            (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 -
              ((selector.chosen A hA).identifiedCore.card : ℝ) * theta) -
        (((E.side₁.loss + E.side₁.reserveBound + slab : ℕ) : ℝ) *
          (highCoefficientZonotopeScale D *
            (mu * (selector.chosen A hA).identifiedCore.card)⁻¹)))
  reverse_radius :
    (3 * E.commonCoveringRadius + 2 : ℕ) + E.reverseCenterError ≤ t *
      (highCoefficientZonotopeScale D *
          ((1 - 2 *
            (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2 -
              ((selector.chosen A hA).identifiedCore.card : ℝ) * theta) -
        (((E.side₂.loss + E.side₂.reserveBound + slab : ℕ) : ℝ) *
          (highCoefficientZonotopeScale D *
            (mu * (selector.chosen A hA).identifiedCore.card)⁻¹)))

namespace Theorem4PostCFPData

/-- Terminal half-core post-CFP assembly through weighted high-pool
functional-slab thickness. -/
theorem exists_sourceWeightedThicknessConstants_ofHighCoefficientSource_halfCore
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
    (hhalf : (1 / 2 : ℝ) * (A.card : ℝ) ≤
      ((selector.chosen A hA).identifiedCore.card : ℝ))
    (hpopulation : 32 / mu ≤ (A.card : ℝ))
    (hdeltaMu : delta < mu / 8)
    (hdelta : 0 < delta) (hmu : 0 < mu) (hgamma : 0 < gamma) :
    let theta := sourceCoefficientThreshold A.card
    let hcap : 0 < (mu *
        (selector.chosen A hA).identifiedCore.card)⁻¹ :=
      inv_mu_mul_coreCard_pos_of_coreRetention
        (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention
    let hmass := highCoefficient_massBudget_of_halfCore
      (selector.eligible_nonempty hA).card_pos hmu hdeltaMu hhalf hpopulation
    let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
      hdelta (sourceCoefficientThreshold_pos
        (selector.eligible_nonempty hA).card_pos).le hcap hmass
    ∃ forwardFactor reverseFactor : ℕ,
      ∃ forwardConstant reverseConstant : ℝ,
        1 ≤ forwardConstant ∧ 1 ≤ reverseConstant ∧
        ∀ (slab : ℕ) (t : ℝ),
          HighCoefficientBoundedSupportScalarHierarchies E →
          HighCoefficientWeightedSourceThicknessScalarHierarchies
            (delta := delta) E forwardConstant reverseConstant slab t →
          ∃ Dout : Theorem4PostCFPData
              (selector.chosen A hA).identifiedCore, Dout.a = D.a := by
  dsimp only
  let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
    hdelta (sourceCoefficientThreshold_pos
      (selector.eligible_nonempty hA).card_pos).le
    (inv_mu_mul_coreCard_pos_of_coreRetention
      (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention)
    (highCoefficient_massBudget_of_halfCore
      (selector.eligible_nonempty hA).card_pos hmu hdeltaMu hhalf hpopulation)
  have hd : 0 < (selector.chosen A hA).dimension :=
    selectedDimension_pos_of_coreRetention selector hdelta hcoreRetention
  obtain ⟨forwardFactor, forwardConstant, hforwardConstant, hforward⟩ :=
    ConvexPoolsData.exists_sourceWeightedSelectedForwardThicknessConstants
      selector hA hd
  obtain ⟨reverseFactor, reverseConstant, hreverseConstant, hreverse⟩ :=
    ConvexPoolsData.exists_sourceWeightedSelectedReverseThicknessConstants
      selector hA hd
  refine ⟨forwardFactor, reverseFactor, forwardConstant, reverseConstant,
    hforwardConstant, hreverseConstant, ?_⟩
  intro slab t Hscalar Hthickness
  have hscale : 0 ≤ highCoefficientZonotopeScale D :=
    D.highCoefficientZonotopeScale_nonneg hmu
  have htheta : 0 ≤ sourceCoefficientThreshold A.card :=
    (sourceCoefficientThreshold_pos
      (selector.eligible_nonempty hA).card_pos).le
  have hthick₁ := hforward D E slab hirr hclosed hgamma hmu htheta hscale
    Hthickness.forward_slab.t_pos Hthickness.forward_slab.density
    Hthickness.forward_slab.box_scale Hthickness.forward_slab.low_rank
    Hthickness.forward_slab.full_rank Hthickness.forward_radius
  have hthick₂ := hreverse D E slab hirr hclosed hgamma hmu htheta hscale
    Hthickness.reverse_slab.t_pos Hthickness.reverse_slab.density
    Hthickness.reverse_slab.box_scale Hthickness.reverse_slab.low_rank
    Hthickness.reverse_slab.full_rank Hthickness.reverse_radius
  let assembled := ofHighCoefficientSource_halfCore selector D hirr hclosed
    hcoreRetention hhalf hpopulation hdeltaMu hdelta hmu hgamma Hscalar
      (fun _y hy ↦ hthick₁ hy) (fun _y hy ↦ hthick₂ hy)
  exact ⟨assembled.1, assembled.2⟩

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
