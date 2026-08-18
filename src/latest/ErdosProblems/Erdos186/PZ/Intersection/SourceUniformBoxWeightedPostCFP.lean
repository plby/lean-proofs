/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceUniformBoxWeightedThickness

/-! # Rank-uniform finite post-CFP assembly -/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

namespace Theorem4PostCFPData

/-- Complete finite zero-cutoff construction with the deterministic John
constant uniform below `rankCeiling`. -/
theorem of_sourceUniformBoxWeightedFullCoefficientSource_halfCore
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    (rankCeiling : ℕ)
    (hrank : (selector.chosen A hA).dimension ≤ rankCeiling)
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
    (hdelta : 0 < delta) (hmu : 0 < mu) (hgamma : 0 < gamma)
    (slab : ℕ) (t radius : ℝ) :
    let hcap : 0 < (mu *
        (selector.chosen A hA).identifiedCore.card)⁻¹ :=
      inv_mu_mul_coreCard_pos_of_coreRetention
        (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention
    let hmass := highCoefficient_zeroCutoff_massBudget_of_halfCore
      (selector.eligible_nonempty hA).card_pos hmu hdeltaMu hhalf hpopulation
    let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
      hdelta (show (0 : ℝ) ≤ 0 by rfl) hcap hmass
    HighCoefficientBoundedSupportScalarHierarchies E →
    BoxWeightedZeroCutoffScalarHierarchies (delta := delta) E
      (sourceBoxWeightedJohnUniformConstant rankCeiling) slab t radius →
    ∃ Dout : Theorem4PostCFPData
        (selector.chosen A hA).identifiedCore, Dout.a = D.a := by
  dsimp only
  let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
    hdelta (show (0 : ℝ) ≤ 0 by rfl)
    (inv_mu_mul_coreCard_pos_of_coreRetention
      (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention)
    (highCoefficient_zeroCutoff_massBudget_of_halfCore
      (selector.eligible_nonempty hA).card_pos hmu hdeltaMu hhalf hpopulation)
  intro Hbounded H
  have hd : 0 < (selector.chosen A hA).dimension :=
    selectedDimension_pos_of_coreRetention selector hdelta hcoreRetention
  obtain ⟨hforward, hreverse⟩ :=
    D.sourceUniformBoxWeightedSelectedThickness selector rankCeiling hrank hd
      E slab t radius hirr hclosed hgamma hmu H
  have htargetForward : ∀ y,
      (∀ i, |y i| ≤ (3 * E.commonCoveringRadius + 2 : ℕ) +
        E.forwardZeroCoordinateCenterError i) →
      y ∈ centeredZonotope E.forwardRoundingCore
        (D.scaledForwardCoefficient (highCoefficientZonotopeScale D)) := by
    intro y hy
    apply hforward
    intro i
    apply (hy i).trans
    let w : ℝ :=
      ((selector.chosen A hA).progression.widths i - 1 : ℕ)
    have hw : 2 ≤ w := by
      have hthree : 3 ≤
          (selector.chosen A hA).progression.widths i :=
        (selector.chosen A hA).witness.three_le_width i
      have htwo : 2 ≤
          (selector.chosen A hA).progression.widths i - 1 := by omega
      dsimp only [w]
      exact_mod_cast htwo
    have hw0 : 0 ≤ w := le_trans (by norm_num) hw
    have htarget := mul_le_mul_of_nonneg_right H.forward_target_radius hw0
    have htarget' :
        (((3 * E.commonCoveringRadius + 2 : ℕ) : ℝ) / 2 +
          (((E.side₁.loss + E.side₁.reserveBound : ℕ) : ℝ) / 2 +
            E.side₁.reserveBound)) * w ≤
          radius *
            (4 * context.scaleDen (selector.chosen A hA).dimension) * w := by
      simpa only [E] using htarget
    rw [integerBoxSideLength_sourceFunctionalControlBox]
    dsimp only [HighCoefficientSideSelectionData.forwardZeroCoordinateCenterError,
      w]
    push_cast at htarget' ⊢
    nlinarith
  have htargetReverse : ∀ y,
      (∀ i, |y i| ≤ (3 * E.commonCoveringRadius + 2 : ℕ) +
        E.reverseZeroCoordinateCenterError i) →
      y ∈ centeredZonotope E.reverseRoundingCore
        (D.scaledReverseCoefficient (highCoefficientZonotopeScale D)) := by
    intro y hy
    apply hreverse
    intro i
    apply (hy i).trans
    let w : ℝ :=
      ((selector.chosen A hA).progression.widths i - 1 : ℕ)
    have hw : 2 ≤ w := by
      have hthree : 3 ≤
          (selector.chosen A hA).progression.widths i :=
        (selector.chosen A hA).witness.three_le_width i
      have htwo : 2 ≤
          (selector.chosen A hA).progression.widths i - 1 := by omega
      dsimp only [w]
      exact_mod_cast htwo
    have hw0 : 0 ≤ w := le_trans (by norm_num) hw
    have htarget := mul_le_mul_of_nonneg_right H.reverse_target_radius hw0
    have htarget' :
        (((3 * E.commonCoveringRadius + 2 : ℕ) : ℝ) / 2 +
          (((E.side₂.loss + E.side₂.reserveBound : ℕ) : ℝ) / 2 +
            E.side₂.reserveBound)) * w ≤
          radius *
            (4 * context.scaleDen (selector.chosen A hA).dimension) * w := by
      simpa only [E] using htarget
    rw [integerBoxSideLength_sourceFunctionalControlBox]
    dsimp only [HighCoefficientSideSelectionData.reverseZeroCoordinateCenterError,
      w]
    push_cast at htarget' ⊢
    nlinarith
  let assembled :=
    ofHighCoefficientSideSelection_boundedSupport_zeroCutoff_coordinateCenter
      D E hd hmu hgamma Hbounded.full₁ Hbounded.full₂
      (by simpa only [sourceBoundedSupportAnisotropicConstant, Nat.cast_mul,
          mul_comm] using Hbounded.anisotropic₁.le)
      (by simpa only [sourceBoundedSupportAnisotropicConstant, Nat.cast_mul,
          mul_comm] using Hbounded.anisotropic₂.le)
      htargetForward htargetReverse
  exact ⟨assembled.1, assembled.2⟩

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
