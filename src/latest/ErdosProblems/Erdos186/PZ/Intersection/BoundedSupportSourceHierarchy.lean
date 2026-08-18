/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientSourceHierarchy

/-!
# Source hierarchy for bounded-support zonotope rounding

Once zonotope rounding leaves at most `r` fractional generators, the
anisotropic error factor is `r` rather than `sqrt (r * |core|)`.  It is then
a fixed rank-dependent constant, so the source selected dilation dominates
it for every positive scale exponent `eta`.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

def sourceBoundedSupportAnisotropicConstant
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (r : ℕ) : ℕ :=
  r * sourceAnisotropicConstant context r

def sourceBoundedSupportHierarchyBound
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) : ℕ :=
  sourceFullRankConstantBound context rankCeiling +
    rankCeiling * sourceAnisotropicConstantBound context rankCeiling

theorem sourceBoundedSupportAnisotropicConstant_le_bound
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    {r rankCeiling : ℕ} (hr : r ≤ rankCeiling) :
    sourceBoundedSupportAnisotropicConstant context r ≤
      sourceBoundedSupportHierarchyBound context rankCeiling := by
  have haniso := sourceAnisotropicConstant_le_bound context hr
  unfold sourceBoundedSupportAnisotropicConstant
  unfold sourceBoundedSupportHierarchyBound
  exact (Nat.mul_le_mul hr haniso).trans (Nat.le_add_left _ _)

theorem sourceFullRankConstant_le_boundedSupportHierarchyBound
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    {r rankCeiling : ℕ} (hr : r ≤ rankCeiling) :
    sourceFullRankConstant context r ≤
      sourceBoundedSupportHierarchyBound context rankCeiling := by
  exact (sourceFullRankConstant_le_bound context hr).trans
    (Nat.le_add_right _ _)

/-- The four scalar inequalities after bounded-support rounding. -/
structure HighCoefficientBoundedSupportScalarHierarchies
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
    ((sourceFullRankConstant context
      (selector.chosen A hA).dimension : ℕ) : ℝ) <
      (E.side₁.dilation : ℝ) * gamma
  full₂ :
    ((sourceFullRankConstant context
      (selector.chosen A hA).dimension : ℕ) : ℝ) <
      (E.side₂.dilation : ℝ) * gamma
  anisotropic₁ :
    ((sourceBoundedSupportAnisotropicConstant context
      (selector.chosen A hA).dimension : ℕ) : ℝ) <
      (E.side₁.dilation : ℝ) * gamma
  anisotropic₂ :
    ((sourceBoundedSupportAnisotropicConstant context
      (selector.chosen A hA).dimension : ℕ) : ℝ) <
      (E.side₂.dilation : ℝ) * gamma

/-- For every `eta > 0`, fixed source constants are eventually dominated on
both selected sides.  This is the numerical replacement for the earlier
square-root hierarchy, which required `eta > 1/2`. -/
theorem exists_sourceParameters_highCoefficientBoundedSupportHierarchies
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
        {a₀ : realImage (selector.chosen A hA).identifiedCore}
        {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
        (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
        (theta : ℝ)
        (E : HighCoefficientSideSelectionData selector hA D theta gamma),
        delta * (A.card : ℝ) ≤ (D.largeA₁ theta).card →
        delta * (A.card : ℝ) ≤ (D.largeA₂ theta).card →
        HighCoefficientBoundedSupportScalarHierarchies E := by
  refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
  intro context
  obtain ⟨M, hM⟩ := exists_cardThreshold_selectedCFP_dilation_mul_gamma_gt
    context rankCeiling heta (by norm_num : (0 : ℝ) < 2)
      (sourceBoundedSupportHierarchyBound context rankCeiling : ℝ)
  refine ⟨M, ?_⟩
  intro selector ambient A hA hrank delta gamma mu hparams a₀ c D theta E
    hdense₁ hdense₂
  let S := selector.chosen A hA
  have H₁ := hM A delta gamma mu hparams
    (r := S.dimension)
    (X := Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
    (selector.input _ E.eligible₁) hrank
    (by simpa only [Reduction.card_identifiedTranslate] using hdense₁)
  have H₂ := hM A delta gamma mu hparams
    (r := S.dimension)
    (X := Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
    (selector.input _ E.eligible₂) hrank
    (by simpa only [Reduction.card_identifiedTranslate] using hdense₂)
  have hfull :
      (sourceFullRankConstant context S.dimension : ℝ) ≤
        sourceBoundedSupportHierarchyBound context rankCeiling := by
    exact_mod_cast
      sourceFullRankConstant_le_boundedSupportHierarchyBound context hrank
  have haniso :
      (sourceBoundedSupportAnisotropicConstant context S.dimension : ℝ) ≤
        sourceBoundedSupportHierarchyBound context rankCeiling := by
    exact_mod_cast
      sourceBoundedSupportAnisotropicConstant_le_bound context hrank
  refine {
    full₁ := hfull.trans_lt H₁
    full₂ := hfull.trans_lt H₂
    anisotropic₁ := haniso.trans_lt H₁
    anisotropic₂ := haniso.trans_lt H₂ }

end

end Erdos186.PZ.Intersection
