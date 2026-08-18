/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabBoxScale
import ErdosProblems.Erdos186.PZ.Intersection.SourceFrozenParameterAsymptotics

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Frozen source parameters satisfy the box-scale inequality uniformly for
every terminal population above an arbitrary fixed positive power of the
initial one. -/
theorem eventually_sourceFunctionalSlab_powerRange_boxScale
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ {ambient : ℕ}
        (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint ambient)) (hA : selector.Eligible A),
        Real.rpow (initialCard : ℝ) p ≤ (A.card : ℝ) →
        0 < (selector.chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          ((selector.chosen A hA).identifiedCore.card : ℝ) →
        1 ≤
          (2 * ((selector.chosen A hA).dimension : ℝ) *
              sourceFunctionalSlabThickness context rankCeiling
                forwardConstant reverseConstant
                (gamma kappa K initialCard)) *
            ((controlIntegerBox (selector.chosen A hA).progression
              (2 * context.scaleDen
                (selector.chosen A hA).dimension)).carrier.card : ℝ) := by
  let B := sourceFunctionalSlabTermBound context rankCeiling
    forwardConstant reverseConstant
  have hB : 0 ≤ B := sourceFunctionalSlabTermBound_nonneg
    (context := context) hforward hreverse
  have hgrowth := eventually_const_le_gamma_mul_nat_rpow
    kappa K hp (2 * (B + 1))
  filter_upwards [hgrowth, eventually_gamma_pos kappa hK]
    with initialCard hgrowthN hgammaN
  intro ambient selector A hA hlower hd hhalf
  let S := selector.chosen A hA
  let m : ℕ := 2 * context.scaleDen S.dimension
  let boxCard : ℝ := ((controlIntegerBox S.progression m).carrier.card : ℝ)
  let t := sourceFunctionalSlabThickness context rankCeiling
    forwardConstant reverseConstant (gamma kappa K initialCard)
  have hm : 1 ≤ m := by
    dsimp only [m]
    have hden := context.scaleDen_pos S.dimension
    omega
  have hcoreSubset : S.identifiedCore ⊆
      (controlIntegerBox S.progression m).carrier :=
    S.identifiedCore_subset_coefficientBox.trans
      (gapCoefficientBox_subset_controlIntegerBox S.progression hm)
  have hcoreCard : (S.identifiedCore.card : ℝ) ≤ boxCard := by
    dsimp only [boxCard]
    exact_mod_cast Finset.card_le_card hcoreSubset
  have hAbox : (A.card : ℝ) ≤ 2 * boxCard := by linarith
  have hdreal : (1 : ℝ) ≤ S.dimension := by exact_mod_cast hd
  have hAfactor : (A.card : ℝ) ≤
      2 * (S.dimension : ℝ) * boxCard := by
    calc
      (A.card : ℝ) ≤ 2 * boxCard := hAbox
      _ ≤ 2 * (S.dimension : ℝ) * boxCard := by
        have hboxNonneg : 0 ≤ boxCard := by positivity
        nlinarith
  have ht : 0 < t := by
    dsimp only [t]
    exact sourceFunctionalSlabThickness_pos hforward hreverse hgammaN
  have hdenom : 0 < 2 * (B + 1) := by positivity
  have hgammaCurrent : 2 * (B + 1) ≤
      gamma kappa K initialCard * (A.card : ℝ) := by
    exact hgrowthN.trans
      (mul_le_mul_of_nonneg_left hlower hgammaN.le)
  have hone : 1 ≤ t * (A.card : ℝ) := by
    calc
      1 ≤ gamma kappa K initialCard * (A.card : ℝ) /
          (2 * (B + 1)) :=
        (le_div_iff₀ hdenom).2 (by simpa only [one_mul] using hgammaCurrent)
      _ = t * (A.card : ℝ) := by
        dsimp only [t, sourceFunctionalSlabThickness]
        ring
  have hmul := mul_le_mul_of_nonneg_left hAfactor ht.le
  dsimp only [S, m, boxCard, t] at hone hmul ⊢
  calc
    1 ≤ sourceFunctionalSlabThickness context rankCeiling
        forwardConstant reverseConstant (gamma kappa K initialCard) *
          (A.card : ℝ) := hone
    _ ≤ (2 * ((selector.chosen A hA).dimension : ℝ) *
          sourceFunctionalSlabThickness context rankCeiling
            forwardConstant reverseConstant (gamma kappa K initialCard)) *
        ((controlIntegerBox (selector.chosen A hA).progression
          (2 * context.scaleDen
            (selector.chosen A hA).dimension)).carrier.card : ℝ) := by
      nlinarith

/-- Frozen source parameters still satisfy the box-scale inequality uniformly
for every terminal population above the square root of the initial one. -/
theorem eventually_sourceFunctionalSlab_frozen_boxScale
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (kappa K : ℝ) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ {ambient : ℕ}
        (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint ambient)) (hA : selector.Eligible A),
        Real.sqrt (initialCard : ℝ) ≤ (A.card : ℝ) →
        0 < (selector.chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          ((selector.chosen A hA).identifiedCore.card : ℝ) →
        1 ≤
          (2 * ((selector.chosen A hA).dimension : ℝ) *
              sourceFunctionalSlabThickness context rankCeiling
                forwardConstant reverseConstant
                (gamma kappa K initialCard)) *
            ((controlIntegerBox (selector.chosen A hA).progression
              (2 * context.scaleDen
                (selector.chosen A hA).dimension)).carrier.card : ℝ) := by
  let B := sourceFunctionalSlabTermBound context rankCeiling
    forwardConstant reverseConstant
  have hB : 0 ≤ B := sourceFunctionalSlabTermBound_nonneg
    (context := context) hforward hreverse
  have hgrowth := eventually_const_le_gamma_mul_nat_rpow
    kappa K (by norm_num : (0 : ℝ) < 1 / 2) (2 * (B + 1))
  filter_upwards [hgrowth, eventually_gamma_pos kappa hK]
    with initialCard hgrowthN hgammaN
  intro ambient selector A hA hsqrt hd hhalf
  let S := selector.chosen A hA
  let m : ℕ := 2 * context.scaleDen S.dimension
  let boxCard : ℝ := ((controlIntegerBox S.progression m).carrier.card : ℝ)
  let t := sourceFunctionalSlabThickness context rankCeiling
    forwardConstant reverseConstant (gamma kappa K initialCard)
  have hm : 1 ≤ m := by
    dsimp only [m]
    have hden := context.scaleDen_pos S.dimension
    omega
  have hcoreSubset : S.identifiedCore ⊆
      (controlIntegerBox S.progression m).carrier :=
    S.identifiedCore_subset_coefficientBox.trans
      (gapCoefficientBox_subset_controlIntegerBox S.progression hm)
  have hcoreCard : (S.identifiedCore.card : ℝ) ≤ boxCard := by
    dsimp only [boxCard]
    exact_mod_cast Finset.card_le_card hcoreSubset
  have hAbox : (A.card : ℝ) ≤ 2 * boxCard := by linarith
  have hdreal : (1 : ℝ) ≤ S.dimension := by exact_mod_cast hd
  have hAfactor : (A.card : ℝ) ≤
      2 * (S.dimension : ℝ) * boxCard := by
    calc
      (A.card : ℝ) ≤ 2 * boxCard := hAbox
      _ ≤ 2 * (S.dimension : ℝ) * boxCard := by
        have hboxNonneg : 0 ≤ boxCard := by positivity
        nlinarith
  have ht : 0 < t := by
    dsimp only [t]
    exact sourceFunctionalSlabThickness_pos hforward hreverse hgammaN
  have hdenom : 0 < 2 * (B + 1) := by positivity
  have hgammaCurrent : 2 * (B + 1) ≤
      gamma kappa K initialCard * (A.card : ℝ) := by
    calc
      2 * (B + 1) ≤ gamma kappa K initialCard *
          (initialCard : ℝ) ^ (1 / 2 : ℝ) := hgrowthN
      _ = gamma kappa K initialCard *
          Real.sqrt (initialCard : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ ≤ gamma kappa K initialCard * (A.card : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt hgammaN.le
  have hone : 1 ≤ t * (A.card : ℝ) := by
    calc
      1 ≤ gamma kappa K initialCard * (A.card : ℝ) /
          (2 * (B + 1)) :=
        (le_div_iff₀ hdenom).2 (by simpa only [one_mul] using hgammaCurrent)
      _ = t * (A.card : ℝ) := by
        dsimp only [t, sourceFunctionalSlabThickness]
        ring
  have hmul := mul_le_mul_of_nonneg_left hAfactor ht.le
  dsimp only [S, m, boxCard, t] at hone hmul ⊢
  calc
    1 ≤ sourceFunctionalSlabThickness context rankCeiling
        forwardConstant reverseConstant (gamma kappa K initialCard) *
          (A.card : ℝ) := hone
    _ ≤ (2 * ((selector.chosen A hA).dimension : ℝ) *
          sourceFunctionalSlabThickness context rankCeiling
            forwardConstant reverseConstant (gamma kappa K initialCard)) *
        ((controlIntegerBox (selector.chosen A hA).progression
          (2 * context.scaleDen
            (selector.chosen A hA).dimension)).carrier.card : ℝ) := by
      nlinarith

end

end Erdos186.PZ.Intersection
