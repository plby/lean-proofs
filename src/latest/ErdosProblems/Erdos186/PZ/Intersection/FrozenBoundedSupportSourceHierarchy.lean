/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.BoundedSupportSourceHierarchy
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabFrozenLowRank

/-!
# Bounded-support hierarchies with parameters frozen at the initial population
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Every dense terminal side of bounded rank has enough selected dilation
for bounded-support rounding, uniformly throughout the retained square-root
range of a frozen source population. -/
theorem eventually_frozen_selectedCFP_dilation_mul_gamma_gt_boundedSupport
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hK : 0 < K) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ (currentCard : ℕ),
        Real.sqrt (initialCard : ℝ) ≤ (currentCard : ℝ) →
        ∀ {r : ℕ} {X : Finset (LatticePoint r)}
          (I : Reduction.EligibleInput context X),
          r ≤ rankCeiling →
          delta kappa initialCard * (currentCard : ℝ) ≤ (X.card : ℝ) →
          (sourceBoundedSupportHierarchyBound context rankCeiling : ℝ) <
            (I.selectedCFP.dilation : ℝ) * gamma kappa K initialCard := by
  let D : ℕ := Reduction.scaleDenSum context rankCeiling
  let B : ℝ := sourceBoundedSupportHierarchyBound context rankCeiling
  have hD : 0 < D := Reduction.scaleDenSum_pos context rankCeiling
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hgrowth :=
    eventually_const_le_gamma_mul_delta_rpow_mul_nat_half_rpow
      kappa K heta ((D : ℝ) * B + 1)
  filter_upwards [hgrowth, eventually_delta_pos kappa,
      eventually_gamma_pos kappa hK, eventually_gt_atTop (0 : ℕ)]
    with initialCard hgrowthN hdeltaN hgammaN hN
  intro currentCard hsqrt r X I hrank hdense
  have hNnonneg : (0 : ℝ) ≤ (initialCard : ℝ) := by positivity
  have hrootPower : (initialCard : ℝ) ^ (eta / 2) =
      Real.sqrt (initialCard : ℝ) ^ eta := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNnonneg]
    congr 1
    ring
  have hpopulationPower : (initialCard : ℝ) ^ (eta / 2) ≤
      (currentCard : ℝ) ^ eta := by
    rw [hrootPower]
    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) hsqrt heta.le
  have hpower : delta kappa initialCard ^ eta *
        (currentCard : ℝ) ^ eta ≤
      (D : ℝ) * (I.selectedCFP.dilation : ℝ) := by
    simpa only [D] using fixed_dense_power_le_scaleDenSum_mul_dilation
      context I heta.le hdeltaN.le hrank hdense
  have hparameterPower :
      gamma kappa K initialCard * delta kappa initialCard ^ eta *
          (initialCard : ℝ) ^ (eta / 2) ≤
        gamma kappa K initialCard *
          (delta kappa initialCard ^ eta * (currentCard : ℝ) ^ eta) := by
    have hdeltaPow : 0 ≤ delta kappa initialCard ^ eta :=
      Real.rpow_nonneg hdeltaN.le _
    nlinarith [mul_le_mul_of_nonneg_left hpopulationPower hdeltaPow,
      hgammaN.le]
  have hscaled :
      gamma kappa K initialCard *
          (delta kappa initialCard ^ eta * (currentCard : ℝ) ^ eta) ≤
        gamma kappa K initialCard *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) :=
    mul_le_mul_of_nonneg_left hpower hgammaN.le
  have hDB : (D : ℝ) * B <
      (D : ℝ) * ((I.selectedCFP.dilation : ℝ) *
        gamma kappa K initialCard) := by
    calc
      (D : ℝ) * B < (D : ℝ) * B + 1 := by linarith
      _ ≤ gamma kappa K initialCard * delta kappa initialCard ^ eta *
          (initialCard : ℝ) ^ (eta / 2) := hgrowthN
      _ ≤ gamma kappa K initialCard *
          (delta kappa initialCard ^ eta * (currentCard : ℝ) ^ eta) :=
        hparameterPower
      _ ≤ gamma kappa K initialCard *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) := hscaled
      _ = (D : ℝ) * ((I.selectedCFP.dilation : ℝ) *
          gamma kappa K initialCard) := by ring
  exact (mul_lt_mul_iff_of_pos_left hDreal).mp hDB

/-- Arbitrary positive power-range version of the frozen selected-dilation
hierarchy. -/
theorem eventually_powerRange_selectedCFP_dilation_mul_gamma_gt_boundedSupport
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ) (hK : 0 < K) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ (currentCard : ℕ),
        (initialCard : ℝ) ^ p ≤ (currentCard : ℝ) →
        ∀ {r : ℕ} {X : Finset (LatticePoint r)}
          (I : Reduction.EligibleInput context X),
          r ≤ rankCeiling →
          delta kappa initialCard * (currentCard : ℝ) ≤ (X.card : ℝ) →
          (sourceBoundedSupportHierarchyBound context rankCeiling : ℝ) <
            (I.selectedCFP.dilation : ℝ) * gamma kappa K initialCard := by
  let D : ℕ := Reduction.scaleDenSum context rankCeiling
  let B : ℝ := sourceBoundedSupportHierarchyBound context rankCeiling
  have hD : 0 < D := Reduction.scaleDenSum_pos context rankCeiling
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hgrowth :=
    eventually_const_le_gamma_mul_delta_rpow_mul_nat_rpow
      kappa K heta hp ((D : ℝ) * B + 1)
  filter_upwards [hgrowth, eventually_delta_pos kappa,
      eventually_gamma_pos kappa hK, eventually_gt_atTop (0 : ℕ)]
    with initialCard hgrowthN hdeltaN hgammaN hN
  intro currentCard hlower r X I hrank hdense
  have hNnonneg : (0 : ℝ) ≤ (initialCard : ℝ) := by positivity
  have hpopulationPower : (initialCard : ℝ) ^ (p * eta) ≤
      (currentCard : ℝ) ^ eta := by
    rw [Real.rpow_mul hNnonneg]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hNnonneg p) hlower heta.le
  have hpower : delta kappa initialCard ^ eta *
        (currentCard : ℝ) ^ eta ≤
      (D : ℝ) * (I.selectedCFP.dilation : ℝ) := by
    simpa only [D] using fixed_dense_power_le_scaleDenSum_mul_dilation
      context I heta.le hdeltaN.le hrank hdense
  have hparameterPower :
      gamma kappa K initialCard * delta kappa initialCard ^ eta *
          (initialCard : ℝ) ^ (p * eta) ≤
        gamma kappa K initialCard *
          (delta kappa initialCard ^ eta * (currentCard : ℝ) ^ eta) := by
    have hdeltaPow : 0 ≤ delta kappa initialCard ^ eta :=
      Real.rpow_nonneg hdeltaN.le _
    nlinarith [mul_le_mul_of_nonneg_left hpopulationPower hdeltaPow,
      hgammaN.le]
  have hscaled :
      gamma kappa K initialCard *
          (delta kappa initialCard ^ eta * (currentCard : ℝ) ^ eta) ≤
        gamma kappa K initialCard *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) :=
    mul_le_mul_of_nonneg_left hpower hgammaN.le
  have hDB : (D : ℝ) * B <
      (D : ℝ) * ((I.selectedCFP.dilation : ℝ) *
        gamma kappa K initialCard) := by
    calc
      (D : ℝ) * B < (D : ℝ) * B + 1 := by linarith
      _ ≤ gamma kappa K initialCard * delta kappa initialCard ^ eta *
          (initialCard : ℝ) ^ (p * eta) := hgrowthN
      _ ≤ gamma kappa K initialCard *
          (delta kappa initialCard ^ eta * (currentCard : ℝ) ^ eta) :=
        hparameterPower
      _ ≤ gamma kappa K initialCard *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) := hscaled
      _ = (D : ℝ) * ((I.selectedCFP.dilation : ℝ) *
          gamma kappa K initialCard) := by ring
  exact (mul_lt_mul_iff_of_pos_left hDreal).mp hDB

/-- Threshold form, packaged directly as the four inequalities consumed by
the zero-cutoff canonical post-CFP constructor. -/
theorem exists_frozen_highCoefficientBoundedSupportHierarchyThreshold
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hK : 0 < K) :
    ∃ threshold : ℕ, ∀ {initialCard ambient : ℕ},
      threshold ≤ initialCard →
      ∀ (A : Finset (LatticePoint ambient))
        (hA : (context.scaleSelector exponent).Eligible A),
        Real.sqrt (initialCard : ℝ) ≤ (A.card : ℝ) →
        ((context.scaleSelector exponent).chosen A hA).dimension ≤
          rankCeiling →
        ∀ {a₀ : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore}
          {c : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore → ℝ}
          (D : ConvexPoolsData
            ((context.scaleSelector exponent).chosen A hA).identifiedCore a₀ c
              (mu kappa initialCard))
          (E : HighCoefficientSideSelectionData
            (context.scaleSelector exponent) hA D 0
              (gamma kappa K initialCard)),
          delta kappa initialCard * (A.card : ℝ) ≤
              (D.largeA₁ 0).card →
          delta kappa initialCard * (A.card : ℝ) ≤
              (D.largeA₂ 0).card →
          HighCoefficientBoundedSupportScalarHierarchies E := by
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
    (eventually_frozen_selectedCFP_dilation_mul_gamma_gt_boundedSupport
      context rankCeiling heta kappa K hK)
  refine ⟨threshold, ?_⟩
  intro initialCard ambient hlarge A hA hsqrt hrank a₀ c D E hdense₁ hdense₂
  let selector := context.scaleSelector exponent
  have H₁ := hthreshold initialCard hlarge A.card hsqrt
    (selector.input _ E.eligible₁) hrank
    (by simpa only [Reduction.card_identifiedTranslate] using hdense₁)
  have H₂ := hthreshold initialCard hlarge A.card hsqrt
    (selector.input _ E.eligible₂) hrank
    (by simpa only [Reduction.card_identifiedTranslate] using hdense₂)
  have hfull :
      (sourceFullRankConstant context
        (selector.chosen A hA).dimension : ℝ) ≤
        sourceBoundedSupportHierarchyBound context rankCeiling := by
    exact_mod_cast
      sourceFullRankConstant_le_boundedSupportHierarchyBound context hrank
  have haniso :
      (sourceBoundedSupportAnisotropicConstant context
        (selector.chosen A hA).dimension : ℝ) ≤
        sourceBoundedSupportHierarchyBound context rankCeiling := by
    exact_mod_cast
      sourceBoundedSupportAnisotropicConstant_le_bound context hrank
  exact {
    full₁ := hfull.trans_lt H₁
    full₂ := hfull.trans_lt H₂
    anisotropic₁ := haniso.trans_lt H₁
    anisotropic₂ := haniso.trans_lt H₂ }

/-- Threshold form of the arbitrary positive power-range bounded-support
hierarchy. -/
theorem exists_powerRange_highCoefficientBoundedSupportHierarchyThreshold
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ) (hK : 0 < K) :
    ∃ threshold : ℕ, ∀ {initialCard ambient : ℕ},
      threshold ≤ initialCard →
      ∀ (A : Finset (LatticePoint ambient))
        (hA : (context.scaleSelector exponent).Eligible A),
        (initialCard : ℝ) ^ p ≤ (A.card : ℝ) →
        ((context.scaleSelector exponent).chosen A hA).dimension ≤
          rankCeiling →
        ∀ {a₀ : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore}
          {c : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore → ℝ}
          (D : ConvexPoolsData
            ((context.scaleSelector exponent).chosen A hA).identifiedCore a₀ c
              (mu kappa initialCard))
          (E : HighCoefficientSideSelectionData
            (context.scaleSelector exponent) hA D 0
              (gamma kappa K initialCard)),
          delta kappa initialCard * (A.card : ℝ) ≤
              (D.largeA₁ 0).card →
          delta kappa initialCard * (A.card : ℝ) ≤
              (D.largeA₂ 0).card →
          HighCoefficientBoundedSupportScalarHierarchies E := by
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
    (eventually_powerRange_selectedCFP_dilation_mul_gamma_gt_boundedSupport
      context rankCeiling heta p hp kappa K hK)
  refine ⟨threshold, ?_⟩
  intro initialCard ambient hlarge A hA hlower hrank a₀ c D E hdense₁ hdense₂
  let selector := context.scaleSelector exponent
  have H₁ := hthreshold initialCard hlarge A.card hlower
    (selector.input _ E.eligible₁) hrank
    (by simpa only [Reduction.card_identifiedTranslate] using hdense₁)
  have H₂ := hthreshold initialCard hlarge A.card hlower
    (selector.input _ E.eligible₂) hrank
    (by simpa only [Reduction.card_identifiedTranslate] using hdense₂)
  have hfull :
      (sourceFullRankConstant context
        (selector.chosen A hA).dimension : ℝ) ≤
        sourceBoundedSupportHierarchyBound context rankCeiling := by
    exact_mod_cast
      sourceFullRankConstant_le_boundedSupportHierarchyBound context hrank
  have haniso :
      (sourceBoundedSupportAnisotropicConstant context
        (selector.chosen A hA).dimension : ℝ) ≤
        sourceBoundedSupportHierarchyBound context rankCeiling := by
    exact_mod_cast
      sourceBoundedSupportAnisotropicConstant_le_bound context hrank
  exact {
    full₁ := hfull.trans_lt H₁
    full₂ := hfull.trans_lt H₂
    anisotropic₁ := haniso.trans_lt H₁
    anisotropic₂ := haniso.trans_lt H₂ }

end

end Erdos186.PZ.Intersection
