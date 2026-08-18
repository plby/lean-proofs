/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFrozenParameterAsymptotics
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabDenseDilation

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Uniform low-rank slab inequalities with source parameters frozen at the
initial population and the current population retained above any fixed
positive power of the initial one. -/
theorem eventually_sourceFunctionalSlab_powerRange_lowRank
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ (currentCard : ℕ),
        Real.rpow (initialCard : ℝ) p ≤ (currentCard : ℝ) →
        ∀ {r : ℕ} {X : Finset (LatticePoint r)}
          (I : Reduction.EligibleInput context X),
          r ≤ rankCeiling →
          delta kappa initialCard * (currentCard : ℝ) ≤
            (X.card : ℝ) →
          sourceFunctionalSlabFixedTerm context forwardConstant r <
              (I.selectedCFP.dilation : ℝ) *
                gamma kappa K initialCard ∧
            sourceFunctionalSlabFixedTerm context reverseConstant r <
              (I.selectedCFP.dilation : ℝ) *
                gamma kappa K initialCard := by
  let D : ℕ := Reduction.scaleDenSum context rankCeiling
  let B : ℝ := sourceFunctionalSlabTermBound context rankCeiling
    forwardConstant reverseConstant
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
    calc
      (initialCard : ℝ) ^ (p * eta) =
          ((initialCard : ℝ) ^ p) ^ eta :=
        Real.rpow_mul hNnonneg p eta
      _ ≤ (currentCard : ℝ) ^ eta :=
        Real.rpow_le_rpow (Real.rpow_nonneg hNnonneg p) hlower heta.le
  have hpower : delta kappa initialCard ^ eta *
        (currentCard : ℝ) ^ eta ≤
      (D : ℝ) * (I.selectedCFP.dilation : ℝ) := by
    simpa only [D] using fixed_dense_power_le_scaleDenSum_mul_dilation
      context I heta.le hdeltaN.le hrank hdense
  have hparameterPower :
      gamma kappa K initialCard * delta kappa initialCard ^ eta *
          (initialCard : ℝ) ^ (p * eta) ≤
        gamma kappa K initialCard *
          (delta kappa initialCard ^ eta *
            (currentCard : ℝ) ^ eta) := by
    have hdeltaPow : 0 ≤ delta kappa initialCard ^ eta :=
      Real.rpow_nonneg hdeltaN.le _
    nlinarith [mul_le_mul_of_nonneg_left hpopulationPower hdeltaPow,
      hgammaN.le]
  have hscaled :
      gamma kappa K initialCard *
          (delta kappa initialCard ^ eta *
            (currentCard : ℝ) ^ eta) ≤
        gamma kappa K initialCard *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) :=
    mul_le_mul_of_nonneg_left hpower hgammaN.le
  have hDB : (D : ℝ) * B <
      (D : ℝ) *
        ((I.selectedCFP.dilation : ℝ) *
          gamma kappa K initialCard) := by
    calc
      (D : ℝ) * B < (D : ℝ) * B + 1 := by linarith
      _ ≤ gamma kappa K initialCard * delta kappa initialCard ^ eta *
          (initialCard : ℝ) ^ (p * eta) := hgrowthN
      _ ≤ gamma kappa K initialCard *
          (delta kappa initialCard ^ eta *
            (currentCard : ℝ) ^ eta) := hparameterPower
      _ ≤ gamma kappa K initialCard *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) := hscaled
      _ = (D : ℝ) * ((I.selectedCFP.dilation : ℝ) *
          gamma kappa K initialCard) := by ring
  have hBstrict : B < (I.selectedCFP.dilation : ℝ) *
      gamma kappa K initialCard :=
    (mul_lt_mul_iff_of_pos_left hDreal).mp hDB
  constructor
  · exact (sourceFunctionalSlabFixedTerm_le_bound
      hforward hreverse hrank).trans_lt hBstrict
  · exact (sourceFunctionalSlabReverseFixedTerm_le_bound
      hforward hreverse hrank).trans_lt hBstrict

/-- Uniform low-rank slab inequalities with the source parameters frozen at
the initial population and the current population only assumed to remain
above its square root. -/
theorem eventually_sourceFunctionalSlab_frozen_lowRank
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ (currentCard : ℕ),
        Real.sqrt (initialCard : ℝ) ≤ (currentCard : ℝ) →
        ∀ {r : ℕ} {X : Finset (LatticePoint r)}
          (I : Reduction.EligibleInput context X),
          r ≤ rankCeiling →
          delta kappa initialCard * (currentCard : ℝ) ≤
            (X.card : ℝ) →
          sourceFunctionalSlabFixedTerm context forwardConstant r <
              (I.selectedCFP.dilation : ℝ) *
                gamma kappa K initialCard ∧
            sourceFunctionalSlabFixedTerm context reverseConstant r <
              (I.selectedCFP.dilation : ℝ) *
                gamma kappa K initialCard := by
  let D : ℕ := Reduction.scaleDenSum context rankCeiling
  let B : ℝ := sourceFunctionalSlabTermBound context rankCeiling
    forwardConstant reverseConstant
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
  have hcurrentNonneg : (0 : ℝ) ≤ (currentCard : ℝ) := by positivity
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
          (delta kappa initialCard ^ eta *
            (currentCard : ℝ) ^ eta) := by
    have hdeltaPow : 0 ≤ delta kappa initialCard ^ eta :=
      Real.rpow_nonneg hdeltaN.le _
    nlinarith [mul_le_mul_of_nonneg_left hpopulationPower hdeltaPow,
      hgammaN.le]
  have hscaled :
      gamma kappa K initialCard *
          (delta kappa initialCard ^ eta *
            (currentCard : ℝ) ^ eta) ≤
        gamma kappa K initialCard *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) :=
    mul_le_mul_of_nonneg_left hpower hgammaN.le
  have hDB : (D : ℝ) * B <
      (D : ℝ) *
        ((I.selectedCFP.dilation : ℝ) *
          gamma kappa K initialCard) := by
    calc
      (D : ℝ) * B < (D : ℝ) * B + 1 := by linarith
      _ ≤ gamma kappa K initialCard * delta kappa initialCard ^ eta *
          (initialCard : ℝ) ^ (eta / 2) := hgrowthN
      _ ≤ gamma kappa K initialCard *
          (delta kappa initialCard ^ eta *
            (currentCard : ℝ) ^ eta) := hparameterPower
      _ ≤ gamma kappa K initialCard *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) := hscaled
      _ = (D : ℝ) * ((I.selectedCFP.dilation : ℝ) *
          gamma kappa K initialCard) := by ring
  have hBstrict : B < (I.selectedCFP.dilation : ℝ) *
      gamma kappa K initialCard :=
    (mul_lt_mul_iff_of_pos_left hDreal).mp hDB
  constructor
  · exact (sourceFunctionalSlabFixedTerm_le_bound
      hforward hreverse hrank).trans_lt hBstrict
  · exact (sourceFunctionalSlabReverseFixedTerm_le_bound
      hforward hreverse hrank).trans_lt hBstrict

end

end Erdos186.PZ.Intersection
