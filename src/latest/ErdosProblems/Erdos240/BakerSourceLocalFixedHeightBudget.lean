/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities
import ErdosProblems.Erdos240.BakerLemma3Concrete

/-!
# Fixed-height absorption for the local term in source Lemma 4

The freely enlarged normalized exponent controls the row error, whereas the
Liouville comparison at an integral target is naturally expressed in the
fixed source-height unit `h * k * Omega * log OmegaOld`.  This module records
the exact bridge.  The hypothesis `4 * contourConstant <= C₀` is uniform in
the varying final prime and leaves much more than the five fixed-height units
needed by the source argument.
-/

noncomputable section

namespace Erdos240.VDPLParameters

open BakerLemma3Concrete

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  (P : VDPLParameters (Fin oldRank))

/-- After paying the complete local-circle loss, a normalized row-error
exponent of `-2E/3` still leaves five fixed source-height units of decay. -/
theorem localError_add_contourExponent_le_neg_five_sourceHeight
    {C₀ : ℝ}
    (hC₀ : 4 * P.lemmaFourContourAbsorptionConstant ≤ C₀) :
    -2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3 +
        (P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) *
          P.Omega * Real.log P.OmegaOld) / 6 ≤
      -(5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  let X : ℝ := (P.h : ℝ) * W
  let C : ℝ := P.lemmaFourContourAbsorptionConstant
  have hW : 0 < W := by
    dsimp only [W]
    exact mul_pos P.Omega_pos P.log_OmegaOld_pos
  have hX : 0 < X := by
    dsimp only [X]
    exact mul_pos (by exact_mod_cast P.h_pos) hW
  have hCpos : 0 < C := by
    dsimp only [C, lemmaFourContourAbsorptionConstant]
    exact mul_pos (by norm_num) (sq_pos_of_pos P.k_pos)
  have hC₀pos : 0 < C₀ := (mul_pos (by norm_num) hCpos).trans_le hC₀
  have hE : C₀ * X ≤ sourceExponent P (C₀ * Real.log P.OmegaOld) := by
    have hheight : C₀ * (P.h : ℝ) ≤ C₀ * Real.log P.Bsrc :=
      mul_le_mul_of_nonneg_left P.h_cast_le_log_Bsrc hC₀pos.le
    calc
      C₀ * X = (C₀ * (P.h : ℝ)) * P.Omega *
          Real.log P.OmegaOld := by simp only [X, W]; ring
      _ ≤ (C₀ * Real.log P.Bsrc) * P.Omega *
          Real.log P.OmegaOld := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hheight P.Omega_pos.le)
          P.log_OmegaOld_pos.le
      _ = sourceExponent P (C₀ * Real.log P.OmegaOld) := by
        unfold sourceExponent VDPLParameters.Omega
        ring
  have hcoefficient : 30 * P.k + C ≤ 4 * C₀ := by
    have hk : (1 : ℝ) ≤ P.k := P.one_le_k
    have hCeq : C = 960 * P.k ^ 2 := by
      rfl
    have hsmall : 30 * P.k ≤ 15 * C := by
      rw [hCeq]
      nlinarith [sq_nonneg (P.k - 1)]
    nlinarith
  have hscaled : (30 * P.k + C) * X ≤ 4 * C₀ * X :=
    mul_le_mul_of_nonneg_right hcoefficient hX.le
  dsimp only [C, X, W] at hE hscaled ⊢
  nlinarith

/-- Multiplicative form of
`localError_add_contourExponent_le_neg_five_sourceHeight`, ready for the
local-circle estimate in source Lemma 4. -/
theorem exp_localError_mul_contour_le_exp_neg_five_sourceHeight
    {C₀ : ℝ}
    (hC₀ : 4 * P.lemmaFourContourAbsorptionConstant ≤ C₀) :
    Real.exp (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) *
        Real.exp
          ((P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) *
            P.Omega * Real.log P.OmegaOld) / 6) ≤
      Real.exp
        (-(5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr
    (P.localError_add_contourExponent_le_neg_five_sourceHeight hC₀)

/-- Two independently estimated Lemma-4 remainders at the `-5H` scale fit
strictly below the integral Liouville comparison scale `-4H`. -/
theorem add_lt_exp_neg_four_sourceHeight_of_le_exp_neg_five
    {localTerm outerTerm : ℝ}
    (hlocal : localTerm ≤ Real.exp
      (-(5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))))
    (houter : outerTerm ≤ Real.exp
      (-(5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)))) :
    localTerm + outerTerm < Real.exp
      (-(4 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  apply add_lt_exp_neg_of_le_exp_neg hlocal houter
  have hH : (1 : ℝ) ≤
      (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld :=
    P.one_le_sourceHeightUnit
  nlinarith [Real.log_two_lt_d9]

end Erdos240.VDPLParameters

#print axioms Erdos240.VDPLParameters.localError_add_contourExponent_le_neg_five_sourceHeight
#print axioms Erdos240.VDPLParameters.exp_localError_mul_contour_le_exp_neg_five_sourceHeight
#print axioms Erdos240.VDPLParameters.add_lt_exp_neg_four_sourceHeight_of_le_exp_neg_five
