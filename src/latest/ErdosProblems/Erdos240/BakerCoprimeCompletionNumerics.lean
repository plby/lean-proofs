/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceCoprimeHermiteBudget
import ErdosProblems.Erdos240.BakerSourceCoprimeFixedHeightBudget
import ErdosProblems.Erdos240.BakerCoprimeFactorialCancellation
import ErdosProblems.Erdos240.BakerSourceOversizedConstantNumerics
import ErdosProblems.Erdos240.BakerSourceInitialOuterBudget

/-!
# Final numerical assembly for the p. 52 coprime completion

The arbitrary-node Hermite estimate exposes three elementary finite-sum
factors in addition to the source's explicit Hermite factor.  This file
absorbs those factors into one more copy of the node-radius exponent, and
then applies the checked source budget.
-/

noncomputable section

namespace Erdos240.VDPLParameters

open BakerCoprimeFactorialCancellation
open BakerCoprimeInterpolation
open BakerLemma3Concrete
open BakerSourceOversizedConstantNumerics

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  (P : VDPLParameters (Fin oldRank))

/-- The raw finite-sum factor in the arbitrary-node Hermite estimate is a
subfactor of `q^T * 2^((5R+3)T)`. -/
theorem coprime_fullHermiteFactor_le
    {J : ℕ} (hJ : P.LevelOK J) :
    ((coprimeNodeIndices P.q (P.R (J + 1))).card : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
        (((P.q : ℝ) * (2 : ℝ) ^ (3 * P.R (J + 1))) ^
            (P.Sstep J / 4) *
          (2 : ℝ) ^
            ((coprimeNodeIndices P.q (P.R (J + 1))).card *
                (P.Sstep J / 4) + (P.Sstep J / 4))) ≤
      (P.q : ℝ) ^ (P.Sstep J / 4) *
        (2 : ℝ) ^
          ((5 * P.R (J + 1) + 3) * (P.Sstep J / 4)) := by
  let R : ℕ := P.R (J + 1)
  let T : ℕ := P.Sstep J / 4
  let c : ℕ := (coprimeNodeIndices P.q R).card
  have hT : 0 < T := by
    simpa only [T] using P.Sstep_div_four_pos_of_LevelOK hJ
  have hcR : c ≤ R := by
    dsimp only [c]
    calc
      (coprimeNodeIndices P.q R).card ≤ (Finset.range R).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = R := Finset.card_range R
  have hcPow : (c : ℝ) ≤ (2 : ℝ) ^ c := by
    exact_mod_cast nat_le_two_pow c
  have hTPow : (T : ℝ) ≤ (2 : ℝ) ^ T := by
    exact_mod_cast nat_le_two_pow T
  have hcoeff : (c : ℝ) * T * T ≤ (2 : ℝ) ^ (c + 2 * T) := by
    calc
      (c : ℝ) * T * T ≤
          (2 : ℝ) ^ c * (2 : ℝ) ^ T * (2 : ℝ) ^ T := by
        exact mul_le_mul
          (mul_le_mul hcPow hTPow (by positivity) (by positivity))
          hTPow (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (c + 2 * T) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have hindex :
      c + 2 * T + ((3 * R) * T + (c * T + T)) ≤
        (5 * R + 3) * T := by
    have hcT : c * T ≤ R * T := Nat.mul_le_mul_right T hcR
    have hRT : R ≤ R * T := Nat.le_mul_of_pos_right R hT
    have hcRT : c ≤ R * T := hcR.trans hRT
    calc
      c + 2 * T + ((3 * R) * T + (c * T + T)) =
          c + 2 * T + (3 * (R * T) + (c * T + T)) := by ring
      _ ≤
          R * T + 2 * T + (3 * (R * T) + (R * T + T)) := by
        omega
      _ = (5 * R + 3) * T := by ring
  change (c : ℝ) * T * T *
      (((P.q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T *
        (2 : ℝ) ^ (c * T + T)) ≤
    (P.q : ℝ) ^ T * (2 : ℝ) ^ ((5 * R + 3) * T)
  have hKpow :
      (((P.q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T *
          (2 : ℝ) ^ (c * T + T)) =
        (P.q : ℝ) ^ T *
          (2 : ℝ) ^ ((3 * R) * T + (c * T + T)) := by
    rw [mul_pow, ← pow_mul, pow_add]
    ring
  calc
    (c : ℝ) * T * T *
        (((P.q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T *
          (2 : ℝ) ^ (c * T + T)) =
      (P.q : ℝ) ^ T *
        (((c : ℝ) * T * T) *
          (2 : ℝ) ^ ((3 * R) * T + (c * T + T))) := by
      rw [hKpow]
      ring
    _ ≤ (P.q : ℝ) ^ T *
        ((2 : ℝ) ^ (c + 2 * T) *
          (2 : ℝ) ^ ((3 * R) * T + (c * T + T))) := by
      gcongr
    _ = (P.q : ℝ) ^ T *
        (2 : ℝ) ^
          (c + 2 * T + ((3 * R) * T + (c * T + T))) := by
      rw [pow_add]
      ring
    _ ≤ (P.q : ℝ) ^ T * (2 : ℝ) ^ ((5 * R + 3) * T) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hindex)
        (by positivity)

/-- The exact Hermite loss used by the completion is absorbed by the
oversized source exponent. -/
theorem coprime_fullHermiteFactor_le_exp_sixth
    {J : ℕ} (hJ : P.LevelOK J) {C₀ : ℝ}
    (hstruct : 4 * P.C ≤ C₀) :
    ((coprimeNodeIndices P.q (P.R (J + 1))).card : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
        (((P.q : ℝ) * (2 : ℝ) ^ (3 * P.R (J + 1))) ^
            (P.Sstep J / 4) *
          (2 : ℝ) ^
            ((coprimeNodeIndices P.q (P.R (J + 1))).card *
                (P.Sstep J / 4) + (P.Sstep J / 4))) ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 6) := by
  refine (P.coprime_fullHermiteFactor_le hJ).trans ?_
  refine (P.coprime_explicitHermiteFactor_le_exp_twelfth hJ).trans ?_
  apply Real.exp_le_exp.mpr
  have hmono := sourceExponent_mono_normalized P hstruct
  rw [sourceExponent_four_mul] at hmono
  have hEC : 0 ≤ sourceExponent P (P.C * Real.log P.OmegaOld) :=
    BakerLemma3Concrete.sourceExponent_nonneg P
      (mul_nonneg P.C_pos.le P.log_OmegaOld_pos.le)
  linarith

/-- Four-times structural domination makes half of the normalized source
exponent at least four fixed source-height units. -/
theorem eight_mul_sourceHeight_le_sourceExponent_of_structural
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀) :
    8 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) ≤
      sourceExponent P (C₀ * Real.log P.OmegaOld) := by
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  have hW : 0 < W := by
    dsimp only [W]
    exact mul_pos P.Omega_pos P.log_OmegaOld_pos
  have hk : (2 : ℝ) ≤ P.k := by
    have hqk : (13 : ℝ) ≤ P.k := by
      have hepsOne : P.epsilon ≤ 1 := by
        rw [P.epsilon_eq]
        have hrank : (1 : ℝ) ≤ P.rank + 1 := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
        apply (div_le_one (by positivity :
          (0 : ℝ) < 6 * (P.rank + 1))).2
        nlinarith
      calc
        (13 : ℝ) = P.q := by norm_num [VDPLParameters.q]
        _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
        _ ≤ P.k := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le P.one_le_k hepsOne
    linarith
  have hCeq : P.C = P.k ^ 2 := by
    unfold VDPLParameters.C
    rw [P.mu_eq]
    norm_num [Real.rpow_two]
  have hC₀k : 8 * P.k ≤ C₀ := by
    rw [hCeq] at hstruct
    nlinarith [sq_nonneg (P.k - 2)]
  have hC₀pos : 0 ≤ C₀ :=
    (mul_pos (by norm_num) P.C_pos).le.trans hstruct
  have hheight : C₀ * (P.h : ℝ) ≤ C₀ * Real.log P.Bsrc :=
    mul_le_mul_of_nonneg_left P.h_cast_le_log_Bsrc hC₀pos
  calc
    8 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) =
        (8 * P.k) * (P.h * W) := by simp only [W]; ring
    _ ≤ C₀ * (P.h * W) :=
      mul_le_mul_of_nonneg_right hC₀k (mul_nonneg (by positivity) hW.le)
    _ ≤ (C₀ * Real.log P.Bsrc) * W := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hheight hW.le
    _ = sourceExponent P (C₀ * Real.log P.OmegaOld) := by
      unfold sourceExponent
      dsimp only [W, VDPLParameters.Omega]
      ring

/-- The completed Hermite polynomial is below four fixed source-height
units, a convenient form for the final strict sum. -/
theorem exp_neg_half_sourceExponent_le_exp_neg_four_sourceHeight
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀) :
    Real.exp (-sourceExponent P (C₀ * Real.log P.OmegaOld) / 2) ≤
      Real.exp (-(4 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  apply Real.exp_le_exp.mpr
  have h := P.eight_mul_sourceHeight_le_sourceExponent_of_structural hstruct
  linarith

/-- The sharp coprime nodal decay pays the boundary growth and the `4/3`
radial factor while retaining `13/4` source-height units. -/
theorem four_thirds_mul_growth_mul_coprime_decay_lt_exp_neg_thirteen_quarters
    {J : ℕ} (hJ : P.LevelOK J) {growth : ℝ}
    (hgrowth : growth ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (4 / 3 : ℝ) * growth *
        (((3 : ℝ)⁻¹ ^ (P.R (J + 1) * (P.q - 1) / P.q)) ^
          (P.Sstep J / 4)) <
      Real.exp (-(13 / 4 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let decay : ℝ := ((3 : ℝ)⁻¹) ^
    ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4))
  have hH : (26 / 3 : ℝ) < H := by
    simpa only [H] using P.twentySix_thirds_lt_sourceHeightUnit
  have hdecay : decay < Real.exp (-(11 / 2 : ℝ) * H) := by
    simpa only [decay, H] using
      P.coprime_decay_pow_lt_exp_neg_eleven_halves_sourceHeight hJ
  have hgrowthH : growth ≤ Real.exp (2 * H) := by
    convert hgrowth using 1 <;> dsimp only [H] <;> ring
  have hfactor : (4 / 3 : ℝ) < Real.exp (H / 4) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    apply Real.exp_lt_exp.mpr
    have hlog : Real.log (4 / 3 : ℝ) < 1 / 2 := by
      have h := Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num : (4 / 3 : ℝ) ≠ 1)
      norm_num at h ⊢
      linarith
    linarith
  rw [P.coprime_decay_source_power_eq J]
  change (4 / 3 : ℝ) * growth * decay < _
  calc
    (4 / 3 : ℝ) * growth * decay ≤
        (4 / 3 : ℝ) * Real.exp (2 * H) * decay := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgrowthH (by norm_num))
        (by positivity)
    _ < (4 / 3 : ℝ) * Real.exp (2 * H) *
        Real.exp (-(11 / 2 : ℝ) * H) := by
      exact mul_lt_mul_of_pos_left hdecay
        (mul_pos (by norm_num) (Real.exp_pos _))
    _ = (4 / 3 : ℝ) *
        (Real.exp (2 * H) * Real.exp (-(11 / 2 : ℝ) * H)) := by ring
    _ = (4 / 3 : ℝ) * Real.exp (-(7 / 2 : ℝ) * H) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ < Real.exp (H / 4) * Real.exp (-(7 / 2 : ℝ) * H) :=
      mul_lt_mul_of_pos_right hfactor (Real.exp_pos _)
    _ = Real.exp (-(13 / 4 : ℝ) * H) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-(13 / 4 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := rfl

/-- The source-faithful boundary estimate on the radius-`4R` circle costs
`7H/3`, rather than the optimistic `2H`.  The exact coprime nodal product
still leaves `35H/12` after paying the radial factor `4/3`. -/
theorem four_thirds_mul_seven_thirds_growth_mul_coprime_decay_lt_exp_neg_thirtyFive_twelfths
    {J : ℕ} (hJ : P.LevelOK J) {growth : ℝ}
    (hgrowth : growth ≤ Real.exp
      ((7 / 3 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (4 / 3 : ℝ) * growth *
        (((3 : ℝ)⁻¹ ^ (P.R (J + 1) * (P.q - 1) / P.q)) ^
          (P.Sstep J / 4)) <
      Real.exp (-(35 / 12 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let decay : ℝ := ((3 : ℝ)⁻¹) ^
    ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4))
  have hH : (26 / 3 : ℝ) < H := by
    simpa only [H] using P.twentySix_thirds_lt_sourceHeightUnit
  have hdecay : decay < Real.exp (-(11 / 2 : ℝ) * H) := by
    simpa only [decay, H] using
      P.coprime_decay_pow_lt_exp_neg_eleven_halves_sourceHeight hJ
  have hgrowthH : growth ≤ Real.exp ((7 / 3 : ℝ) * H) := by
    convert hgrowth using 1 <;> dsimp only [H] <;> ring
  have hfactor : (4 / 3 : ℝ) < Real.exp (H / 4) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    apply Real.exp_lt_exp.mpr
    have hlog : Real.log (4 / 3 : ℝ) < 1 / 2 := by
      have h := Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num : (4 / 3 : ℝ) ≠ 1)
      norm_num at h ⊢
      linarith
    linarith
  rw [P.coprime_decay_source_power_eq J]
  change (4 / 3 : ℝ) * growth * decay < _
  calc
    (4 / 3 : ℝ) * growth * decay ≤
        (4 / 3 : ℝ) * Real.exp ((7 / 3 : ℝ) * H) * decay := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgrowthH (by norm_num))
        (by positivity)
    _ < (4 / 3 : ℝ) * Real.exp ((7 / 3 : ℝ) * H) *
        Real.exp (-(11 / 2 : ℝ) * H) := by
      exact mul_lt_mul_of_pos_left hdecay
        (mul_pos (by norm_num) (Real.exp_pos _))
    _ = (4 / 3 : ℝ) *
        (Real.exp ((7 / 3 : ℝ) * H) *
          Real.exp (-(11 / 2 : ℝ) * H)) := by ring
    _ = (4 / 3 : ℝ) * Real.exp (-(19 / 6 : ℝ) * H) := by
      congr 1
      calc
        Real.exp ((7 / 3 : ℝ) * H) * Real.exp (-(11 / 2 : ℝ) * H) =
            Real.exp (((7 / 3 : ℝ) * H) + (-(11 / 2 : ℝ) * H)) :=
          (Real.exp_add _ _).symm
        _ = Real.exp (-(19 / 6 : ℝ) * H) := by congr 1 <;> ring
    _ < Real.exp (H / 4) * Real.exp (-(19 / 6 : ℝ) * H) :=
      mul_lt_mul_of_pos_right hfactor (Real.exp_pos _)
    _ = Real.exp (-(35 / 12 : ℝ) * H) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-(35 / 12 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := rfl

/-- With the honest `7H/3` boundary cost, the polynomial and contour
remainders together are still strictly below the sharp successor
Liouville scale `exp (-5H/2)`. -/
theorem polynomial_add_outer_lt_exp_neg_five_halves_sourceHeight
    {polynomialTerm outerTerm : ℝ}
    (hpoly : polynomialTerm ≤ Real.exp
      (-(4 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))))
    (houter : outerTerm < Real.exp
      (-(35 / 12 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    polynomialTerm + outerTerm < Real.exp
      (-((5 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hH : (26 / 3 : ℝ) < H := by
    simpa only [H] using P.twentySix_thirds_lt_sourceHeightUnit
  have hpoly' : polynomialTerm ≤ Real.exp (-(35 / 12 : ℝ) * H) := by
    refine hpoly.trans (Real.exp_le_exp.mpr ?_)
    linarith
  have houter' : outerTerm ≤ Real.exp (-(35 / 12 : ℝ) * H) :=
    houter.le
  have hlog : Real.log 2 < (35 / 12 : ℝ) * H - (5 / 2 : ℝ) * H := by
    have : Real.log 2 < 1 := by nlinarith [Real.log_two_lt_d9]
    linarith
  exact add_lt_exp_neg_of_le_exp_neg
    (by simpa only [neg_mul] using hpoly')
    (by simpa only [neg_mul] using houter') hlog

/-- The polynomial and outer remainders together retain three full
source-height units. -/
theorem polynomial_add_outer_lt_exp_neg_three_sourceHeight
    {polynomialTerm outerTerm : ℝ}
    (hpoly : polynomialTerm ≤ Real.exp
      (-(4 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))))
    (houter : outerTerm < Real.exp
      (-(13 / 4 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    polynomialTerm + outerTerm < Real.exp
      (-(3 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hH : (26 / 3 : ℝ) < H := by
    simpa only [H] using P.twentySix_thirds_lt_sourceHeightUnit
  have hpoly' : polynomialTerm ≤ Real.exp (-(13 / 4 : ℝ) * H) := by
    refine hpoly.trans (Real.exp_le_exp.mpr ?_)
    linarith
  have houter' : outerTerm ≤ Real.exp (-(13 / 4 : ℝ) * H) :=
    houter.le
  have hlog : Real.log 2 < (13 / 4 : ℝ) * H - 3 * H := by
    have : Real.log 2 < 1 := by nlinarith [Real.log_two_lt_d9]
    linarith
  exact add_lt_exp_neg_of_le_exp_neg
    (by simpa only [neg_mul] using hpoly')
    (by simpa only [neg_mul] using houter') hlog

end Erdos240.VDPLParameters

#print axioms Erdos240.VDPLParameters.coprime_fullHermiteFactor_le
#print axioms Erdos240.VDPLParameters.coprime_fullHermiteFactor_le_exp_sixth
#print axioms Erdos240.VDPLParameters.eight_mul_sourceHeight_le_sourceExponent_of_structural
#print axioms Erdos240.VDPLParameters.exp_neg_half_sourceExponent_le_exp_neg_four_sourceHeight
#print axioms Erdos240.VDPLParameters.four_thirds_mul_growth_mul_coprime_decay_lt_exp_neg_thirteen_quarters
#print axioms Erdos240.VDPLParameters.four_thirds_mul_seven_thirds_growth_mul_coprime_decay_lt_exp_neg_thirtyFive_twelfths
#print axioms Erdos240.VDPLParameters.polynomial_add_outer_lt_exp_neg_five_halves_sourceHeight
#print axioms Erdos240.VDPLParameters.polynomial_add_outer_lt_exp_neg_three_sourceHeight
