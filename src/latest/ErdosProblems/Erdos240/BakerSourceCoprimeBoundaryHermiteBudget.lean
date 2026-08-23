/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerCoprimeCompletionNumerics

/-!
# Hermite loss on the p. 52 boundary circle

The factorial comparison for a complex point on `|z| = 4R` is slightly
more expensive than the comparison at a missing integral node.  This file
reserves a factor `2^(10R)` for that comparison and proves that the complete
three-sum Hermite loss is still absorbed by the source exponent.
-/

noncomputable section

namespace Erdos240.VDPLParameters

open BakerCoprimeInterpolation
open BakerCoprimeFactorialCancellation
open BakerLemma3Concrete
open BakerSourceOversizedConstantNumerics

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  (P : VDPLParameters (Fin oldRank))

/-- Three successor radii fit inside the source Lemma-5 local radius. -/
theorem three_mul_R_succ_le_lemmaFiveLocalRadius (J : ℕ) :
    3 * P.R (J + 1) ≤ P.lemmaFiveLocalRadius J := by
  unfold lemmaFiveLocalRadius
  apply Nat.le_floor
  have hroot : (39 : ℝ) ≤ P.k ^ (1 / 2 : ℝ) :=
    (by norm_num : (39 : ℝ) ≤ 128).trans P.oneTwentyEight_le_k_rpow_half
  have hfac : 0 ≤ 16 * (((P.q ^ J : ℕ) : ℝ)) * P.h := by positivity
  calc
    ((3 * P.R (J + 1) : ℕ) : ℝ) =
        (16 * (((P.q ^ J : ℕ) : ℝ)) * P.h) * 39 := by
      simp only [R, q, pow_succ]
      push_cast
      ring
    _ ≤ (16 * (((P.q ^ J : ℕ) : ℝ)) * P.h) *
        P.k ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hroot hfac
    _ = 16 * (((P.q ^ J : ℕ) : ℝ)) * P.h *
        P.k ^ (1 / 2 : ℝ) := by ring

/-- The boundary-specific power of two fits inside the already checked
source Lemma-5 Hermite reserve. -/
theorem coprime_boundary_explicitHermiteFactor_le_exp_twelfth
    {J : ℕ} (hJ : P.LevelOK J) :
    (2 : ℝ) ^ ((12 * P.R (J + 1) + 3) * (P.Sstep J / 4)) ≤
      Real.exp
        (sourceExponent P (P.C * Real.log P.OmegaOld) / 12) := by
  let R : ℕ := P.R (J + 1)
  let T : ℕ := P.Sstep J / 4
  let R₅ : ℕ := P.lemmaFiveLocalRadius J
  let T₅ : ℕ := P.lemmaFiveLocalMultiplicity J
  have hR : 12 * R ≤ 4 * R₅ := by
    have hthree := P.three_mul_R_succ_le_lemmaFiveLocalRadius J
    dsimp only [R, R₅] at hthree ⊢
    omega
  have hT : T ≤ T₅ := by
    simpa only [T, T₅] using
      P.Sstep_div_four_le_lemmaFiveLocalMultiplicity J
  have hindex : (12 * R + 3) * T ≤ (4 * R₅ + 3) * T₅ :=
    Nat.mul_le_mul (Nat.add_le_add_right hR 3) hT
  have htwo : (2 : ℝ) ^ ((12 * R + 3) * T) ≤
      (2 : ℝ) ^ ((4 * R₅ + 3) * T₅) :=
    pow_le_pow_right₀ (by norm_num) hindex
  have hqone : (1 : ℝ) ≤ (P.q : ℝ) ^ T₅ := by
    exact one_le_pow₀ (by norm_num [q] : (1 : ℝ) ≤ P.q)
  have hterminal := P.lemmaFive_explicitHermiteFactor_le_exp_twelfth hJ
  change (2 : ℝ) ^ ((12 * R + 3) * T) ≤ _
  calc
    (2 : ℝ) ^ ((12 * R + 3) * T) ≤
        (2 : ℝ) ^ ((4 * R₅ + 3) * T₅) := htwo
    _ ≤ (P.q : ℝ) ^ T₅ *
        (2 : ℝ) ^ ((4 * R₅ + 3) * T₅) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hqone (by positivity :
        0 ≤ (2 : ℝ) ^ ((4 * R₅ + 3) * T₅))
    _ ≤ Real.exp ((P.C * P.Omega * Real.log P.OmegaOld *
        Real.log (P.Bsrc : ℝ)) / 12) := by
      simpa only [R₅, T₅] using hterminal
    _ = Real.exp
        (sourceExponent P (P.C * Real.log P.OmegaOld) / 12) := by
      congr 1
      unfold sourceExponent VDPLParameters.Omega
      ring

/-- A `2^(10R)` complex-boundary product ratio, the basis loss, and all
three finite sums together cost at most `2^((12R+3)T)`. -/
theorem coprime_boundary_fullHermiteFactor_le
    {J : ℕ} (hJ : P.LevelOK J) :
    ((coprimeNodeIndices P.q (P.R (J + 1))).card : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
        ((((2 : ℝ) ^ (10 * P.R (J + 1))) ^ (P.Sstep J / 4)) *
          (2 : ℝ) ^
            ((coprimeNodeIndices P.q (P.R (J + 1))).card *
                (P.Sstep J / 4) + (P.Sstep J / 4))) ≤
      (2 : ℝ) ^
        ((12 * P.R (J + 1) + 3) * (P.Sstep J / 4)) := by
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
      c + 2 * T + ((10 * R) * T + (c * T + T)) ≤
        (12 * R + 3) * T := by
    have hRT : R ≤ R * T := Nat.le_mul_of_pos_right R hT
    have hcRT : c ≤ R * T := hcR.trans hRT
    have hcT : c * T ≤ R * T := Nat.mul_le_mul_right T hcR
    calc
      c + 2 * T + ((10 * R) * T + (c * T + T)) ≤
          R * T + 2 * T + (10 * R * T + (R * T + T)) := by omega
      _ = (12 * R + 3) * T := by ring
  change (c : ℝ) * T * T *
      ((((2 : ℝ) ^ (10 * R)) ^ T) *
        (2 : ℝ) ^ (c * T + T)) ≤
    (2 : ℝ) ^ ((12 * R + 3) * T)
  have hpow :
      (((2 : ℝ) ^ (10 * R)) ^ T) *
          (2 : ℝ) ^ (c * T + T) =
        (2 : ℝ) ^ ((10 * R) * T + (c * T + T)) := by
    rw [← pow_mul, ← pow_add]
  calc
    (c : ℝ) * T * T *
        ((((2 : ℝ) ^ (10 * R)) ^ T) *
          (2 : ℝ) ^ (c * T + T)) =
      ((c : ℝ) * T * T) *
        (2 : ℝ) ^ ((10 * R) * T + (c * T + T)) := by rw [hpow]
    _ ≤ (2 : ℝ) ^ (c + 2 * T) *
        (2 : ℝ) ^ ((10 * R) * T + (c * T + T)) := by gcongr
    _ = (2 : ℝ) ^
        (c + 2 * T + ((10 * R) * T + (c * T + T))) := by
      rw [← pow_add]
    _ ≤ (2 : ℝ) ^ ((12 * R + 3) * T) :=
      pow_le_pow_right₀ (by norm_num) hindex

/-- Final boundary-Hermite loss at an arbitrary point of the p. 52
contour.  The geometric input is precisely the separately proved
`2^(10R)` product-ratio estimate. -/
theorem coprime_boundary_fullHermiteFactor_le_exp_sixth
    {J : ℕ} (hJ : P.LevelOK J) {C₀ : ℝ}
    (hstruct : 4 * P.C ≤ C₀) :
    ((coprimeNodeIndices P.q (P.R (J + 1))).card : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
        ((((2 : ℝ) ^ (10 * P.R (J + 1))) ^ (P.Sstep J / 4)) *
          (2 : ℝ) ^
            ((coprimeNodeIndices P.q (P.R (J + 1))).card *
                (P.Sstep J / 4) + (P.Sstep J / 4))) ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 6) := by
  refine (P.coprime_boundary_fullHermiteFactor_le hJ).trans ?_
  refine (P.coprime_boundary_explicitHermiteFactor_le_exp_twelfth hJ).trans ?_
  apply Real.exp_le_exp.mpr
  have hmono := sourceExponent_mono_normalized P hstruct
  rw [sourceExponent_four_mul] at hmono
  have hEC : 0 ≤ sourceExponent P (P.C * Real.log P.OmegaOld) :=
    BakerLemma3Concrete.sourceExponent_nonneg P
      (mul_nonneg P.C_pos.le P.log_OmegaOld_pos.le)
  linarith

/-- The analytic `3H/2` boundary term and the exponentially small Hermite
polynomial fit comfortably inside the advertised `7H/3` numerator bound. -/
theorem exp_three_halves_add_exp_neg_four_le_exp_seven_thirds :
    Real.exp ((3 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) +
      Real.exp (-(4 *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) ≤
    Real.exp ((7 / 3 : ℝ) *
      ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hH : (26 / 3 : ℝ) < H := by
    simpa only [H] using P.twentySix_thirds_lt_sourceHeightUnit
  have hsmall : Real.exp (-(4 * H)) ≤ Real.exp ((3 / 2 : ℝ) * H) := by
    apply Real.exp_le_exp.mpr
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp (H / 6) := by
    calc
      (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
      _ ≤ Real.exp (H / 6) := Real.exp_le_exp.mpr (by linarith)
  change Real.exp ((3 / 2 : ℝ) * H) + Real.exp (-(4 * H)) ≤
    Real.exp ((7 / 3 : ℝ) * H)
  calc
    Real.exp ((3 / 2 : ℝ) * H) + Real.exp (-(4 * H)) ≤
        2 * Real.exp ((3 / 2 : ℝ) * H) := by linarith
    _ ≤ Real.exp (H / 6) * Real.exp ((3 / 2 : ℝ) * H) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp ((5 / 3 : ℝ) * H) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((7 / 3 : ℝ) * H) :=
      Real.exp_le_exp.mpr (by nlinarith)

end Erdos240.VDPLParameters

#print axioms Erdos240.VDPLParameters.three_mul_R_succ_le_lemmaFiveLocalRadius
#print axioms Erdos240.VDPLParameters.coprime_boundary_explicitHermiteFactor_le_exp_twelfth
#print axioms Erdos240.VDPLParameters.coprime_boundary_fullHermiteFactor_le
#print axioms Erdos240.VDPLParameters.coprime_boundary_fullHermiteFactor_le_exp_sixth
#print axioms Erdos240.VDPLParameters.exp_three_halves_add_exp_neg_four_le_exp_seven_thirds
