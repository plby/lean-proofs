/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceMomentCancellation
import ErdosProblems.Erdos240.BakerSourceNumericalConditions
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Oversized-constant numerical absorption for the source construction

The normalized logarithmic-form theorem is free to choose its constant after
the finite old prime family has been fixed.  This file records two reusable
ways of spending that freedom.

First, increasing the constant by a factor of four turns quarter-scale bounds
for the auxiliary-function growth and amplification into sixteenth-scale
bounds.  At exponent at least eight this makes the literal Lemma-3 comparison
error at most `exp (-3 E / 4)`.

Second, the factorial in a normalized order-`j` derivative must not be
discarded.  The elementary inequality `B^j / j! <= exp B` shows that the full
iteration of the equation-(7) row operation costs only `exp B`, uniformly in
`j`.  An explicit old-family constant then absorbs this `B` into `E / 12`.
Combining the two estimates gives the source-shaped bound
`exp (-2 E / 3)` required after equations (7)--(8).
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceOversizedConstantNumerics

open Erdos240
open BakerLemma3Concrete
open BakerLemma3Concrete.SourceMajorants
open BakerInduction
open BakerLemma3Instantiation
open BakerSourceLogFormNormalization
open BakerSourceMomentCancellation
open BakerSourceJetTransport
open BakerSourceState

/-! ## Monotonicity in the freely chosen source constant -/

theorem sourceExponent_mono_normalized {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) :
    sourceExponent P (C₁ * Real.log P.OmegaOld) ≤
      sourceExponent P (C₂ * Real.log P.OmegaOld) := by
  unfold sourceExponent
  gcongr
  · exact P.log_newHeight_pos.le
  · exact P.OmegaOld_pos.le
  · exact P.log_OmegaOld_pos.le

theorem sourceExponent_four_mul {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (C : ℝ) :
    sourceExponent P ((4 * C) * Real.log P.OmegaOld) =
      4 * sourceExponent P (C * Real.log P.OmegaOld) := by
  unfold sourceExponent
  ring

/-- A quarter-scale bound for a reference constant becomes a
sixteenth-scale bound after increasing the normalized constant by a factor
of at least four. -/
theorem exp_quarter_le_exp_sixteenth_of_four_mul_le
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {Cbase C₀ : ℝ}
    (hC : 4 * Cbase ≤ C₀) :
    Real.exp (sourceExponent P (Cbase * Real.log P.OmegaOld) / 4) ≤
      Real.exp (sourceExponent P (C₀ * Real.log P.OmegaOld) / 16) := by
  apply Real.exp_le_exp.mpr
  have hmono := sourceExponent_mono_normalized P hC
  rw [sourceExponent_four_mul] at hmono
  linarith

/-! ## A strong error estimate obtained from oversized slack -/

/-- If both the auxiliary growth and the amplification majorant use only a
sixteenth of the available source exponent, the exact comparison error uses
at most the remaining three quarters. -/
theorem error_smallLinearFormBound_le_exp_neg_three_quarters
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*}
    {P : VDPLParameters ι} {coord : BakerLemma3.SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ} {q N : ℕ} {z : ℂ}
    {m : VDPLMultiIndex (oldRank + 1)}
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    {sourceConstant : ℝ}
    (hE : 8 ≤ sourceExponent P sourceConstant)
    (hgrowth : M.growth ≤
      Real.exp (sourceExponent P sourceConstant / 16))
    (hamplification : M.amplificationMajorant ≤
      Real.exp (sourceExponent P sourceConstant / 16)) :
    M.error (smallLinearFormBound P sourceConstant) ≤
      Real.exp (-3 * sourceExponent P sourceConstant / 4) := by
  let E := sourceExponent P sourceConstant
  let A := M.amplificationMajorant
  let U := A * Real.exp (-E)
  have hE0 : 0 ≤ E := by dsimp only [E]; linarith
  have hA0 : 0 ≤ A := by
    exact M.amplificationMajorant_nonneg
  have hU0 : 0 ≤ U := by
    exact mul_nonneg hA0 (Real.exp_pos _).le
  have hU : U ≤ Real.exp (-15 * E / 16) := by
    calc
      U = A * Real.exp (-E) := rfl
      _ ≤ Real.exp (E / 16) * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right hamplification (Real.exp_pos _).le
      _ = Real.exp (-15 * E / 16) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hU_le_one : U ≤ 1 := by
    calc
      U ≤ Real.exp (-15 * E / 16) := hU
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hexpU : Real.exp U ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hU_le_one
  have hinner : Real.exp U * U ≤
      Real.exp 1 * Real.exp (-15 * E / 16) := by
    exact mul_le_mul hexpU hU hU0 (Real.exp_pos _).le
  change M.growth * (Real.exp U * U) ≤ Real.exp (-3 * E / 4)
  calc
    M.growth * (Real.exp U * U) ≤
        Real.exp (E / 16) *
          (Real.exp 1 * Real.exp (-15 * E / 16)) :=
      mul_le_mul hgrowth hinner
        (mul_nonneg (Real.exp_pos _).le hU0) (Real.exp_pos _).le
    _ = Real.exp (1 - 14 * E / 16) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-3 * E / 4) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- A convenient wrapper: bounds at a reference constant `Cbase` imply the
strong comparison-error estimate for any constant at least `4*Cbase`, once
the enlarged exponent is at least eight. -/
theorem error_le_exp_neg_three_quarters_of_oversized
    {oldRank : ℕ} [Nonempty (Fin oldRank)] {I : Type*}
    {P : VDPLParameters (Fin oldRank)}
    {coord : BakerLemma3.SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ} {q N : ℕ} {z : ℂ}
    {m : VDPLMultiIndex (oldRank + 1)}
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    {Cbase C₀ : ℝ} (hC : 4 * Cbase ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hgrowth : M.growth ≤
      Real.exp (sourceExponent P (Cbase * Real.log P.OmegaOld) / 4))
    (hamplification : M.amplificationMajorant ≤
      Real.exp (sourceExponent P (Cbase * Real.log P.OmegaOld) / 4)) :
    M.error (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
      Real.exp
        (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4) := by
  apply error_smallLinearFormBound_le_exp_neg_three_quarters M hE
  · exact hgrowth.trans (exp_quarter_le_exp_sixteenth_of_four_mul_le P hC)
  · exact hamplification.trans
      (exp_quarter_le_exp_sixteenth_of_four_mul_le P hC)

/-! ## Retaining the factorial in equation-(7) transport -/

/-- Pointwise errors bounded on the relevant weight simplex grow by at most
the uniform row mass at each iteration. -/
theorem jetErrorIterate_le_pow_of_weight {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (bLast : ℤ) (hbLast : bLast ≠ 0) (S j : ℕ)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ)
    (hE : ∀ m, 0 ≤ E m) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hbound : ∀ m, VDPLMultiIndex.weight m ≤ S → E m ≤ delta) :
    ∀ m : VDPLMultiIndex (oldRank + 1),
      VDPLMultiIndex.weight m + j ≤ S →
      jetErrorIterate P N bLast j E m ≤
        (sourceJetCoefficientBound P S) ^ j * delta := by
  induction j with
  | zero =>
      intro m hm
      simpa [jetErrorIterate] using hbound m (by omega)
  | succ j ih =>
      intro m hm
      rw [jetErrorIterate]
      have hmajorant :
          0 ≤ (sourceJetCoefficientBound P S) ^ j * delta :=
        mul_nonneg (pow_nonneg (sourceJetCoefficientBound_nonneg P S) j)
          hdelta
      calc
        jetErrorStep P N bLast (jetErrorIterate P N bLast j E) m ≤
            jetCoefficientMass P N bLast m *
              ((sourceJetCoefficientBound P S) ^ j * delta) := by
          apply jetErrorStep_le_mass_mul P N bLast _ m hmajorant
          · exact ih m (by omega)
          · intro i
            apply ih (bump m i)
            rw [weight_bump]
            omega
        _ ≤ sourceJetCoefficientBound P S *
              ((sourceJetCoefficientBound P S) ^ j * delta) := by
          apply mul_le_mul_of_nonneg_right _ hmajorant
          apply jetCoefficientMass_le_sourceJetCoefficientBound
            P N bLast hbLast S m
          omega
        _ = (sourceJetCoefficientBound P S) ^ (j + 1) * delta := by
          rw [pow_succ]
          ring

/-- The normalized iterate costs only the exponential of one row-mass
bound.  This is the factorial cancellation absent from a coarse power-only
estimate. -/
theorem jetErrorIterate_div_factorial_le_exp_mul {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (bLast : ℤ) (hbLast : bLast ≠ 0) (S j : ℕ)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ)
    (hE : ∀ m, 0 ≤ E m) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hbound : ∀ m, VDPLMultiIndex.weight m ≤ S → E m ≤ delta)
    (m : VDPLMultiIndex (oldRank + 1))
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    jetErrorIterate P N bLast j E m / ‖(j.factorial : ℂ)‖ ≤
      Real.exp (sourceJetCoefficientBound P S) * delta := by
  have hiter := jetErrorIterate_le_pow_of_weight P N bLast hbLast S j E hE
    hdelta hbound m hmj
  have hfac0 : 0 ≤ ‖(j.factorial : ℂ)‖ := norm_nonneg _
  calc
    jetErrorIterate P N bLast j E m / ‖(j.factorial : ℂ)‖ ≤
        ((sourceJetCoefficientBound P S) ^ j * delta) /
          ‖(j.factorial : ℂ)‖ :=
      div_le_div_of_nonneg_right hiter hfac0
    _ = ((sourceJetCoefficientBound P S) ^ j /
          (j.factorial : ℝ)) * delta := by
      rw [Complex.norm_natCast]
      ring
    _ ≤ Real.exp (sourceJetCoefficientBound P S) * delta := by
      apply mul_le_mul_of_nonneg_right _ hdelta
      exact Real.pow_div_factorial_le_exp
        (x := sourceJetCoefficientBound P S)
        (sourceJetCoefficientBound_nonneg P S) j

/-! ## An explicit fixed-family coefficient for jet absorption -/

/-- The old-logarithm factor in the source row operation. -/
def oldJetFactor {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) : ℝ :=
  1 + 2 * ∑ r, ‖BakerSourceState.oldLog P r‖

/-- A deliberately oversized constant which absorbs every normalized
equation-(7) row iteration at every outer level.  It depends only on `k` and
the fixed old logarithms. -/
def jetAbsorptionConstant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  12 * (P.k + 1) * oldJetFactor P

theorem oldJetFactor_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : 0 ≤ oldJetFactor P := by
  unfold oldJetFactor
  positivity

theorem one_le_normalizedCore {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) :
    1 ≤ P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld := by
  have hOmega : (2 : ℝ) ≤ P.OmegaOld := by
    exact (show (2 : ℝ) ≤ P.rank by
      exact_mod_cast P.two_le_rank).trans P.rank_le_OmegaOld
  have hlogOmega : (1 / 2 : ℝ) ≤ Real.log P.OmegaOld := by
    exact (by
      nlinarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
        P.log_two_le_log_OmegaOld
  have hfirst : (1 : ℝ) ≤ P.OmegaOld * Real.log P.OmegaOld := by
    nlinarith [mul_le_mul hOmega hlogOmega (by norm_num : 0 ≤ (1 / 2 : ℝ))
      P.OmegaOld_pos.le]
  calc
    (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (P.OmegaOld * Real.log P.OmegaOld) *
          Real.log P.newHeight :=
      mul_le_mul hfirst P.one_le_log_newHeight (by norm_num)
        (mul_nonneg P.OmegaOld_pos.le P.log_OmegaOld_pos.le)
    _ = P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld := by ring

theorem levelScale_le_k_mul_normalizedCore {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    P.levelScale N ≤
      P.k * (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) := by
  have hq : P.qInvPow N ≤ 1 := by
    have hmono := P.qInvPow_antitone (Nat.zero_le N)
    simpa [VDPLParameters.qInvPow] using hmono
  unfold VDPLParameters.levelScale VDPLParameters.Omega
  calc
    P.qInvPow N * P.k * (P.OmegaOld * Real.log P.newHeight) *
          Real.log P.OmegaOld ≤
        1 * P.k * (P.OmegaOld * Real.log P.newHeight) *
          Real.log P.OmegaOld := by
      gcongr
      · exact P.log_OmegaOld_pos.le
      · exact mul_nonneg P.OmegaOld_pos.le P.log_newHeight_pos.le
      · exact P.k_pos.le
    _ = P.k *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) := by ring

theorem Slevel_add_one_le_k_add_one_mul_normalizedCore {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    (P.Slevel N + 1 : ℝ) ≤
      (P.k + 1) *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) := by
  have hS := P.Slevel_cast_le N
  have hscale := levelScale_le_k_mul_normalizedCore P N
  have hcore := one_le_normalizedCore P
  push_cast
  calc
    (P.Slevel N : ℝ) + 1 ≤
        P.k * (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) +
          1 := by linarith
    _ ≤ P.k * (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) +
          (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) :=
      by linarith
    _ = (P.k + 1) *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) := by ring

/-- The entire equation-(7) row mass at budget `Slevel N` fits in one
twelfth of the normalized source exponent at `jetAbsorptionConstant`. -/
theorem sourceJetCoefficientBound_Slevel_le_sourceExponent_div_twelve
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    sourceJetCoefficientBound P (P.Slevel N) ≤
      sourceExponent P
        (jetAbsorptionConstant P * Real.log P.OmegaOld) / 12 := by
  have hside := Slevel_add_one_le_k_add_one_mul_normalizedCore P N
  have hfactor : oldJetFactor P =
      1 + 2 * ∑ r, ‖BakerSourceState.oldLog P r‖ := rfl
  have hmass : sourceJetCoefficientBound P (P.Slevel N) ≤
      ((P.k + 1) *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld)) *
          oldJetFactor P := by
    unfold sourceJetCoefficientBound
    rw [← hfactor]
    exact mul_le_mul_of_nonneg_right hside (oldJetFactor_nonneg P)
  calc
    sourceJetCoefficientBound P (P.Slevel N) ≤
        ((P.k + 1) *
          (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld)) *
            oldJetFactor P := hmass
    _ ≤ sourceExponent P
          (jetAbsorptionConstant P * Real.log P.OmegaOld) / 12 := by
      rw [sourceExponent_eq_normalized]
      unfold jetAbsorptionConstant
      have hlog : (1 : ℝ) ≤ Real.log P.Bsrc :=
        (show (1 : ℝ) ≤ 2 by norm_num).trans P.two_le_log_Bsrc
      have hfactor0 : 0 ≤ oldJetFactor P := oldJetFactor_nonneg P
      have hk1 : 0 ≤ P.k + 1 := by linarith [P.k_pos]
      have hprefix : 0 ≤
          12 * (P.k + 1) * oldJetFactor P * P.OmegaOld *
            Real.log P.OmegaOld * Real.log P.newHeight := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by norm_num) hk1) hfactor0)
              P.OmegaOld_pos.le)
            P.log_OmegaOld_pos.le)
          P.log_newHeight_pos.le
      calc
        ((P.k + 1) *
            (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld)) *
              oldJetFactor P =
            (12 * (P.k + 1) * oldJetFactor P * P.OmegaOld *
              Real.log P.OmegaOld * Real.log P.newHeight * 1) / 12 := by
          ring
        _ ≤ (12 * (P.k + 1) * oldJetFactor P * P.OmegaOld *
              Real.log P.OmegaOld * Real.log P.newHeight *
                Real.log P.Bsrc) / 12 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog hprefix) (by norm_num)

/-- The same absorption remains true for every larger normalized source
constant. -/
theorem sourceJetCoefficientBound_Slevel_le_oversizedExponent_div_twelve
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) {C₀ : ℝ}
    (hC : jetAbsorptionConstant P ≤ C₀) :
    sourceJetCoefficientBound P (P.Slevel N) ≤
      sourceExponent P (C₀ * Real.log P.OmegaOld) / 12 := by
  calc
    sourceJetCoefficientBound P (P.Slevel N) ≤
        sourceExponent P
          (jetAbsorptionConstant P * Real.log P.OmegaOld) / 12 :=
      sourceJetCoefficientBound_Slevel_le_sourceExponent_div_twelve P N
    _ ≤ sourceExponent P (C₀ * Real.log P.OmegaOld) / 12 := by
      gcongr
      exact sourceExponent_mono_normalized P hC

/-- Final equation-(7)--(8) numerical package.  A pointwise
`exp (-3E/4)` comparison error on the seed simplex remains at most
`exp (-2E/3)` after every allowed normalized jet iteration. -/
theorem jetErrorIterate_div_factorial_le_exp_neg_two_thirds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (bLast : ℤ) (hbLast : bLast ≠ 0) (j : ℕ)
    (Erow : VDPLMultiIndex (oldRank + 1) → ℝ)
    (hErow : ∀ m, 0 ≤ Erow m) {C₀ : ℝ}
    (hC : jetAbsorptionConstant P ≤ C₀)
    (hrow : ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel N →
      Erow m ≤ Real.exp
        (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex (oldRank + 1))
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Slevel N) :
    jetErrorIterate P N bLast j Erow m / ‖(j.factorial : ℂ)‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) := by
  let E := sourceExponent P (C₀ * Real.log P.OmegaOld)
  let delta := Real.exp (-3 * E / 4)
  have hdelta : 0 ≤ delta := (Real.exp_pos _).le
  have hiter := jetErrorIterate_div_factorial_le_exp_mul P N bLast hbLast
    (P.Slevel N) j Erow hErow hdelta (by
      intro m' hm'
      simpa only [delta, E] using hrow m' hm') m hmj
  have hmass :=
    sourceJetCoefficientBound_Slevel_le_oversizedExponent_div_twelve
      P N hC
  calc
    jetErrorIterate P N bLast j Erow m / ‖(j.factorial : ℂ)‖ ≤
        Real.exp (sourceJetCoefficientBound P (P.Slevel N)) * delta := hiter
    _ ≤ Real.exp (E / 12) * Real.exp (-3 * E / 4) := by
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmass)
        (Real.exp_pos _).le
    _ = Real.exp (-2 * E / 3) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Direct equation-(7)--(8) conclusion for an integral source seed.  Only
the elementary growth and amplification estimates at the structural
constant `P.C` remain as hypotheses; all comparison-error and iterated-jet
arithmetic is discharged here using the oversized constant. -/
theorem norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_oversized
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : IntegralSeedAtLevel P (g state b bLast) N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (l j : ℕ) (hl : 1 ≤ l) (hlR : l ≤ P.R N)
    (hgrowth : ∀ m', VDPLMultiIndex.weight m' ≤ P.Slevel N →
      (stateSourceMajorants P state b bLast (l : ℂ) m').growth ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ m', VDPLMultiIndex.weight m' ≤ P.Slevel N →
      (stateSourceMajorants P state b bLast (l : ℂ) m').amplificationMajorant ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Slevel N) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) := by
  have hbase :=
    norm_normalizedIteratedDeriv_f_le_sourceError_of_integralSeed
      state b hbLast hseed C₀ hsmall hl hlR m hmj
  refine hbase.trans ?_
  apply jetErrorIterate_div_factorial_le_exp_neg_two_thirds
    P N bLast hbLast j
    (sourceRowError P state b bLast (l : ℂ)
      (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact sourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hjet
  · intro m' hm'
    exact error_le_exp_neg_three_quarters_of_oversized
      (stateSourceMajorants P state b bLast (l : ℂ) m') hstruct hE
      (hgrowth m' hm') (hamplification m' hm')
  · simpa only [weight_toSourceMultiIndex] using hmj

end Erdos240.BakerSourceOversizedConstantNumerics

#print axioms Erdos240.BakerSourceOversizedConstantNumerics.error_smallLinearFormBound_le_exp_neg_three_quarters
#print axioms Erdos240.BakerSourceOversizedConstantNumerics.jetErrorIterate_div_factorial_le_exp_mul
#print axioms Erdos240.BakerSourceOversizedConstantNumerics.sourceJetCoefficientBound_Slevel_le_oversizedExponent_div_twelve
#print axioms Erdos240.BakerSourceOversizedConstantNumerics.jetErrorIterate_div_factorial_le_exp_neg_two_thirds
#print axioms Erdos240.BakerSourceOversizedConstantNumerics.norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_oversized
