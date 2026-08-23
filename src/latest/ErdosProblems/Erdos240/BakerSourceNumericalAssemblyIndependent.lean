/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma3Instantiation
import ErdosProblems.Erdos240.BakerInduction
import ErdosProblems.Erdos240.BakerLemma4Concrete
import ErdosProblems.Erdos240.BakerLemma4InnerInduction
import ErdosProblems.Erdos240.BakerSourceLogFormNormalization
import ErdosProblems.Erdos240.BakerSourceNumericalConditions
import ErdosProblems.Erdos240.BakerSourceLiouvilleThresholds

/-!
# Numerical source-step adapters for the independent Baker assembly

This module starts the concrete construction of
`HasNormalizedConcreteSourceChains`.  It turns the fully instantiated
rational-point form of source Lemma 3 into the exact `lowerStep` field of
`ConcreteSourceContinuation`.  Consequently the remaining rational
interpolation work is only the strict analytic upper estimate; no algebraic
certificate, denominator, field-degree, or conjugate bound remains hidden in
the assembly interface.
-/

open scoped BigOperators NumberField Polynomial

noncomputable section

namespace Erdos240.BakerSourceNumericalAssemblyIndependent

open BakerInduction
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerLemma4Concrete
open BakerLemma4InnerInduction
open BakerSourceState
open BakerSourceLogFormNormalization
open BakerSourceNumericalConditions
open BakerSourceLiouvilleThresholds

/-! ## Canonical numerical conditions on the bounded source grids -/

@[simp] theorem lemmaFourCertificateLower_stateIntegralTargetCertificate
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (m : VDPLMultiIndex P.rank) :
    lemmaFourCertificateLower
        (stateIntegralTargetCertificate P state b bLast l
          (toSourceMultiIndex P m)) =
      stateIntegralLiouvilleThreshold P J (toSourceMultiIndex P m) := by
  rfl

@[simp] theorem lemmaFourCertificateLower_stateRationalTargetCertificate
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (m : VDPLMultiIndex P.rank) :
    lemmaFourCertificateLower
        (stateRationalTargetCertificate P state b bLast l
          (toSourceMultiIndex P m)) =
      stateRationalLiouvilleThreshold P J state b bLast l
        (toSourceMultiIndex P m) := by
  rfl

/-- Positivity of the normalized source exponent.  The old family is
nonempty in every induction application, so `log OmegaOld` is positive. -/
theorem normalizedSourceExponent_pos {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < sourceExponent P (C₀ * Real.log P.OmegaOld) := by
  unfold sourceExponent
  exact mul_pos
    (mul_pos
      (mul_pos (mul_pos hC₀ P.log_OmegaOld_pos) P.OmegaOld_pos)
        P.log_newHeight_pos)
    (log_Bsrc_pos P)

/-- For the source's actual choice `C₀ = P.C`, the normalized exponent is
already at least four.  This is the precise threshold used by the
fixed-quarter numerical conditions. -/
theorem four_le_normalizedSourceExponent {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    4 ≤ sourceExponent P (P.C * Real.log P.OmegaOld) := by
  have hbase : (2 : ℝ) ≤ P.kSeedBase := by
    unfold VDPLParameters.kSeedBase
    have hrank : (0 : ℝ) ≤ P.rank := by positivity
    nlinarith
  have hseed : (2 : ℝ) ≤ P.kSeed := by
    exact hbase.trans
      (le_self_pow₀ P.one_le_kSeedBase P.kExponent_pos.ne')
  have hk : (2 : ℝ) ≤ P.k :=
    hseed.trans P.kSeed_lt_k.le
  have hC : (4 : ℝ) ≤ P.C := by
    have hpow : (2 : ℝ) ^ 2 ≤ P.k ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hk 2
    rw [VDPLParameters.C, P.mu_eq]
    norm_num [Real.rpow_two]
    norm_num at hpow
    exact hpow
  have hlogOmega : (1 / 2 : ℝ) ≤ Real.log P.OmegaOld := by
    exact (by
      nlinarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
        P.log_two_le_log_OmegaOld
  have hCLog : (4 : ℝ) * (1 / 2) ≤
      P.C * Real.log P.OmegaOld := by
    exact mul_le_mul hC hlogOmega (by norm_num) (by positivity)
  have hCLogOmega : (4 : ℝ) * (1 / 2) * 1 ≤
      (P.C * Real.log P.OmegaOld) * P.OmegaOld := by
    exact mul_le_mul hCLog P.one_le_OmegaOld (by norm_num)
      (by positivity)
  have hCLogOmegaHeight : (4 : ℝ) * (1 / 2) * 1 * 1 ≤
      (P.C * Real.log P.OmegaOld) * P.OmegaOld *
        Real.log P.newHeight := by
    exact mul_le_mul hCLogOmega P.one_le_log_newHeight (by norm_num)
      (by positivity)
  have hfull : (4 : ℝ) * (1 / 2) * 1 * 1 * 2 ≤
      (P.C * Real.log P.OmegaOld) * P.OmegaOld *
        Real.log P.newHeight * Real.log (P.Bsrc : ℝ) := by
    exact mul_le_mul hCLogOmegaHeight P.two_le_log_Bsrc (by norm_num)
      (by positivity)
  unfold sourceExponent
  calc
    (4 : ℝ) = (4 * (1 / 2)) * 1 * 1 * 2 := by norm_num
    _ ≤ (P.C * Real.log P.OmegaOld) * P.OmegaOld *
        Real.log P.newHeight * Real.log (P.Bsrc : ℝ) := hfull

/-- Canonical numerical conditions at an integral source target.  Growth
and the two multipliers are synthesized; the only remaining real estimate
is the direct comparison error against the explicit degree-one Liouville
threshold. -/
def integralNumericalConditionsOfError {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (l : ℕ) (m : VDPLMultiIndex P.rank)
    (herror :
      (stateSourceMajorants P state b bLast (l : ℂ)
        (toSourceMultiIndex P m)).error
          (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
        stateIntegralLiouvilleThreshold P J (toSourceMultiIndex P m)) :
    SourceNumericalConditions
      (stateSourceMajorants P state b bLast (l : ℂ)
        (toSourceMultiIndex P m)) :=
  canonicalSourceNumericalConditions
    (stateSourceMajorants P state b bLast (l : ℂ)
      (toSourceMultiIndex P m))
    (C₀ * Real.log P.OmegaOld)
    (stateIntegralLiouvilleThreshold P J (toSourceMultiIndex P m))
    (normalizedSourceExponent_pos P hC₀)
    (stateIntegralLiouvilleThreshold_pos P J (toSourceMultiIndex P m))
    (stateIntegralLiouvilleThreshold_le_one P J (toSourceMultiIndex P m))
    herror

@[simp] theorem integralNumericalConditionsOfError_sourceConstant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (l : ℕ) (m : VDPLMultiIndex P.rank) (herror) :
    (integralNumericalConditionsOfError P state b bLast C₀ hC₀ l m
      herror).sourceConstant = C₀ * Real.log P.OmegaOld := rfl

@[simp] theorem integralNumericalConditionsOfError_errorEnvelope
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (l : ℕ) (m : VDPLMultiIndex P.rank) (herror) :
    errorEnvelope P
        (integralNumericalConditionsOfError P state b bLast C₀ hC₀ l m
          herror).sourceConstant
        (integralNumericalConditionsOfError P state b bLast C₀ hC₀ l m
          herror).errorMultiplier =
      stateIntegralLiouvilleThreshold P J (toSourceMultiIndex P m) := by
  exact errorEnvelope_canonical_eq (normalizedSourceExponent_pos P hC₀)
    (stateIntegralLiouvilleThreshold_pos P J (toSourceMultiIndex P m))

/-- Canonical numerical conditions at a rational source target `l/q`. -/
def rationalNumericalConditionsOfError {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (l : ℕ) (m : VDPLMultiIndex P.rank)
    (herror :
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
        (toSourceMultiIndex P m)).error
          (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
        stateRationalLiouvilleThreshold P J state b bLast l
          (toSourceMultiIndex P m)) :
    SourceNumericalConditions
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
        (toSourceMultiIndex P m)) :=
  canonicalSourceNumericalConditions
    (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
      (toSourceMultiIndex P m))
    (C₀ * Real.log P.OmegaOld)
    (stateRationalLiouvilleThreshold P J state b bLast l
      (toSourceMultiIndex P m))
    (normalizedSourceExponent_pos P hC₀)
    (stateRationalLiouvilleThreshold_pos P J state b bLast l
      (toSourceMultiIndex P m))
    (stateRationalLiouvilleThreshold_le_one P J state b bLast l
      (toSourceMultiIndex P m))
    herror

@[simp] theorem rationalNumericalConditionsOfError_sourceConstant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (l : ℕ) (m : VDPLMultiIndex P.rank) (herror) :
    (rationalNumericalConditionsOfError P state b bLast C₀ hC₀ l m
      herror).sourceConstant = C₀ * Real.log P.OmegaOld := rfl

@[simp] theorem rationalNumericalConditionsOfError_errorEnvelope
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (l : ℕ) (m : VDPLMultiIndex P.rank) (herror) :
    errorEnvelope P
        (rationalNumericalConditionsOfError P state b bLast C₀ hC₀ l m
          herror).sourceConstant
        (rationalNumericalConditionsOfError P state b bLast C₀ hC₀ l m
          herror).errorMultiplier =
      stateRationalLiouvilleThreshold P J state b bLast l
        (toSourceMultiIndex P m) := by
  exact errorEnvelope_canonical_eq (normalizedSourceExponent_pos P hC₀)
    (stateRationalLiouvilleThreshold_pos P J state b bLast l
      (toSourceMultiIndex P m))

/-! ### State-specialized fixed-quarter constructors -/

/-- Fixed-quarter numerical conditions at an integral source target.  The
constant is the common normalized source constant and both multipliers are
definitionally `1 / 4`; only the literal growth and amplification estimates
remain. -/
def integralFixedQuarterNumericalConditions {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (C₀ : ℝ)
    (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource :
      4 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hgrowth :
      (stateSourceMajorants P state b bLast (l : ℂ)
          (toSourceMultiIndex P m)).growth ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (hamplification :
      (stateSourceMajorants P state b bLast (l : ℂ)
          (toSourceMultiIndex P m)).amplificationMajorant ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 4)) :
    SourceNumericalConditions
      (stateSourceMajorants P state b bLast (l : ℂ)
        (toSourceMultiIndex P m)) :=
  fixedQuarterSourceNumericalConditions
    (stateSourceMajorants P state b bLast (l : ℂ)
      (toSourceMultiIndex P m))
    (C₀ * Real.log P.OmegaOld) hsource hgrowth hamplification

/-- Fixed-quarter numerical conditions at a rational source target. -/
def rationalFixedQuarterNumericalConditions {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (C₀ : ℝ)
    (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource :
      4 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hgrowth :
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).growth ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (hamplification :
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).amplificationMajorant ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 4)) :
    SourceNumericalConditions
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
        (toSourceMultiIndex P m)) :=
  fixedQuarterSourceNumericalConditions
    (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
      (toSourceMultiIndex P m))
    (C₀ * Real.log P.OmegaOld) hsource hgrowth hamplification

@[simp] theorem integralFixedQuarterNumericalConditions_sourceConstant
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ) (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource hgrowth hamplification) :
    (integralFixedQuarterNumericalConditions P state b bLast C₀ l m
      hsource hgrowth hamplification).sourceConstant =
        C₀ * Real.log P.OmegaOld := rfl

@[simp] theorem rationalFixedQuarterNumericalConditions_sourceConstant
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ) (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource hgrowth hamplification) :
    (rationalFixedQuarterNumericalConditions P state b bLast C₀ l m
      hsource hgrowth hamplification).sourceConstant =
        C₀ * Real.log P.OmegaOld := rfl

@[simp] theorem integralFixedQuarterNumericalConditions_growthMultiplier
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ) (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource hgrowth hamplification) :
    (integralFixedQuarterNumericalConditions P state b bLast C₀ l m
      hsource hgrowth hamplification).growthMultiplier = (1 / 4 : ℝ) := rfl

@[simp] theorem integralFixedQuarterNumericalConditions_errorMultiplier
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ) (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource hgrowth hamplification) :
    (integralFixedQuarterNumericalConditions P state b bLast C₀ l m
      hsource hgrowth hamplification).errorMultiplier = (1 / 4 : ℝ) := rfl

@[simp] theorem rationalFixedQuarterNumericalConditions_growthMultiplier
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ) (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource hgrowth hamplification) :
    (rationalFixedQuarterNumericalConditions P state b bLast C₀ l m
      hsource hgrowth hamplification).growthMultiplier = (1 / 4 : ℝ) := rfl

@[simp] theorem rationalFixedQuarterNumericalConditions_errorMultiplier
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ) (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource hgrowth hamplification) :
    (rationalFixedQuarterNumericalConditions P state b bLast C₀ l m
      hsource hgrowth hamplification).errorMultiplier = (1 / 4 : ℝ) := rfl

@[simp] theorem integralFixedQuarterNumericalConditions_errorEnvelope
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ) (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource hgrowth hamplification) :
    errorEnvelope P
        (integralFixedQuarterNumericalConditions P state b bLast C₀ l m
          hsource hgrowth hamplification).sourceConstant
        (integralFixedQuarterNumericalConditions P state b bLast C₀ l m
          hsource hgrowth hamplification).errorMultiplier =
      Real.exp
        (-sourceExponent P (C₀ * Real.log P.OmegaOld) / 4) := by
  rw [integralFixedQuarterNumericalConditions_sourceConstant,
    integralFixedQuarterNumericalConditions_errorMultiplier,
    errorEnvelope_quarter_eq]

@[simp] theorem rationalFixedQuarterNumericalConditions_errorEnvelope
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ) (l : ℕ) (m : VDPLMultiIndex P.rank)
    (hsource hgrowth hamplification) :
    errorEnvelope P
        (rationalFixedQuarterNumericalConditions P state b bLast C₀ l m
          hsource hgrowth hamplification).sourceConstant
        (rationalFixedQuarterNumericalConditions P state b bLast C₀ l m
          hsource hgrowth hamplification).errorMultiplier =
      Real.exp
        (-sourceExponent P (C₀ * Real.log P.OmegaOld) / 4) := by
  rw [rationalFixedQuarterNumericalConditions_sourceConstant,
    rationalFixedQuarterNumericalConditions_errorMultiplier,
    errorEnvelope_quarter_eq]

/-- The integral fixed-quarter constructor with the literal source constant
`P.C * log P.OmegaOld`; its exponent threshold is automatic. -/
def integralSourceQuarterNumericalConditions {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex P.rank)
    (hgrowth :
      (stateSourceMajorants P state b bLast (l : ℂ)
          (toSourceMultiIndex P m)).growth ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification :
      (stateSourceMajorants P state b bLast (l : ℂ)
          (toSourceMultiIndex P m)).amplificationMajorant ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4)) :
    SourceNumericalConditions
      (stateSourceMajorants P state b bLast (l : ℂ)
        (toSourceMultiIndex P m)) :=
  integralFixedQuarterNumericalConditions P state b bLast P.C l m
    (four_le_normalizedSourceExponent P) hgrowth hamplification

/-- The rational fixed-quarter constructor with the literal source constant
`P.C * log P.OmegaOld`; its exponent threshold is automatic. -/
def rationalSourceQuarterNumericalConditions {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex P.rank)
    (hgrowth :
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).growth ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification :
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).amplificationMajorant ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4)) :
    SourceNumericalConditions
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
        (toSourceMultiIndex P m)) :=
  rationalFixedQuarterNumericalConditions P state b bLast P.C l m
    (four_le_normalizedSourceExponent P) hgrowth hamplification

@[simp] theorem integralSourceQuarterNumericalConditions_sourceConstant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex P.rank) (hgrowth hamplification) :
    (integralSourceQuarterNumericalConditions P state b bLast l m hgrowth
      hamplification).sourceConstant = P.C * Real.log P.OmegaOld := rfl

@[simp] theorem rationalSourceQuarterNumericalConditions_sourceConstant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex P.rank) (hgrowth hamplification) :
    (rationalSourceQuarterNumericalConditions P state b bLast l m hgrowth
      hamplification).sourceConstant = P.C * Real.log P.OmegaOld := rfl

@[simp] theorem integralSourceQuarterNumericalConditions_errorMultiplier
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex P.rank) (hgrowth hamplification) :
    (integralSourceQuarterNumericalConditions P state b bLast l m hgrowth
      hamplification).errorMultiplier = (1 / 4 : ℝ) := rfl

@[simp] theorem rationalSourceQuarterNumericalConditions_errorMultiplier
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex P.rank) (hgrowth hamplification) :
    (rationalSourceQuarterNumericalConditions P state b bLast l m hgrowth
      hamplification).errorMultiplier = (1 / 4 : ℝ) := rfl

@[simp] theorem integralSourceQuarterNumericalConditions_errorEnvelope
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex P.rank) (hgrowth hamplification) :
    errorEnvelope P
        (integralSourceQuarterNumericalConditions P state b bLast l m hgrowth
          hamplification).sourceConstant
        (integralSourceQuarterNumericalConditions P state b bLast l m hgrowth
          hamplification).errorMultiplier =
      Real.exp
        (-sourceExponent P (P.C * Real.log P.OmegaOld) / 4) := by
  rw [integralSourceQuarterNumericalConditions_sourceConstant,
    integralSourceQuarterNumericalConditions_errorMultiplier,
    errorEnvelope_quarter_eq]

@[simp] theorem rationalSourceQuarterNumericalConditions_errorEnvelope
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex P.rank) (hgrowth hamplification) :
    errorEnvelope P
        (rationalSourceQuarterNumericalConditions P state b bLast l m hgrowth
          hamplification).sourceConstant
        (rationalSourceQuarterNumericalConditions P state b bLast l m hgrowth
          hamplification).errorMultiplier =
      Real.exp
        (-sourceExponent P (P.C * Real.log P.OmegaOld) / 4) := by
  rw [rationalSourceQuarterNumericalConditions_sourceConstant,
    rationalSourceQuarterNumericalConditions_errorMultiplier,
    errorEnvelope_quarter_eq]

/-- The exact numerical inputs still needed by the fully instantiated
rational-point Lemma 3 for one active coefficient state. -/
structure RationalLowerInputs {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) where
  numerical : ∀ (l : ℕ) (_hl : 1 ≤ l) (_hlR : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex P.rank) (_hm : VDPLMultiIndex.weight m ≤ P.Sstep J),
    SourceNumericalConditions
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
        (toSourceMultiIndex P m))
  last_ne_zero : bLast ≠ 0
  smallForm : ∀ (l : ℕ) (hl : 1 ≤ l) (hlR : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex P.rank) (hm : VDPLMultiIndex.weight m ≤ P.Sstep J),
    ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤
      smallLinearFormBound P (numerical l hl hlR m hm).sourceConstant
  error_le_liouville : ∀ (l : ℕ) (hl : 1 ≤ l)
    (hlR : l ≤ P.R (J + 1)) (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J),
    errorEnvelope P (numerical l hl hlR m hm).sourceConstant
        (numerical l hl hlR m hm).errorMultiplier ≤
      stateRationalLiouvilleThreshold P J state b bLast l
        (toSourceMultiIndex P m)

namespace RationalLowerInputs

variable {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
  {state : LevelState P J} {b : Fin oldRank → ℤ} {bLast : ℤ}

/-- Build every bounded rational-grid numerical condition with the fixed
source multipliers `1 / 4`.  The remaining hypotheses are precisely the
growth and amplification estimates and the comparison of the resulting
exact envelope `exp (-sourceExponent / 4)` with the rational Liouville
threshold. -/
def ofNormalizedFixedQuarter [Nonempty (Fin oldRank)]
    (C₀ : ℝ)
    (hsource : 4 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hbLast : bLast ≠ 0)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hgrowth : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).growth ≤
          Real.exp
            (sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).amplificationMajorant ≤
          Real.exp
            (sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (henvelope : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        Real.exp
            (-sourceExponent P (C₀ * Real.log P.OmegaOld) / 4) ≤
          stateRationalLiouvilleThreshold P J state b bLast l
            (toSourceMultiIndex P m)) :
    RationalLowerInputs P state b bLast where
  numerical := fun l hl hlR m hm ↦
    rationalFixedQuarterNumericalConditions P state b bLast C₀ l m
      hsource (hgrowth l hl hlR m hm) (hamplification l hl hlR m hm)
  last_ne_zero := hbLast
  smallForm := by
    intro l hl hlR m hm
    rw [rationalFixedQuarterNumericalConditions_sourceConstant]
    exact norm_logForm_le_smallLinearFormBound_of_normalized
      P C₀ b bLast hsmall
  error_le_liouville := by
    intro l hl hlR m hm
    rw [rationalFixedQuarterNumericalConditions_errorEnvelope]
    exact henvelope l hl hlR m hm

/-- Literal-source specialization of `ofNormalizedFixedQuarter`: the common
constant is `P.C * log P.OmegaOld`, and the four-unit exponent threshold is
discharged from the parameter package. -/
def ofNormalizedSourceQuarter [Nonempty (Fin oldRank)]
    (hbLast : bLast ≠ 0)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm P.old P.newPrime b bLast| <
        Real.exp (-(P.C * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hgrowth : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).growth ≤
          Real.exp
            (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).amplificationMajorant ≤
          Real.exp
            (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (henvelope : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        Real.exp
            (-sourceExponent P (P.C * Real.log P.OmegaOld) / 4) ≤
          stateRationalLiouvilleThreshold P J state b bLast l
            (toSourceMultiIndex P m)) :
    RationalLowerInputs P state b bLast :=
  ofNormalizedFixedQuarter P.C (four_le_normalizedSourceExponent P)
    hbLast hsmall hgrowth hamplification henvelope

/-- The bounded rational-grid inputs obtained from one direct error estimate
at each relevant target.  The common source constant is definitionally
`C₀ * log OmegaOld`, and the canonical error envelope is exactly the
Liouville threshold, so neither multiplier nor a second comparison proof
remains in this interface. -/
def ofNormalizedDirectError [Nonempty (Fin oldRank)]
    (C₀ : ℝ) (hC₀ : 0 < C₀) (hbLast : bLast ≠ 0)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hdirect : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).error
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
          stateRationalLiouvilleThreshold P J state b bLast l
            (toSourceMultiIndex P m)) :
    RationalLowerInputs P state b bLast where
  numerical := fun l hl hlR m hm ↦
    rationalNumericalConditionsOfError P state b bLast C₀ hC₀ l m
      (hdirect l hl hlR m hm)
  last_ne_zero := hbLast
  smallForm := by
    intro l hl hlR m hm
    rw [rationalNumericalConditionsOfError_sourceConstant]
    exact norm_logForm_le_smallLinearFormBound_of_normalized
      P C₀ b bLast hsmall
  error_le_liouville := by
    intro l hl hlR m hm
    rw [rationalNumericalConditionsOfError_errorEnvelope]

/-- Literal-source specialization of the direct-error constructor. -/
def ofNormalizedSourceDirectError [Nonempty (Fin oldRank)]
    (hbLast : bLast ≠ 0)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm P.old P.newPrime b bLast| <
        Real.exp (-(P.C * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hdirect : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).error
            (smallLinearFormBound P (P.C * Real.log P.OmegaOld)) ≤
          stateRationalLiouvilleThreshold P J state b bLast l
            (toSourceMultiIndex P m)) :
    RationalLowerInputs P state b bLast :=
  ofNormalizedDirectError P.C P.C_pos hbLast hsmall hdirect

/-- Build the rational lower-step inputs directly from the normalized
strict-smallness hypothesis.  The only substantive numerical obligations
left are the concrete `SourceNumericalConditions`, their common source
constant, and the explicit error-to-Liouville comparisons. -/
def ofNormalized (C₀ : ℝ)
    (numerical : ∀ (l : ℕ) (_hl : 1 ≤ l) (_hlR : l ≤ P.R (J + 1))
      (m : VDPLMultiIndex P.rank) (_hm : VDPLMultiIndex.weight m ≤ P.Sstep J),
      SourceNumericalConditions
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)))
    (sourceConstant_eq : ∀ l hl hlR m hm,
      (numerical l hl hlR m hm).sourceConstant = C₀ * Real.log P.OmegaOld)
    (hbLast : bLast ≠ 0)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (herror : ∀ l hl hlR m hm,
      errorEnvelope P (numerical l hl hlR m hm).sourceConstant
          (numerical l hl hlR m hm).errorMultiplier ≤
        stateRationalLiouvilleThreshold P J state b bLast l
          (toSourceMultiIndex P m)) :
    RationalLowerInputs P state b bLast where
  numerical := numerical
  last_ne_zero := hbLast
  smallForm := by
    intro l hl hlR m hm
    rw [sourceConstant_eq l hl hlR m hm]
    exact norm_logForm_le_smallLinearFormBound_of_normalized
      P C₀ b bLast hsmall
  error_le_liouville := herror

/-- The literal Liouville lower threshold used by the assembly. -/
def lower (_data : RationalLowerInputs P state b bLast) :
    ℕ → VDPLMultiIndex P.rank → ℝ := fun (l : ℕ) m ↦
  stateRationalLiouvilleThreshold P J state b bLast l
    (toSourceMultiIndex P m)

/-- The fully instantiated rational Lemma 3 supplies the exact lower
alternative required by source Lemma 5. -/
theorem lowerStep (data : RationalLowerInputs P state b bLast) :
    RationalLiouvilleAlternativeAtLevel P (f state b bLast)
      (g state b bLast) data.lower J := by
  intro l hl hlR m hm
  have hlemma := quantitative_lemma3_state_rational P state b bLast l
    (toSourceMultiIndex P m) (data.numerical l hl hlR m hm) data.last_ne_zero
    (data.smallForm l hl hlR m hm) (data.error_le_liouville l hl hlR m hm)
  change vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
      (oldLog P) (lastLog P) P.q J ((l : ℂ) / (P.q : ℂ))
        (toSourceMultiIndex P m) = 0 ∨
    data.lower l m ≤
      ‖vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) P.q J ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)‖
  simpa only [lower] using hlemma.2.2

end RationalLowerInputs

/-! ## Integral Lemma-4 inner iteration -/

/-- The exact per-stage analytic input to source Lemma 4.

The source performs `3 * (rank + 1)` integral extrapolation steps at each
outer level.  Each callback is asked only for a genuine stage below that
terminal value and receives the full current rectangle
`lemmaFourRadius J t × lemmaFourBudget J t`.  In particular, this interface
does not replace the source-local factorial cancellation by the obsolete
global `sharpHasseEvaluationBound` budget.

This structure is deliberately assumption-transparent: the local-circle
analytic development must construct `innerStep` from its pointwise estimates;
the finite iteration itself is discharged below. -/
structure IntegralStepInputs {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) where
  innerStep : InnerStepCallback P (g state b bLast) J

namespace IntegralStepInputs

variable {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
  {state : LevelState P J} {b : Fin oldRank → ℤ} {bLast : ℤ}

/-- Iterate the exact source-local callbacks through all inner Lemma 4
stages, retaining the full terminal radius and derivative budget needed by
Lemma 5. -/
theorem integralStep (data : IntegralStepInputs P state b bLast) :
    IntegralSeedAtLevel P (g state b bLast) J →
      IntegralExtrapolatedAtLevel P (g state b bLast) J := by
  exact integralExtrapolatedAtLevel_of_innerStep P (g state b bLast) J
    data.innerStep

end IntegralStepInputs

end Erdos240.BakerSourceNumericalAssemblyIndependent

#print axioms Erdos240.BakerSourceNumericalAssemblyIndependent.RationalLowerInputs.lowerStep
#print axioms
  Erdos240.BakerSourceNumericalAssemblyIndependent.RationalLowerInputs.ofNormalizedFixedQuarter
#print axioms
  Erdos240.BakerSourceNumericalAssemblyIndependent.RationalLowerInputs.ofNormalizedSourceQuarter
#print axioms
  Erdos240.BakerSourceNumericalAssemblyIndependent.RationalLowerInputs.ofNormalizedSourceDirectError
#print axioms
  Erdos240.BakerSourceNumericalAssemblyIndependent.integralFixedQuarterNumericalConditions
#print axioms
  Erdos240.BakerSourceNumericalAssemblyIndependent.rationalFixedQuarterNumericalConditions
#print axioms
  Erdos240.BakerSourceNumericalAssemblyIndependent.integralSourceQuarterNumericalConditions
#print axioms
  Erdos240.BakerSourceNumericalAssemblyIndependent.rationalSourceQuarterNumericalConditions
#print axioms
  Erdos240.BakerSourceNumericalAssemblyIndependent.four_le_normalizedSourceExponent
#print axioms Erdos240.BakerSourceNumericalAssemblyIndependent.IntegralStepInputs.integralStep
