/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma3Concrete

/-!
# Canonical numerical conditions for the Baker source step

Given a positive source exponent, this file chooses the two multipliers in
`SourceNumericalConditions` canonically.  The growth multiplier realizes the
envelope `max 1 M.growth`, while the error multiplier realizes any prescribed
target `T` in `(0, 1]`.  Thus constructing the numerical conditions is reduced
to the single estimate that the concrete error is at most `T`.
-/

noncomputable section

namespace Erdos240.BakerSourceNumericalConditions

open BakerLemma3
open BakerLemma3Concrete

variable
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*}
    {P : VDPLParameters ι} {coord : SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)}

/-- The canonical multiplier whose growth envelope is `max 1 M.growth`. -/
def canonicalGrowthMultiplier
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    (sourceConstant : ℝ) : ℝ :=
  Real.log (max 1 M.growth) / sourceExponent P sourceConstant

/-- The canonical multiplier whose error envelope is the target `T`. -/
def canonicalErrorMultiplier (P : VDPLParameters ι)
    (sourceConstant T : ℝ) : ℝ :=
  -Real.log T / sourceExponent P sourceConstant

/-- Positivity of the source exponent forces positivity of its constant. -/
theorem sourceConstant_pos_of_sourceExponent_pos {sourceConstant : ℝ}
    (hsource : 0 < sourceExponent P sourceConstant) :
    0 < sourceConstant := by
  have hfactor :
      0 < P.OmegaOld * Real.log P.newHeight * Real.log (P.Bsrc : ℝ) :=
    mul_pos (mul_pos P.OmegaOld_pos P.log_newHeight_pos) (log_Bsrc_pos P)
  rw [sourceExponent, show
    sourceConstant * P.OmegaOld * Real.log P.newHeight *
        Real.log (P.Bsrc : ℝ) =
      sourceConstant *
        (P.OmegaOld * Real.log P.newHeight * Real.log (P.Bsrc : ℝ)) by
      ring] at hsource
  exact pos_of_mul_pos_left hsource hfactor.le

/-- The canonical growth multiplier is nonnegative. -/
theorem canonicalGrowthMultiplier_nonneg
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    {sourceConstant : ℝ}
    (hsource : 0 < sourceExponent P sourceConstant) :
    0 ≤ canonicalGrowthMultiplier M sourceConstant := by
  exact div_nonneg
    (Real.log_nonneg (le_max_left (1 : ℝ) M.growth)) hsource.le

/-- The canonical error multiplier is nonnegative for a target at most one. -/
theorem canonicalErrorMultiplier_nonneg {sourceConstant T : ℝ}
    (hsource : 0 < sourceExponent P sourceConstant)
    (hT : 0 < T) (hT_le_one : T ≤ 1) :
    0 ≤ canonicalErrorMultiplier P sourceConstant T := by
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hT.le hT_le_one)) hsource.le

/-- The canonical choice makes the growth envelope exactly `max 1 M.growth`. -/
theorem growthEnvelope_canonical_eq
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    {sourceConstant : ℝ}
    (hsource : 0 < sourceExponent P sourceConstant) :
    growthEnvelope P sourceConstant
        (canonicalGrowthMultiplier M sourceConstant) =
      max 1 M.growth := by
  unfold growthEnvelope canonicalGrowthMultiplier
  rw [div_mul_cancel₀ _ hsource.ne', Real.exp_log]
  exact lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) M.growth)

/-- Consequently the actual growth is bounded by its canonical envelope. -/
theorem growth_le_growthEnvelope_canonical
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    {sourceConstant : ℝ}
    (hsource : 0 < sourceExponent P sourceConstant) :
    M.growth ≤ growthEnvelope P sourceConstant
      (canonicalGrowthMultiplier M sourceConstant) := by
  rw [growthEnvelope_canonical_eq M hsource]
  exact le_max_right 1 M.growth

/-- The canonical choice makes the error envelope exactly the target. -/
theorem errorEnvelope_canonical_eq {sourceConstant T : ℝ}
    (hsource : 0 < sourceExponent P sourceConstant) (hT : 0 < T) :
    errorEnvelope P sourceConstant
        (canonicalErrorMultiplier P sourceConstant T) = T := by
  unfold errorEnvelope canonicalErrorMultiplier
  have hcancel :
      -(-Real.log T / sourceExponent P sourceConstant) *
          sourceExponent P sourceConstant = Real.log T := by
    field_simp
  rw [hcancel, Real.exp_log hT]

/-- Construct source numerical conditions from a positive exponent and a
target in `(0, 1]`.  After the sign and range hypotheses, the only numerical
estimate required is `M.error (smallLinearFormBound P sourceConstant) ≤ T`. -/
def canonicalSourceNumericalConditions
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    (sourceConstant T : ℝ)
    (hsource : 0 < sourceExponent P sourceConstant)
    (hT : 0 < T) (hT_le_one : T ≤ 1)
    (herror : M.error (smallLinearFormBound P sourceConstant) ≤ T) :
    SourceNumericalConditions M where
  sourceConstant := sourceConstant
  growthMultiplier := canonicalGrowthMultiplier M sourceConstant
  errorMultiplier := canonicalErrorMultiplier P sourceConstant T
  sourceConstant_nonneg :=
    (sourceConstant_pos_of_sourceExponent_pos hsource).le
  growthMultiplier_nonneg := canonicalGrowthMultiplier_nonneg M hsource
  errorMultiplier_nonneg :=
    canonicalErrorMultiplier_nonneg hsource hT hT_le_one
  growth_le := growth_le_growthEnvelope_canonical M hsource
  error_le := herror.trans_eq (errorEnvelope_canonical_eq hsource hT).symm

/-! ## Fixed quarter multipliers -/

/-- The growth envelope with multiplier `1 / 4` has the expected exponent. -/
theorem growthEnvelope_quarter_eq (sourceConstant : ℝ) :
    growthEnvelope P sourceConstant (1 / 4 : ℝ) =
      Real.exp (sourceExponent P sourceConstant / 4) := by
  unfold growthEnvelope
  congr 1
  ring

/-- The error envelope with multiplier `1 / 4` has the expected exponent. -/
theorem errorEnvelope_quarter_eq (sourceConstant : ℝ) :
    errorEnvelope P sourceConstant (1 / 4 : ℝ) =
      Real.exp (-sourceExponent P sourceConstant / 4) := by
  unfold errorEnvelope
  congr 1
  ring

/-- A quarter-scale exponential growth bound is exactly the growth field
required by `SourceNumericalConditions` with multiplier `1 / 4`. -/
theorem growth_le_growthEnvelope_quarter
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    (sourceConstant : ℝ)
    (hgrowth : M.growth ≤ Real.exp (sourceExponent P sourceConstant / 4)) :
    M.growth ≤ growthEnvelope P sourceConstant (1 / 4 : ℝ) := by
  rw [growthEnvelope_quarter_eq]
  exact hgrowth

/-- Quarter-scale growth and amplification estimates force the concrete
comparison error below the quarter-scale error envelope once the source
exponent is at least four. -/
theorem error_le_errorEnvelope_quarter
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    (sourceConstant : ℝ)
    (hsource : 4 ≤ sourceExponent P sourceConstant)
    (hgrowth : M.growth ≤ Real.exp (sourceExponent P sourceConstant / 4))
    (hamplification : M.amplificationMajorant ≤
      Real.exp (sourceExponent P sourceConstant / 4)) :
    M.error (smallLinearFormBound P sourceConstant) ≤
      errorEnvelope P sourceConstant (1 / 4 : ℝ) := by
  rw [errorEnvelope_quarter_eq]
  unfold SourceMajorants.error smallLinearFormBound
  let E := sourceExponent P sourceConstant
  let A := M.amplificationMajorant
  let U := A * Real.exp (-E)
  change M.growth * (Real.exp U * U) ≤ Real.exp (-E / 4)
  have hE_nonneg : 0 ≤ E := by
    dsimp only [E]
    linarith
  have hU_nonneg : 0 ≤ U := by
    dsimp only [U, A]
    exact mul_nonneg M.amplificationMajorant_nonneg (Real.exp_pos _).le
  have hU : U ≤ Real.exp (-3 * E / 4) := by
    dsimp only [U, A]
    calc
      M.amplificationMajorant * Real.exp (-E) ≤
          Real.exp (E / 4) * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right hamplification (Real.exp_pos _).le
      _ = Real.exp (-3 * E / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hU_le_one : U ≤ 1 := by
    refine hU.trans ?_
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexpU : Real.exp U ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hU_le_one
  have hinner :
      Real.exp U * U ≤ Real.exp 1 * Real.exp (-3 * E / 4) :=
    mul_le_mul hexpU hU hU_nonneg (Real.exp_pos _).le
  calc
    M.growth * (Real.exp U * U) ≤
        Real.exp (E / 4) *
          (Real.exp 1 * Real.exp (-3 * E / 4)) :=
      mul_le_mul hgrowth hinner
        (mul_nonneg (Real.exp_pos _).le hU_nonneg)
        (Real.exp_pos _).le
    _ = Real.exp (1 - E / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-E / 4) := by
      apply Real.exp_le_exp.mpr
      dsimp only [E] at hsource ⊢
      linarith

/-- A source-shaped constructor with the fixed multipliers `1 / 4`.  It
packages the standard estimate in which both growth and amplification use a
quarter of a source exponent of size at least four. -/
def fixedQuarterSourceNumericalConditions
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    (sourceConstant : ℝ)
    (hsource : 4 ≤ sourceExponent P sourceConstant)
    (hgrowth : M.growth ≤ Real.exp (sourceExponent P sourceConstant / 4))
    (hamplification : M.amplificationMajorant ≤
      Real.exp (sourceExponent P sourceConstant / 4)) :
    SourceNumericalConditions M where
  sourceConstant := sourceConstant
  growthMultiplier := 1 / 4
  errorMultiplier := 1 / 4
  sourceConstant_nonneg := by
    exact (sourceConstant_pos_of_sourceExponent_pos (P := P) (by
      linarith)).le
  growthMultiplier_nonneg := by norm_num
  errorMultiplier_nonneg := by norm_num
  growth_le := growth_le_growthEnvelope_quarter M sourceConstant hgrowth
  error_le := error_le_errorEnvelope_quarter M sourceConstant hsource
    hgrowth hamplification

#print axioms growthEnvelope_canonical_eq
#print axioms errorEnvelope_canonical_eq
#print axioms canonicalSourceNumericalConditions
#print axioms error_le_errorEnvelope_quarter
#print axioms fixedQuarterSourceNumericalConditions

end Erdos240.BakerSourceNumericalConditions
