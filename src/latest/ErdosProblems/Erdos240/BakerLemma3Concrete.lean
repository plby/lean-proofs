/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma3
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete quantitative form of van der Poorten--Loxton Lemma 3

`BakerLemma3.lean` proves the exact termwise comparison between the analytic
auxiliary function `f` and its algebraic companion `g`, and proves the
Liouville transfer once an integral certificate is available.  This file
performs the quantitative assembly needed by the extrapolation lemmas.

The hypotheses are deliberately split according to their mathematical
origins:

* `coefficient_le` is the Siegel-lemma coefficient height;
* `delta_le` is the powered-Delta size estimate (after sharp denominator
  clearing has supplied `htermIntegral` below);
* `exponential_le` is the elementary exponential-polynomial growth bound;
* `amplification_le` measures the factor multiplying the small linear form;
* `support_card_le` is the coefficient-box count.

At induction level `N`, only the powered-Delta factor is evaluated at
`z / q^N`.  The exponential is evaluated at the unscaled argument `z`, as
in the source; consequently `exponential_le` and `amplification_le` below
both use `‖z‖`.

The only facts left in `SourceNumericalConditions` are real inequalities
between the displayed majorants.  In particular, no algebraic or analytic
assertion is hidden there.  The scale used in those inequalities is exactly

`constant * OmegaOld * log(newHeight) * log(Bsrc)`.

Thus the varying height remains visible and linear.  The final theorem also
rewrites the Liouville degree as `13 ^ radicalRank`, the degree delivered by
`Kummer.finrank_adjoin_thirteenthRoots_primes_rat`.
-/

open scoped BigOperators NumberField

noncomputable section

namespace Erdos240.BakerLemma3Concrete

open Finset
open BakerLemma3

/-- The source exponent, with all dependence relevant to uniformity kept
visible.  `constant` may depend on the fixed old primes, but not on the
varying final prime. -/
def sourceExponent {ι : Type*} [Fintype ι]
    (P : VDPLParameters ι) (constant : ℝ) : ℝ :=
  constant * P.OmegaOld * Real.log P.newHeight * Real.log (P.Bsrc : ℝ)

theorem log_Bsrc_pos {ι : Type*} [Fintype ι]
    (P : VDPLParameters ι) : 0 < Real.log (P.Bsrc : ℝ) := by
  have hB : (1 : ℝ) < (P.Bsrc : ℝ) := by
    calc
      (1 : ℝ) < Real.exp 2 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      _ ≤ (P.Bsrc : ℝ) := P.Bsrc_lower
  exact Real.log_pos hB

theorem sourceExponent_nonneg {ι : Type*} [Fintype ι]
    (P : VDPLParameters ι) {constant : ℝ} (hconstant : 0 ≤ constant) :
    0 ≤ sourceExponent P constant := by
  unfold sourceExponent
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hconstant P.OmegaOld_pos.le)
      P.log_newHeight_pos.le)
    (log_Bsrc_pos P).le

/-- Termwise input for the quantitative form of Lemma 3.  The coefficient
bound is fixed to the actual source height `P.coeffHeight`; all other
majorants are named explicitly so later parameter arithmetic can discharge
them independently. -/
structure SourceMajorants
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*}
    (P : VDPLParameters ι) (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) where
  supportMajorant : ℝ
  deltaMajorant : ℝ
  exponentialMajorant : ℝ
  amplificationMajorant : ℝ
  supportMajorant_nonneg : 0 ≤ supportMajorant
  deltaMajorant_nonneg : 0 ≤ deltaMajorant
  exponentialMajorant_nonneg : 0 ≤ exponentialMajorant
  amplificationMajorant_nonneg : 0 ≤ amplificationMajorant
  support_card_le : (support.card : ℝ) ≤ supportMajorant
  coefficient_le : ∀ lambda ∈ support, ‖(p lambda : ℂ)‖ ≤ P.coeffHeight
  delta_le : ∀ lambda ∈ support,
    ‖auxiliaryFactor coord h b bLast lambda (scaledArgument q N z) m‖ ≤
      deltaMajorant
  exponential_le : ∀ lambda ∈ support,
    Real.exp
      (‖modifiedRate coord b bLast logAlpha lambda‖ *
        ‖z‖) ≤
        exponentialMajorant
  amplification_le : ∀ lambda ∈ support,
    ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ *
        ‖z‖ ≤ amplificationMajorant

namespace SourceMajorants

variable
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*}
    {P : VDPLParameters ι} {coord : SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)}

/-- The resulting global growth majorant. -/
def growth
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m) : ℝ :=
  M.supportMajorant * (P.coeffHeight * M.deltaMajorant) *
    M.exponentialMajorant

/-- The resulting global comparison error for a bound on the linear form. -/
def error
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    (linearFormBound : ℝ) : ℝ :=
  M.growth *
    (Real.exp (M.amplificationMajorant * linearFormBound) *
      (M.amplificationMajorant * linearFormBound))

theorem sourceCoefficient_le
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    {lambda : I} (hlambda : lambda ∈ support) :
    ‖sourceCoefficient coord p h b bLast q N z m lambda‖ ≤
      P.coeffHeight * M.deltaMajorant := by
  rw [sourceCoefficient, norm_mul]
  exact mul_le_mul (M.coefficient_le lambda hlambda)
    (M.delta_le lambda hlambda) (norm_nonneg _) P.coeffHeight_pos.le

theorem norm_vdplF_le_growth
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m) :
    ‖vdplF coord support p h b bLast logAlpha q N z m‖ ≤ M.growth := by
  refine (BakerLemma3.norm_vdplF_le coord support p h b bLast logAlpha
    q N z m).trans ?_
  calc
    (∑ lambda ∈ support,
        ‖sourceCoefficient coord p h b bLast q N z m lambda‖ *
          Real.exp
            (‖modifiedRate coord b bLast logAlpha lambda‖ *
              ‖z‖)) ≤
        ∑ _lambda ∈ support,
          (P.coeffHeight * M.deltaMajorant) * M.exponentialMajorant := by
      apply sum_le_sum
      intro lambda hlambda
      exact mul_le_mul (M.sourceCoefficient_le hlambda)
        (M.exponential_le lambda hlambda) (Real.exp_pos _).le
        (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
    _ = (support.card : ℝ) *
          ((P.coeffHeight * M.deltaMajorant) * M.exponentialMajorant) := by
      simp
    _ ≤ M.supportMajorant *
          ((P.coeffHeight * M.deltaMajorant) * M.exponentialMajorant) := by
      exact mul_le_mul_of_nonneg_right M.support_card_le
        (mul_nonneg
          (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
          M.exponentialMajorant_nonneg)
    _ = M.growth := by simp [growth, mul_assoc]

/-- The exact termwise comparison assembled into one global error bound. -/
theorem norm_vdplG_sub_vdplF_le_error
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    (logAlphaLast : ℂ) (hbLast : bLast ≠ 0)
    {linearFormBound : ℝ} (hbound : 0 ≤ linearFormBound)
    (hsmall :
      ‖logForm b bLast logAlpha logAlphaLast‖ ≤ linearFormBound) :
    ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
        vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      M.error linearFormBound := by
  refine (BakerLemma3.norm_vdplG_sub_vdplF_le_of_logForm
    coord support p h b hbLast logAlpha logAlphaLast q N z m hsmall).trans ?_
  let errorTerm : ℝ :=
    Real.exp (M.amplificationMajorant * linearFormBound) *
      (M.amplificationMajorant * linearFormBound)
  have herrorTerm : 0 ≤ errorTerm := by
    dsimp only [errorTerm]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg M.amplificationMajorant_nonneg hbound)
  calc
    (∑ lambda ∈ support,
        let U := ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ *
          linearFormBound * ‖z‖
        ‖sourceCoefficient coord p h b bLast q N z m lambda‖ *
          ‖Complex.exp
            (modifiedRate coord b bLast logAlpha lambda *
              z)‖ *
          (Real.exp U * U)) ≤
        ∑ _lambda ∈ support,
          (P.coeffHeight * M.deltaMajorant) *
            M.exponentialMajorant * errorTerm := by
      apply sum_le_sum
      intro lambda hlambda
      let U : ℝ := ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ *
        linearFormBound * ‖z‖
      have hU : U ≤ M.amplificationMajorant * linearFormBound := by
        dsimp only [U]
        calc
          ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ *
                linearFormBound * ‖z‖ =
              (‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ *
                ‖z‖) * linearFormBound := by ring
          _ ≤ M.amplificationMajorant * linearFormBound :=
            mul_le_mul_of_nonneg_right (M.amplification_le lambda hlambda) hbound
      have hU_nonneg : 0 ≤ U := by
        dsimp only [U]
        positivity
      have hexponential :
          ‖Complex.exp
            (modifiedRate coord b bLast logAlpha lambda *
              z)‖ ≤ M.exponentialMajorant := by
        calc
          ‖Complex.exp
              (modifiedRate coord b bLast logAlpha lambda *
                z)‖ ≤
              Real.exp
                ‖modifiedRate coord b bLast logAlpha lambda *
                  z‖ :=
            Complex.norm_exp_le_exp_norm _
          _ ≤ Real.exp
              (‖modifiedRate coord b bLast logAlpha lambda‖ *
                ‖z‖) :=
            Real.exp_le_exp.mpr (norm_mul_le _ _)
          _ ≤ M.exponentialMajorant := M.exponential_le lambda hlambda
      have herror : Real.exp U * U ≤ errorTerm := by
        dsimp only [errorTerm]
        exact mul_le_mul (Real.exp_le_exp.mpr hU) hU
          hU_nonneg (Real.exp_pos _).le
      exact mul_le_mul
        (mul_le_mul (M.sourceCoefficient_le hlambda) hexponential
          (norm_nonneg _)
          (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg))
        herror (mul_nonneg (Real.exp_pos _).le hU_nonneg)
        (mul_nonneg
          (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
          M.exponentialMajorant_nonneg)
    _ = (support.card : ℝ) *
          (((P.coeffHeight * M.deltaMajorant) *
            M.exponentialMajorant) * errorTerm) := by simp
    _ ≤ M.supportMajorant *
          (((P.coeffHeight * M.deltaMajorant) *
            M.exponentialMajorant) * errorTerm) := by
      exact mul_le_mul_of_nonneg_right M.support_card_le
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
            M.exponentialMajorant_nonneg)
          herrorTerm)
    _ = M.error linearFormBound := by
      simp only [error, growth]
      dsimp only [errorTerm]
      ring

end SourceMajorants

/-- Exponentially small upper bound for the original logarithmic form. -/
def smallLinearFormBound {ι : Type*} [Fintype ι]
    (P : VDPLParameters ι) (sourceConstant : ℝ) : ℝ :=
  Real.exp (-sourceExponent P sourceConstant)

/-- Source-shaped global growth envelope. -/
def growthEnvelope {ι : Type*} [Fintype ι]
    (P : VDPLParameters ι) (sourceConstant growthMultiplier : ℝ) : ℝ :=
  Real.exp (growthMultiplier * sourceExponent P sourceConstant)

/-- Source-shaped global comparison-error envelope. -/
def errorEnvelope {ι : Type*} [Fintype ι]
    (P : VDPLParameters ι) (sourceConstant errorMultiplier : ℝ) : ℝ :=
  Real.exp (-errorMultiplier * sourceExponent P sourceConstant)

/-- The purely numerical part of the quantitative Lemma 3 application.
The two fields ending in `_le` are explicit real inequalities; they contain
no vanishing, integrality, field-degree, or auxiliary-function assertion. -/
structure SourceNumericalConditions
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*}
    {P : VDPLParameters ι} {coord : SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)}
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m) where
  sourceConstant : ℝ
  growthMultiplier : ℝ
  errorMultiplier : ℝ
  sourceConstant_nonneg : 0 ≤ sourceConstant
  growthMultiplier_nonneg : 0 ≤ growthMultiplier
  errorMultiplier_nonneg : 0 ≤ errorMultiplier
  growth_le : M.growth ≤
    growthEnvelope P sourceConstant growthMultiplier
  error_le : M.error (smallLinearFormBound P sourceConstant) ≤
    errorEnvelope P sourceConstant errorMultiplier

namespace SourceNumericalConditions

variable
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*}
    {P : VDPLParameters ι} {coord : SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)}
    {M : SourceMajorants P coord support p h b bLast logAlpha q N z m}

theorem smallLinearFormBound_pos (B : SourceNumericalConditions M) :
    0 < smallLinearFormBound P B.sourceConstant := by
  unfold smallLinearFormBound
  positivity

theorem sourceExponent_nonneg (B : SourceNumericalConditions M) :
    0 ≤ BakerLemma3Concrete.sourceExponent P B.sourceConstant :=
  BakerLemma3Concrete.sourceExponent_nonneg P B.sourceConstant_nonneg

end SourceNumericalConditions

/-- Algebraic data for the concrete lower-bound alternative.  The
`termIntegral` field is precisely where the sharp powered-Delta denominator
normalization is consumed.  The degree equality is stated separately so it
can be filled by
`Kummer.finrank_adjoin_thirteenthRoots_primes_rat` without importing the
whole Kummer development into every extrapolation module. -/
structure AlgebraicCertificateInputs
    {oldRank : ℕ} {I K : Type*} [Field K] [NumberField K]
    (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    (radicalRank : ℕ) where
  term : I → K
  denominator : K
  sigma : K →ₐ[ℚ] ℂ
  scale : ℂ
  scale_ne : scale ≠ 0
  denominator_map : sigma denominator = scale
  termIntegral : ∀ lambda ∈ support,
    IsIntegral ℤ (denominator * term lambda)
  term_map : ∀ lambda ∈ support,
    sigma (term lambda) =
      algebraicComplexTerm coord h b bLast logAlpha logAlphaLast
        q N z m lambda
  conjugateBound : ℝ
  conjugateBound_pos : 0 < conjugateBound
  other_embeddings : ∀ tau : K →ₐ[ℚ] ℂ, tau ≠ sigma →
    ‖tau (denominator * algebraicAuxiliaryValue support p term)‖ ≤
      conjugateBound
  finrank_eq_thirteen_pow : Module.finrank ℚ K = 13 ^ radicalRank

/-- **Concrete source Lemma 3.**

Under the displayed coefficient, Delta, exponential, support, and
amplification estimates, a small logarithmic form gives both the global
growth and closeness bounds needed by the integral and rational
extrapolation steps.  If the sharp denominator theorem makes the lifted
terms integral, the algebraic value is either zero or `f` satisfies the
Liouville lower bound with the exact Kummer degree `13 ^ radicalRank`.

The remaining `herrorToLiouville` hypothesis is a single explicit real
inequality.  It is the numerical endpoint of the source parameter check,
not an unproved analytic or algebraic assertion. -/
theorem quantitative_lemma3
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I K : Type*} [Field K] [NumberField K]
    {P : VDPLParameters ι} {coord : SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ} {logAlphaLast : ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)}
    {radicalRank : ℕ}
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m)
    (B : SourceNumericalConditions M)
    (A : AlgebraicCertificateInputs (K := K) coord support p h b bLast
      logAlpha logAlphaLast q N z m radicalRank)
    (hbLast : bLast ≠ 0)
    (hsmall : ‖logForm b bLast logAlpha logAlphaLast‖ ≤
      smallLinearFormBound P B.sourceConstant)
    (herrorToLiouville :
      errorEnvelope P B.sourceConstant B.errorMultiplier ≤
        (((A.conjugateBound ^ (13 ^ radicalRank - 1))⁻¹ / ‖A.scale‖) / 2)) :
    ‖vdplF coord support p h b bLast logAlpha q N z m‖ ≤
        growthEnvelope P B.sourceConstant B.growthMultiplier ∧
      ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
          vdplF coord support p h b bLast logAlpha q N z m‖ ≤
        errorEnvelope P B.sourceConstant B.errorMultiplier ∧
      (vdplG coord support p h b bLast logAlpha logAlphaLast q N z m = 0 ∨
        (((A.conjugateBound ^ (13 ^ radicalRank - 1))⁻¹ / ‖A.scale‖) / 2) ≤
          ‖vdplF coord support p h b bLast logAlpha q N z m‖) := by
  have hgrowth :
      ‖vdplF coord support p h b bLast logAlpha q N z m‖ ≤
        growthEnvelope P B.sourceConstant B.growthMultiplier :=
    (M.norm_vdplF_le_growth).trans B.growth_le
  have hcloseError :
      ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
          vdplF coord support p h b bLast logAlpha q N z m‖ ≤
        errorEnvelope P B.sourceConstant B.errorMultiplier := by
    exact (M.norm_vdplG_sub_vdplF_le_error logAlphaLast hbLast
      B.smallLinearFormBound_pos.le hsmall).trans B.error_le
  have hcloseLiouville :
      ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
          vdplF coord support p h b bLast logAlpha q N z m‖ ≤
        (((A.conjugateBound ^ (Module.finrank ℚ K - 1))⁻¹ /
          ‖A.scale‖) / 2) := by
    rw [A.finrank_eq_thirteen_pow]
    exact hcloseError.trans herrorToLiouville
  have halternative :=
    BakerLemma3.vdplG_eq_zero_or_half_lower_of_termwise_integral
      coord support p h b bLast logAlpha logAlphaLast q N z m
      A.term A.denominator A.sigma A.scale_ne A.denominator_map
      A.termIntegral A.term_map A.conjugateBound_pos A.other_embeddings
      hcloseLiouville
  rw [A.finrank_eq_thirteen_pow] at halternative
  exact ⟨hgrowth, hcloseError, halternative⟩

#print axioms Erdos240.BakerLemma3Concrete.SourceMajorants.norm_vdplF_le_growth
#print axioms Erdos240.BakerLemma3Concrete.SourceMajorants.norm_vdplG_sub_vdplF_le_error
#print axioms Erdos240.BakerLemma3Concrete.quantitative_lemma3

end Erdos240.BakerLemma3Concrete
