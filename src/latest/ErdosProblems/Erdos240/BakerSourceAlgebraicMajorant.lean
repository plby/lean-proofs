/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceMajorantClosedForm

/-!
# Source-faithful algebraic growth majorants

The auxiliary function `f` may have a large modified rate when the
distinguished coefficient is not maximal.  The source-faithful estimate
instead uses the algebraic function `g` as its base.  Termwise,

`f_term = g_term * exp (-(lambda_last / b_last) * z * Lambda)`.

Thus the large coefficient ratios do not occur in the growth majorant.
They occur only in the perturbation, already multiplied by the assumed
small linear form `Lambda`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceAlgebraicMajorant

open Finset
open Erdos240
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceMajorantClosedForm
open BakerSourceState

/-- An algebraic-rate exponential majorant attached to the remaining data
of a concrete Lemma-3 majorant. -/
structure AlgebraicExponentialMajorant
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*}
    (P : VDPLParameters ι) (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    (M : SourceMajorants P coord support p h b bLast logAlpha q N z m) where
  majorant : ℝ
  majorant_nonneg : 0 ≤ majorant
  exponential_le : ∀ lambda ∈ support,
    Real.exp
      (‖algebraicRate coord logAlpha logAlphaLast lambda‖ * ‖z‖) ≤ majorant

namespace AlgebraicExponentialMajorant

variable
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*}
    {P : VDPLParameters ι} {coord : SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ} {logAlphaLast : ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)}
    {M : SourceMajorants P coord support p h b bLast logAlpha q N z m}

/-- Growth of the algebraic base function `g`. -/
def growth (A : AlgebraicExponentialMajorant P coord support p h b bLast
    logAlpha logAlphaLast q N z m M) : ℝ :=
  M.supportMajorant * (P.coeffHeight * M.deltaMajorant) * A.majorant

/-- The comparison error measured relative to algebraic growth. -/
def error (A : AlgebraicExponentialMajorant P coord support p h b bLast
    logAlpha logAlphaLast q N z m M) (linearFormBound : ℝ) : ℝ :=
  A.growth *
    (Real.exp (M.amplificationMajorant * linearFormBound) *
      (M.amplificationMajorant * linearFormBound))

/-- The algebraic function has the advertised growth. -/
theorem norm_vdplG_le_growth
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M) :
    ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m‖ ≤
      A.growth := by
  have hraw :
      ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m‖ ≤
        ∑ lambda ∈ support,
          ‖sourceCoefficient coord p h b bLast q N z m lambda‖ *
            Real.exp
              (‖algebraicRate coord logAlpha logAlphaLast lambda‖ * ‖z‖) := by
    simpa [vdplG] using
      ExponentialPolynomial.norm_ordinaryDerivative_le support
        (sourceCoefficient coord p h b bLast q N z m)
        (algebraicRate coord logAlpha logAlphaLast) 0 z
  refine hraw.trans ?_
  calc
    (∑ lambda ∈ support,
        ‖sourceCoefficient coord p h b bLast q N z m lambda‖ *
          Real.exp
            (‖algebraicRate coord logAlpha logAlphaLast lambda‖ * ‖z‖)) ≤
        ∑ _lambda ∈ support,
          (P.coeffHeight * M.deltaMajorant) * A.majorant := by
      apply Finset.sum_le_sum
      intro lambda hlambda
      exact mul_le_mul (M.sourceCoefficient_le hlambda)
        (A.exponential_le lambda hlambda) (Real.exp_pos _).le
        (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
    _ = (support.card : ℝ) *
          ((P.coeffHeight * M.deltaMajorant) * A.majorant) := by simp
    _ ≤ M.supportMajorant *
          ((P.coeffHeight * M.deltaMajorant) * A.majorant) := by
      exact mul_le_mul_of_nonneg_right M.support_card_le
        (mul_nonneg
          (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
          A.majorant_nonneg)
    _ = A.growth := by simp [growth, mul_assoc]

/-- Exact source factorization with the algebraic exponential as base. -/
theorem sourceTerm_modified_eq_algebraic_mul_exp_neg_perturbation
    (hbLast : bLast ≠ 0) (lambda : I) :
    sourceCoefficient coord p h b bLast q N z m lambda *
        Complex.exp (modifiedRate coord b bLast logAlpha lambda * z) =
      (sourceCoefficient coord p h b bLast q N z m lambda *
        Complex.exp
          (algebraicRate coord logAlpha logAlphaLast lambda * z)) *
        Complex.exp
          (-(perturbationRate coord b bLast logAlpha logAlphaLast lambda * z)) := by
  have hrate := algebraicRate_eq_modifiedRate_add_perturbationRate
    coord b hbLast logAlpha logAlphaLast lambda
  rw [Complex.exp_neg]
  have hmodified :
      modifiedRate coord b bLast logAlpha lambda * z =
        algebraicRate coord logAlpha logAlphaLast lambda * z -
          perturbationRate coord b bLast logAlpha logAlphaLast lambda * z := by
    rw [hrate]
    ring
  rw [hmodified, Complex.exp_sub]
  ring

/-- Global comparison estimate based on `g`, not on the potentially large
modified exponential rate of `f`. -/
theorem norm_vdplG_sub_vdplF_le_algebraic
    (hbLast : bLast ≠ 0) :
    ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
        vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      ∑ lambda ∈ support,
        ‖sourceCoefficient coord p h b bLast q N z m lambda‖ *
          ‖Complex.exp
            (algebraicRate coord logAlpha logAlphaLast lambda * z)‖ *
          (Real.exp
              ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda * z‖ *
            ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda * z‖) := by
  rw [vdplG_eq_sum, vdplF_eq_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun lambda hlambda ↦ ?_)
  let u := perturbationRate coord b bLast logAlpha logAlphaLast lambda * z
  have hfactor :
      sourceCoefficient coord p h b bLast q N z m lambda *
            Complex.exp (algebraicRate coord logAlpha logAlphaLast lambda * z) -
          sourceCoefficient coord p h b bLast q N z m lambda *
            Complex.exp (modifiedRate coord b bLast logAlpha lambda * z) =
        (sourceCoefficient coord p h b bLast q N z m lambda *
          Complex.exp (algebraicRate coord logAlpha logAlphaLast lambda * z)) *
            (1 - Complex.exp (-u)) := by
    rw [sourceTerm_modified_eq_algebraic_mul_exp_neg_perturbation
      hbLast lambda]
    dsimp only [u]
    ring
  rw [hfactor, norm_mul, norm_mul]
  have hrem := ComplexTaylor.norm_exp_sub_partialSum_le (-u) 1
  have hpartial : ComplexTaylor.expPartialSum (-u) 1 = 1 := by
    simp [ComplexTaylor.expPartialSum]
  rw [hpartial, pow_one, norm_neg] at hrem
  have hone : ‖1 - Complex.exp (-u)‖ = ‖Complex.exp (-u) - 1‖ := by
    rw [← norm_neg]
    congr 1
    ring
  rw [hone]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hrem
      (mul_nonneg (norm_nonneg _ ) (norm_nonneg _))

/-- Source comparison with only a bound on the original small linear form. -/
theorem norm_vdplG_sub_vdplF_le_algebraic_of_logForm
    (hbLast : bLast ≠ 0) {bound : ℝ}
    (hsmall : ‖logForm b bLast logAlpha logAlphaLast‖ ≤ bound) :
    ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
        vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      ∑ lambda ∈ support,
        let U := ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ * bound * ‖z‖
        ‖sourceCoefficient coord p h b bLast q N z m lambda‖ *
          ‖Complex.exp
            (algebraicRate coord logAlpha logAlphaLast lambda * z)‖ *
          (Real.exp U * U) := by
  refine (norm_vdplG_sub_vdplF_le_algebraic hbLast).trans ?_
  apply Finset.sum_le_sum
  intro lambda hlambda
  let U := ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ * bound * ‖z‖
  have hU :
      ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda * z‖ ≤ U :=
    norm_perturbationRate_mul_le_of_logForm coord b bLast logAlpha logAlphaLast
      lambda z hsmall
  dsimp only
  gcongr

/-- The exact comparison error is controlled by algebraic growth and the
same amplification majorant as before. -/
theorem norm_vdplG_sub_vdplF_le_error
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    (hbLast : bLast ≠ 0) {linearFormBound : ℝ}
    (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast logAlpha logAlphaLast‖ ≤ linearFormBound) :
    ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
        vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      A.error linearFormBound := by
  refine (norm_vdplG_sub_vdplF_le_algebraic_of_logForm
    hbLast hsmall).trans ?_
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
            (algebraicRate coord logAlpha logAlphaLast lambda * z)‖ *
          (Real.exp U * U)) ≤
        ∑ _lambda ∈ support,
          (P.coeffHeight * M.deltaMajorant) * A.majorant * errorTerm := by
      apply Finset.sum_le_sum
      intro lambda hlambda
      let U : ℝ := ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ *
        linearFormBound * ‖z‖
      have hU : U ≤ M.amplificationMajorant * linearFormBound := by
        dsimp only [U]
        calc
          ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ *
                linearFormBound * ‖z‖ =
              (‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ * ‖z‖) *
                linearFormBound := by ring
          _ ≤ M.amplificationMajorant * linearFormBound :=
            mul_le_mul_of_nonneg_right (M.amplification_le lambda hlambda) hbound
      have hU0 : 0 ≤ U := by dsimp only [U]; positivity
      have hexp :
          ‖Complex.exp
            (algebraicRate coord logAlpha logAlphaLast lambda * z)‖ ≤
              A.majorant := by
        calc
          ‖Complex.exp
              (algebraicRate coord logAlpha logAlphaLast lambda * z)‖ ≤
              Real.exp
                ‖algebraicRate coord logAlpha logAlphaLast lambda * z‖ :=
            Complex.norm_exp_le_exp_norm _
          _ ≤ Real.exp
              (‖algebraicRate coord logAlpha logAlphaLast lambda‖ * ‖z‖) :=
            Real.exp_le_exp.mpr (norm_mul_le _ _)
          _ ≤ A.majorant := A.exponential_le lambda hlambda
      have herr : Real.exp U * U ≤ errorTerm := by
        dsimp only [errorTerm]
        exact mul_le_mul (Real.exp_le_exp.mpr hU) hU hU0 (Real.exp_pos _).le
      exact mul_le_mul
        (mul_le_mul (M.sourceCoefficient_le hlambda) hexp (norm_nonneg _)
          (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg))
        herr (mul_nonneg (Real.exp_pos _).le hU0)
        (mul_nonneg
          (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
          A.majorant_nonneg)
    _ = (support.card : ℝ) *
          (((P.coeffHeight * M.deltaMajorant) * A.majorant) * errorTerm) := by simp
    _ ≤ M.supportMajorant *
          (((P.coeffHeight * M.deltaMajorant) * A.majorant) * errorTerm) := by
      exact mul_le_mul_of_nonneg_right M.support_card_le
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
            A.majorant_nonneg) herrorTerm)
    _ = A.error linearFormBound := by
      simp only [error, growth]
      dsimp only [errorTerm]
      ring

/-- Triangle-inequality recovery of the analytic auxiliary function from
algebraic growth and comparison error. -/
theorem norm_vdplF_le_growth_add_error
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    (hbLast : bLast ≠ 0) {linearFormBound : ℝ}
    (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast logAlpha logAlphaLast‖ ≤ linearFormBound) :
    ‖vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      A.growth + A.error linearFormBound := by
  calc
    ‖vdplF coord support p h b bLast logAlpha q N z m‖ =
        ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
            (vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
              vdplF coord support p h b bLast logAlpha q N z m)‖ := by ring_nf
    _ ≤ ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m‖ +
          ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
            vdplF coord support p h b bLast logAlpha q N z m‖ := norm_sub_le _ _
    _ ≤ A.growth + A.error linearFormBound :=
      add_le_add A.norm_vdplG_le_growth
        (A.norm_vdplG_sub_vdplF_le_error hbLast hbound hsmall)

end AlgebraicExponentialMajorant

/-! ## Corrected source-state specialization -/

/-- Uniform algebraic-rate bound for every coefficient state.  Unlike the
modified-rate bound, this expression is independent of `b` and `bLast`. -/
def sourceAlgebraicRateBound {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  (∑ r : Fin oldRank, (P.LiZero r : ℝ) * ‖oldLog P r‖) +
    (P.LlastZero : ℝ) * ‖lastLog P‖

theorem sourceAlgebraicRateBound_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    0 ≤ sourceAlgebraicRateBound P := by
  unfold sourceAlgebraicRateBound
  positivity

theorem norm_state_algebraicRate_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) :
    ‖algebraicRate (coordinatesForState state) (oldLog P) (lastLog P) lambda‖ ≤
      sourceAlgebraicRateBound P := by
  unfold algebraicRate sourceAlgebraicRateBound
  calc
    ‖(∑ r,
          ((coordinatesForState state).oldExponent lambda r : ℂ) * oldLog P r) +
        ((coordinatesForState state).lastExponent lambda : ℂ) * lastLog P‖ ≤
        ‖∑ r,
          ((coordinatesForState state).oldExponent lambda r : ℂ) * oldLog P r‖ +
          ‖((coordinatesForState state).lastExponent lambda : ℂ) * lastLog P‖ :=
      norm_add_le _ _
    _ ≤ (∑ r,
          ‖((coordinatesForState state).oldExponent lambda r : ℂ) * oldLog P r‖) +
          ‖((coordinatesForState state).lastExponent lambda : ℂ) * lastLog P‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (∑ r, (P.LiZero r : ℝ) * ‖oldLog P r‖) +
          (P.LlastZero : ℝ) * ‖lastLog P‖ := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro r _hr
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (by
          exact_mod_cast state_oldExponent_le_initial P state lambda r)
          (norm_nonneg _)
      · rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (by
          exact_mod_cast state_lastExponent_le_initial P state lambda)
          (norm_nonneg _)

/-- The canonical algebraic-rate majorant for an actual source state. -/
def stateAlgebraicExponentialMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    AlgebraicExponentialMajorant P (coordinatesForState state) state.support
      state.coeff P.h b bLast (oldLog P) (lastLog P) P.q J z m
      (stateSourceMajorants P state b bLast z m) where
  majorant := Real.exp (sourceAlgebraicRateBound P * ‖z‖)
  majorant_nonneg := (Real.exp_pos _).le
  exponential_le := by
    intro lambda _hlambda
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (norm_state_algebraicRate_le P state lambda) (norm_nonneg z))

@[simp] theorem stateAlgebraicExponentialMajorant_majorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (stateAlgebraicExponentialMajorant P state b bLast z m).majorant =
      Real.exp (sourceAlgebraicRateBound P * ‖z‖) := rfl

/-- Concrete source-state algebraic growth theorem. -/
theorem norm_state_vdplG_le_algebraicGrowth {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) (lastLog P) P.q J z m‖ ≤
      (stateAlgebraicExponentialMajorant P state b bLast z m).growth :=
  (stateAlgebraicExponentialMajorant P state b bLast z m).norm_vdplG_le_growth

/-- Concrete source-state comparison theorem based on algebraic growth. -/
theorem norm_state_vdplG_sub_vdplF_le_algebraicError {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) {linearFormBound : ℝ}
    (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) (lastLog P) P.q J z m -
        vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) P.q J z m‖ ≤
      (stateAlgebraicExponentialMajorant P state b bLast z m).error
        linearFormBound :=
  (stateAlgebraicExponentialMajorant P state b bLast z m).norm_vdplG_sub_vdplF_le_error
    hbLast hbound hsmall

/-- Concrete recovery of `f` from algebraic growth plus the small comparison
error. -/
theorem norm_state_vdplF_le_algebraicGrowth_add_error {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) {linearFormBound : ℝ}
    (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) P.q J z m‖ ≤
      (stateAlgebraicExponentialMajorant P state b bLast z m).growth +
        (stateAlgebraicExponentialMajorant P state b bLast z m).error
          linearFormBound :=
  (stateAlgebraicExponentialMajorant P state b bLast z m).norm_vdplF_le_growth_add_error
    hbLast hbound hsmall

#print axioms AlgebraicExponentialMajorant.sourceTerm_modified_eq_algebraic_mul_exp_neg_perturbation
#print axioms AlgebraicExponentialMajorant.norm_vdplG_sub_vdplF_le_error
#print axioms AlgebraicExponentialMajorant.norm_vdplF_le_growth_add_error
#print axioms norm_state_vdplF_le_algebraicGrowth_add_error

end Erdos240.BakerSourceAlgebraicMajorant
