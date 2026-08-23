/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma4OuterContour
import ErdosProblems.Erdos240.BakerLemma3Instantiation

/-!
# Strict source Lemma-4 pointwise assembly

The non-strict `exp (-E/2)` local-circle estimate is not enough for the
Liouville alternative, because the outer contour contributes a positive
remainder.  This module retains the actual slack in equation (9): a contour
loss of at most `E/24` turns `exp (-2E/3)` jets into an `exp (-5E/8)` local
sum.  If the sharp `3^(-R*S)` outer term has the same bound, then `E >= 8`
makes their sum strictly smaller than `exp (-E/2)`.
-/

open scoped BigOperators
open Complex Finset Function Metric

noncomputable section

namespace Erdos240.BakerSourceInnerPointwiseIndependent

open Erdos240
open Erdos240.BakerLemma3
open Erdos240.BakerLemma3Concrete
open Erdos240.BakerLemma3Instantiation
open Erdos240.BakerLemma4Concrete
open Erdos240.BakerSourceState
open Erdos240.InterpolationProducts

/-- Strict equation-(9) estimate with the source's unused contour slack.
The outer hypothesis is exactly the sharp nodal remainder left by the
checked outer-circle theorem, after its radial factor has been bounded by
`3/2`. -/
theorem norm_entire_eval_lt_exp_neg_half_of_sharpOuter
    {Rold Rnext S l : ℕ} (hRoldPos : 1 ≤ Rold) (hS : 1 ≤ S)
    (hRoldl : Rold < l) (hRnext : 0 < Rnext) (hl : l ≤ Rnext)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A delta outer : ℝ} (hA : 8 ≤ A) (hdelta : 0 ≤ delta)
    (houter : 0 ≤ outer)
    (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * Rold + l) * S) + Rold * S) ≤
        Real.exp ((1 / 24) * A))
    (hjets : ∀ r : Fin Rold, ∀ m : Fin S,
      ‖iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)‖ ≤ delta)
    (hboundary : ∀ z : ℂ, ‖z‖ = 3 * (Rnext : ℝ) → ‖f z‖ ≤ outer)
    (hsharpOuter :
      (3 / 2 : ℝ) * ((1 / 3 : ℝ) ^ (Rold * S) * outer) <
        Real.exp (-(5 / 8) * A)) :
    ‖f (l : ℂ)‖ < Real.exp (-(1 / 2) * A) := by
  have hlball :
      (l : ℂ) ∈ Metric.ball (0 : ℂ) (3 * (Rnext : ℝ)) := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    have hlReal : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    linarith
  have hnodes : ∀ r : Fin Rold,
      (((r.1 + 1 : ℕ) : ℂ)) ∈
        Metric.ball (0 : ℂ) (3 * (Rnext : ℝ)) := by
    intro r
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    have hrnext : r.1 + 1 ≤ Rnext :=
      (show r.1 + 1 ≤ Rold by omega).trans (hRoldl.le.trans hl)
    have hrnextReal : ((r.1 + 1 : ℕ) : ℝ) ≤ Rnext := by
      exact_mod_cast hrnext
    linarith
  have hid := entire_eval_eq_outer_sub_local hRoldPos hS hRoldl
    hlball hnodes hf
  have hlocalRaw := norm_sum_normalized_localCircleKernel_integral_le
    hRoldl hdelta
      (fun r m => iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)) hjets
  have hlocal :
      ‖∑ r : Fin Rold, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
              (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel Rold S (r.1 + 1) l m.1 z)‖ ≤
        Real.exp (-(5 / 8) * A) := by
    calc
      _ ≤ (2 : ℝ) ^ (((3 * Rold + l) * S) + Rold * S) * delta :=
        hlocalRaw
      _ ≤ Real.exp ((1 / 24) * A) *
          Real.exp (-(2 / 3) * A) :=
        mul_le_mul hcontour hsmall hdelta (Real.exp_pos _).le
      _ = Real.exp (-(5 / 8) * A) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have houterRaw :=
    norm_normalized_outerCircleIntegral_localEntireKernel_newTarget_le
      (S := S) hRnext hRoldl hl houter hboundary
  have hgeom := sharpOuter_geometricFactor_le_three_halves
    (decay := (1 / 3 : ℝ) ^ (Rold * S)) (outer := outer)
    hRnext hl (pow_nonneg (by norm_num) _) houter
  have houterIntegral :
      ‖(2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C((0 : ℂ), 3 * (Rnext : ℝ)),
            localEntireKernel Rold S (l : ℂ) f z)‖ <
        Real.exp (-(5 / 8) * A) :=
    houterRaw.trans_lt (hgeom.trans_lt hsharpOuter)
  have hsum :
      Real.exp (-(5 / 8) * A) + Real.exp (-(5 / 8) * A) <
        Real.exp (-(1 / 2) * A) := by
    have hlog : Real.log 2 < A / 8 := by
      have : Real.log 2 < (1 : ℝ) := by
        nlinarith [Real.log_two_lt_d9]
      nlinarith
    calc
      Real.exp (-(5 / 8) * A) + Real.exp (-(5 / 8) * A) =
          2 * Real.exp (-(5 / 8) * A) := by ring
      _ = Real.exp (Real.log 2 + (-(5 / 8) * A)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ < Real.exp (-(1 / 2) * A) := by
        apply Real.exp_lt_exp.mpr
        nlinarith
  rw [hid]
  exact (norm_sub_le _ _).trans_lt
    ((add_lt_add_of_lt_of_le houterIntegral hlocal).trans hsum)

/-- The integral Liouville alternative using the algebraic-base comparison
error directly.  Unlike `quantitative_lemma3_state_integral`, this theorem
does not route the comparison through the modified-rate `SourceMajorants`;
the checked rational integrality certificate is reused unchanged. -/
theorem state_integral_algebraicAlternative {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1))
    (hclose :
      ‖gSource state b bLast (l : ℂ) m -
          fSource state b bLast (l : ℂ) m‖ ≤
        stateIntegralLiouvilleThreshold P J m) :
    gSource state b bLast (l : ℂ) m = 0 ∨
      stateIntegralLiouvilleThreshold P J m ≤
        ‖fSource state b bLast (l : ℂ) m‖ := by
  change
    vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) (lastLog P) P.q J (l : ℂ) m = 0 ∨
      stateIntegralLiouvilleThreshold P J m ≤
        ‖vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) P.q J (l : ℂ) m‖
  change
    ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) (lastLog P) P.q J (l : ℂ) m -
        vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) P.q J (l : ℂ) m‖ ≤
      stateIntegralLiouvilleThreshold P J m at hclose
  let A := stateIntegralTargetCertificate P state b bLast l m
  have hclose' :
      ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
            (oldLog P) (lastLog P) P.q J (l : ℂ) m -
          vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
            (oldLog P) P.q J (l : ℂ) m‖ ≤
        ((A.conjugateBound ^ (Module.finrank ℚ ℚ - 1))⁻¹ /
          ‖A.scale‖) / 2 := by
    simpa [stateIntegralLiouvilleThreshold, A, stateIntegralTargetCertificate,
      integralTargetCertificate] using hclose
  have halt :=
    BakerLemma3.vdplG_eq_zero_or_half_lower_of_termwise_integral
      (coordinatesForState state) state.support state.coeff P.h b bLast
      (oldLog P) (lastLog P) P.q J (l : ℂ) m
      A.term A.denominator A.sigma A.scale_ne A.denominator_map
      A.termIntegral A.term_map A.conjugateBound_pos A.other_embeddings
      hclose'
  rw [A.finrank_eq_thirteen_pow] at halt
  simpa [stateIntegralLiouvilleThreshold, A, stateIntegralTargetCertificate,
    integralTargetCertificate] using halt

end Erdos240.BakerSourceInnerPointwiseIndependent

#print axioms Erdos240.BakerSourceInnerPointwiseIndependent.norm_entire_eval_lt_exp_neg_half_of_sharpOuter
#print axioms Erdos240.BakerSourceInnerPointwiseIndependent.state_integral_algebraicAlternative
