/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOffsetOuterQuadraticBarrier

/-!
# Scale-free algebra for the constant-offset outer corridor

The exact-clock barriers have coefficients `4 - epsilon` and `4 + epsilon`.
Once the common rounding/offset error is at most one quarter of
`epsilon * x`, their integer endpoints lie on opposite sides of `4x` with a
quantified gap.  The lemmas below isolate the real polynomial calculations
used by the upper and lower deletion-rate comparisons.
-/

namespace Erdos207

noncomputable section

/-- Elementary endpoint bounds after paying the common offset and rounding
error. -/
lemma fineOffset_endpoint_bands
    {epsilon x s U L : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hx : 0 ≤ x) (hs : 0 ≤ s) (hsmall : 4 * s ≤ epsilon * x)
    (hU : U ≤ (4 - epsilon) * x + s)
    (hL : (4 + epsilon) * x - s ≤ L)
    (hLupper : L ≤ (4 + epsilon) * x) :
    U ≤ 4 * x ∧ 4 * x ≤ L ∧ L ≤ 5 * x ∧
      3 * epsilon * x ≤ 2 * (L - U) := by
  have hex : 0 ≤ epsilon * x := mul_nonneg hepsilon hx
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The upper exact-clock derivative is at most `6L/E` once the rounded
lower endpoint is at least `4x`. -/
lemma fineOffset_upper_rate_crossmul
    {epsilon x E L : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonFour : epsilon ≤ 4)
    (hx : 0 ≤ x) (hE : 0 ≤ E) (hL : 4 * x ≤ L) :
    3 * (4 - epsilon) * (2 * E - 3) * x ≤ 6 * L * E := by
  have hcoeff : 0 ≤ 4 - epsilon := by linarith
  have htwo : 2 * E - 3 ≤ 2 * E := by linarith
  have hprod : (4 - epsilon) * (2 * E - 3) ≤ 4 * (2 * E) := by
    by_cases hterm : 0 ≤ 2 * E - 3
    · exact mul_le_mul (by linarith) htwo hterm (by positivity)
    · have : (4 - epsilon) * (2 * E - 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoeff (le_of_not_ge hterm)
      exact this.trans (by positivity)
  have hleft := mul_le_mul_of_nonneg_right hprod hx
  have hright := mul_le_mul_of_nonneg_right hL hE
  nlinarith

/-- The lower exact-clock derivative dominates `6U/E`; the loss of three
pairs in the discrete derivative is paid by `epsilon * E ≥ 6`. -/
lemma fineOffset_lower_rate_crossmul
    {epsilon x E U : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hx : 0 ≤ x) (hE : 0 ≤ E)
    (hU0 : 0 ≤ U) (hU : U ≤ 4 * x)
    (hscale : 100 ≤ epsilon * E) :
    6 * U * E ≤ 3 * (4 + epsilon) * (2 * E - 3) * x := by
  have hfour : 0 ≤ 4 + epsilon := by positivity
  have hEx : 0 ≤ E * x := mul_nonneg hE hx
  have hUE : U * E ≤ (4 * x) * E :=
    mul_le_mul_of_nonneg_right hU hE
  have heX : 0 ≤ epsilon * x := mul_nonneg hepsilon hx
  nlinarith

/-- The exact numerator `2U² + K` fits in the lower availability width.
The natural quotient `D = ⌊EL/3⌋` is represented only by
`EL ≤ 3D + 2`, so this lemma also pays the full integer-division loss. -/
lemma fineOffset_lower_scalar_crossmul
    {epsilon x E U L K D : ℝ}
    (hepsilon : 0 ≤ epsilon) (hx : 1 ≤ x) (hE : 0 ≤ E)
    (hU0 : 0 ≤ U) (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hU : U ≤ 4 * x) (hLlower : 4 * x ≤ L) (hLupper : L ≤ 5 * x)
    (hmargin : 3 * epsilon * x ≤ 2 * (L - U))
    (hscale : 100 ≤ epsilon * E)
    (hK : K ≤ epsilon * x ^ 2)
    (hdiv : E * L ≤ 3 * D + 2) (hgap : U ≤ D) :
    E * (U * (2 * U) + K) ≤ 6 * L * (D - U) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hsum : 4 * x ≤ L + U := by nlinarith
  have hmargin0 : 0 ≤ L - U := by
    have : 0 ≤ 3 * epsilon * x := by positivity
    nlinarith
  have hgapProduct :
      12 * epsilon * x ^ 2 ≤ 2 * (L - U) * (L + U) := by
    have hmul := mul_le_mul hmargin hsum (by positivity) (by positivity)
    nlinarith
  have hgapScaled :
      12 * epsilon * E * x ^ 2 ≤
        2 * E * (L ^ 2 - U ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hgapProduct hE
    nlinarith
  have hUL : U * L ≤ 20 * x ^ 2 := by
    have := mul_le_mul hU hLupper hL0 (by positivity)
    nlinarith
  have hlinear : L ≤ 5 * x ^ 2 := by
    have hxx : x ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    exact hLupper.trans (by nlinarith)
  have hKscaled : E * K ≤ epsilon * E * x ^ 2 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hK hE
  have hlarge : 140 * x ^ 2 ≤ 11 * epsilon * E * x ^ 2 := by
    have hxSq : 0 ≤ x ^ 2 := sq_nonneg x
    have hs := mul_le_mul_of_nonneg_right hscale hxSq
    nlinarith
  have hdivision := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ 2 * L by positivity)
  nlinarith

end

end Erdos207
