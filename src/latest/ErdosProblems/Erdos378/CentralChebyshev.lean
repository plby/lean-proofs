/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CentralVaughanSmallFactors
import ErdosProblems.Erdos378.CentralVaughanFourth

/-!
# A finite central-range Vaughan estimate

This file combines all four exact terms of Vaughan's identity.  Its
hypotheses separate the finite analytic estimate from the later elementary
asymptotic verification for the chosen logarithmic cutoff.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace CentralChebyshev

open BoundedGaps.Maynard
open PrimeReciprocal
open AdaptiveShifts
open CentralCorrelation
open VaughanReciprocalFull
open CentralVaughanSmallFactors
open CentralVaughanFourth

noncomputable section

def centralChebyshevMajorant (y T : ℕ) (B delta : ℝ) : ℝ :=
  (T : ℝ) * (2 * Real.log (y : ℝ) * B) +
    ((T ^ 2 : ℕ) : ℝ) * (Real.log (y : ℝ) * B) +
      ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (centralFourthUniformMajorant y T delta)

theorem norm_weightedChebyshevInterval_central_le
    {X : ℝ} (hX : 0 < X) {x y T : ℕ} {B delta : ℝ}
    (hT : 0 < T) (hTy : T ≤ y) (hTx : T ^ 4 ≤ x)
    (hxy : x < y) (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hB0 : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hsmallSize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      centralCorrelationSizeCondition (x / q + 1))
    (hsmallB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      1 + adaptiveCorrelationEnvelope (x / q + 1) ≤ B)
    (hlargeSize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      centralCorrelationSizeCondition L)
    (hlargeEnvelope : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      adaptiveCorrelationEnvelope L ≤ delta * L) :
    ‖weightedChebyshevInterval (reciprocalWeight X) x y‖ ≤
      centralChebyshevMajorant y T B delta := by
  have hTone : 1 ≤ T := hT
  have hTfour : T ≤ T ^ 4 := by nlinarith [pow_pos hT 2, pow_pos hT 3]
  have hTlex : T ≤ x := hTfour.trans hTx
  rw [weightedChebyshevInterval_eq_vaughan,
    weightedVaughanIntervalOne_reciprocal_eq_zero (by exact_mod_cast hTlex),
    zero_add]
  have hTwo := norm_weightedVaughanIntervalTwo_central_le
    hX hT hTy hTx hxy hXlo hXhi hyx hB0 hsmallSize hsmallB
  have hThree := norm_weightedVaughanIntervalThree_central_le
    hX hT hTy hTx hxy hXlo hXhi hyx hB0 hsmallSize hsmallB
  have hFour := norm_weightedVaughanIntervalFour_central_le
    hT hdelta hlargeSize hlargeEnvelope hXlo hXhi hyx
  unfold centralChebyshevMajorant
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hTwo hThree)) hFour)

end

end CentralChebyshev
end Erdos378
