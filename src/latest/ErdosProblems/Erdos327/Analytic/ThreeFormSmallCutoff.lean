import ErdosProblems.Erdos327.Analytic.ThreeFormBoxBounds

/-!
# Three-form Euler products when the sieve cutoff is below roughness

The explicit sieve schedule can have `z < L` on its first relevant dyadic
blocks.  In that regime every sieved odd prime uses the below-`L` local
factor.  The source product therefore has exponent `-5/2`, while the mixed
product has exponent `-2`.
-/

namespace Erdos327.Analytic

open Real Finset
open scoped BigOperators

noncomputable section

/-- If the ambient prime cutoff is below `L`, every odd prime in the
ambient set belongs to the below-`L` sum. -/
theorem oddPrimeInvBelow_eq_oddPrimeInvSum_of_lt
    {L X : ℕ} (hXL : X < L) :
    oddPrimeInvBelow L X = oddPrimeInvSum X := by
  unfold oddPrimeInvBelow oddPrimeInvSum
  rw [filter_eq_self.mpr]
  intro p hp
  exact (mem_oddPrimesUpTo.mp hp).2.1.trans_lt hXL

/-- Exact source exponent in the `X < L` branch. -/
theorem sourceEulerExponent_eq_of_lt
    {L X : ℕ} (hXL : X < L) :
    sourceEulerExponent L X =
      -(5 / 2 : ℝ) * oddPrimeInvSum X +
        (3 / 2 : ℝ) * oddPrimeInvSqSum X := by
  unfold sourceEulerExponent
  rw [oddPrimeInvBelow_eq_oddPrimeInvSum_of_lt hXL]
  ring

/-- Remove odd-prime notation from the small-cutoff source exponent. -/
theorem sourceEulerExponent_le_primeInvSum_of_lt
    {L X : ℕ} (hX : 2 ≤ X) (hXL : X < L) :
    sourceEulerExponent L X ≤
      -(5 / 2 : ℝ) * primeInvSum X + 11 / 4 := by
  rw [sourceEulerExponent_eq_of_lt hXL,
    oddPrimeInvSum_eq_primeInvSum_sub_half hX]
  have hsq := oddPrimeInvSqSum_le_one X
  nlinarith

/-- Explicit small-cutoff Mertens envelope for the source product. -/
noncomputable def sourceSmallCutoffMertensEnvelope (X : ℕ) : ℝ :=
  -(5 / 2 : ℝ) * primeInvMertensCenter X +
    (5 / 2 : ℝ) * primeInvMertensError X + 11 / 4

theorem source_localMeanProduct_le_mertens_of_lt
    {L X : ℕ} (hX : 2 ≤ X) (hXL : X < L) :
    (∏ p : oddPrimesUpTo X,
        localWeightMean
          (centeredRetainedFamily (P := oddPrimesUpTo X)
            (sourceQU L) (sourceQV L) (sourceQSum L)) p) ≤
      exp (sourceSmallCutoffMertensEnvelope X) := by
  have hbase :=
    (source_localMeanProduct_le_exp L X).trans
      (exp_le_exp.mpr
        (sourceEulerExponent_le_primeInvSum_of_lt hX hXL))
  have hMX :=
    mul_primeInvSum_le_mertensEnvelope
      hX (-(5 / 2 : ℝ))
  refine hbase.trans ?_
  apply exp_le_exp.mpr
  unfold sourceSmallCutoffMertensEnvelope
  norm_num at hMX ⊢
  linarith

/-- Exact mixed exponent in the `X < L` branch. -/
theorem mixedEulerExponent_eq_of_lt
    {L X : ℕ} {alpha beta s : ℝ} (hXL : X < L) :
    mixedEulerExponent L X alpha beta s =
      -2 * oddPrimeInvSum X +
        2 * oddPrimeInvSqSum X := by
  unfold mixedEulerExponent
  rw [oddPrimeInvBelow_eq_oddPrimeInvSum_of_lt hXL]
  ring

/-- Remove odd-prime notation from the small-cutoff mixed exponent. -/
theorem mixedEulerExponent_le_primeInvSum_of_lt
    {L X : ℕ} {alpha beta s : ℝ}
    (hX : 2 ≤ X) (hXL : X < L) :
    mixedEulerExponent L X alpha beta s ≤
      -2 * primeInvSum X + 3 := by
  rw [mixedEulerExponent_eq_of_lt hXL,
    oddPrimeInvSum_eq_primeInvSum_sub_half hX]
  have hsq := oddPrimeInvSqSum_le_one X
  nlinarith

/-- Explicit small-cutoff Mertens envelope for the mixed product. -/
noncomputable def mixedSmallCutoffMertensEnvelope (X : ℕ) : ℝ :=
  -2 * primeInvMertensCenter X +
    2 * primeInvMertensError X + 3

theorem mixed_localMeanProduct_le_mertens_of_lt
    {L X : ℕ} {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hX : 2 ≤ X) (hXL : X < L) :
    (∏ p : oddPrimesUpTo X,
        localWeightMean
          (crossRetainedFamily (P := oddPrimesUpTo X)
            (mixedQU L alpha) (mixedQW L beta)
            (mixedQLinear L s)) p) ≤
      exp (mixedSmallCutoffMertensEnvelope X) := by
  have hbase :=
    (mixed_localMeanProduct_le_exp
      ha0 ha1 hb0 hb1 hs0 hs1 L X).trans
        (exp_le_exp.mpr
          (mixedEulerExponent_le_primeInvSum_of_lt
            (alpha := alpha) (beta := beta) (s := s) hX hXL))
  have hMX :=
    mul_primeInvSum_le_mertensEnvelope hX (-2)
  refine hbase.trans ?_
  apply exp_le_exp.mpr
  unfold mixedSmallCutoffMertensEnvelope
  norm_num at hMX ⊢
  linarith

end

end Erdos327.Analytic
