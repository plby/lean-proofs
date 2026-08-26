import ErdosProblems.Erdos327.Analytic.MixedIndicator
import ErdosProblems.Erdos327.Analytic.ThreeFormWeightBridge

/-!
# The mixed indicator's outer weight and the finite three-form weight
-/

namespace Erdos327.Analytic

open Finset
open scoped ArithmeticFunction.Omega

noncomputable section

/-- If the finite sieve cutoff lies below the common linear form, the three
outer factors in the mixed indicator are bounded by the finite mixed
squarefree weight.  The remaining `t`-factor is deliberately not included:
it is handled by the one-variable residual estimate. -/
theorem mixedOuterWeight_le_integerWeight
    {L N : ℕ} {Ab Kb Ao Ko qb qo : ℝ} {q : MixedTriple} {z : ℕ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hzx : z ≤ mixedLinear q)
    (hq : q ∈ mixedCoordinateSet L N Ab Kb Ao Ko) :
    (1 / qb) ^ ArithmeticFunction.cardFactors (mixedU q) *
          (1 / qo) ^
            primeFactorCountBetween L (mixedLinear q) (mixedW q) *
          (1 / (qb * qo)) ^
            ArithmeticFunction.cardFactors (mixedLinear q) ≤
      crossIntegerWeight (oddPrimesUpTo z)
        (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
        (mixedQLinear L (1 / (qb * qo)))
        (mixedU q) (mixedW q) := by
  have hqData := hq
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases hqData with
    ⟨hqBox, _hcop, _hw6u, _hx8u, _haHost, _hbLower,
      _hbUpper, _htRough, huRough, hxRough, _htOdd,
      _huOdd, _hwOdd, _hxOdd, _hbRegular, _haRegular⟩
  rcases mem_product.mp hqBox with ⟨htuBox, hwBox⟩
  rcases mem_product.mp htuBox with ⟨_htBox, huBox⟩
  have hu0 : mixedU q ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (mem_Icc.mp huBox).1
  have hw0 : mixedW q ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hwBox).1
  have hx0 : mixedLinear q ≠ 0 := by
    simp only [mixedLinear]
    omega
  have hqb0 : 0 < qb := zero_lt_one.trans hqb
  have hqo0 : 0 < qo := zero_lt_one.trans hqo
  have hqbqo0 : 0 < qb * qo := mul_pos hqb0 hqo0
  have ha0 : 0 ≤ (1 / qb : ℝ) := by positivity
  have ha1 : (1 / qb : ℝ) ≤ 1 :=
    (div_le_one₀ hqb0).mpr hqb.le
  have hb0 : 0 ≤ (1 / qo : ℝ) := by positivity
  have hb1 : (1 / qo : ℝ) ≤ 1 :=
    (div_le_one₀ hqo0).mpr hqo.le
  have hs0 : 0 ≤ (1 / (qb * qo) : ℝ) := by positivity
  have hprodOne : 1 ≤ qb * qo := by
    nlinarith [mul_pos (sub_pos.mpr hqb) (sub_pos.mpr hqo)]
  have hs1 : (1 / (qb * qo) : ℝ) ≤ 1 :=
    (div_le_one₀ hqbqo0).mpr hprodOne
  have hU :
      (1 / qb) ^ ArithmeticFunction.cardFactors (mixedU q) ≤
        (1 / qb) ^
          primeFactorCountBetween L z (mixedU q) :=
    pow_cardFactors_le_pow_primeFactorCountBetween
      ha0 ha1 L z (mixedU q)
  have hW :
      (1 / qo) ^
          primeFactorCountBetween L (mixedLinear q) (mixedW q) ≤
        (1 / qo) ^
          primeFactorCountBetween L z (mixedW q) :=
    pow_le_pow_of_le_one hb0 hb1
      (primeFactorCountBetween_mono_right L (mixedW q) hzx)
  have hX :
      (1 / (qb * qo)) ^
          ArithmeticFunction.cardFactors (mixedLinear q) ≤
        (1 / (qb * qo)) ^
          primeFactorCountBetween L z (mixedLinear q) :=
    pow_cardFactors_le_pow_primeFactorCountBetween
      hs0 hs1 L z (mixedLinear q)
  have hlocalized :=
    mixedMultiplicityWeight_le_oddIntegerWeight
      hL hu0 hw0 hx0 huRough hxRough
      ha0 ha1 hb0 hb1 hs0 hs1
      (z := z)
  calc
    (1 / qb) ^ ArithmeticFunction.cardFactors (mixedU q) *
          (1 / qo) ^
            primeFactorCountBetween L (mixedLinear q) (mixedW q) *
          (1 / (qb * qo)) ^
            ArithmeticFunction.cardFactors (mixedLinear q)
        ≤ (1 / qb) ^
              primeFactorCountBetween L z (mixedU q) *
            (1 / qo) ^
              primeFactorCountBetween L z (mixedW q) *
            (1 / (qb * qo)) ^
              primeFactorCountBetween L z (mixedLinear q) := by
      exact mul_le_mul
        (mul_le_mul hU hW (by positivity) (by positivity))
        hX (by positivity) (by positivity)
    _ ≤ crossIntegerWeight (oddPrimesUpTo z)
          (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
          (mixedQLinear L (1 / (qb * qo)))
          (mixedU q) (mixedW q) :=
      hlocalized

end

end Erdos327.Analytic
