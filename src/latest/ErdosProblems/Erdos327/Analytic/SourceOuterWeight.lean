import ErdosProblems.Erdos327.Analytic.CoordinateCounting
import ErdosProblems.Erdos327.Analytic.ThreeFormWeightBridge

/-!
# The score-oriented source weight and the three-form squarefree weight
-/

namespace Erdos327.Analytic

open Finset
open scoped ArithmeticFunction.Omega

noncomputable section

/-- The score orientation `Ω(v) ≤ Ω(u)` splits the `4^{-Ω(u)}` factor
into the two half-power weights used by the source three-form estimate. -/
theorem sourceScoreWeight_le
    {u v : ℕ}
    (hscore :
      ArithmeticFunction.cardFactors v ≤
        ArithmeticFunction.cardFactors u) :
    (1 / 4 : ℝ) ^ ArithmeticFunction.cardFactors u ≤
      (1 / 2 : ℝ) ^ ArithmeticFunction.cardFactors u *
        (1 / 2 : ℝ) ^ ArithmeticFunction.cardFactors v := by
  have hexponent :
      ArithmeticFunction.cardFactors u +
          ArithmeticFunction.cardFactors v ≤
        2 * ArithmeticFunction.cardFactors u := by
    omega
  have hpow :=
    pow_le_pow_of_le_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
      hexponent
  calc
    (1 / 4 : ℝ) ^ ArithmeticFunction.cardFactors u =
        (1 / 2 : ℝ) ^
          (2 * ArithmeticFunction.cardFactors u) := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
        pow_mul]
    _ ≤ (1 / 2 : ℝ) ^
          (ArithmeticFunction.cardFactors u +
            ArithmeticFunction.cardFactors v) :=
      hpow
    _ = (1 / 2 : ℝ) ^ ArithmeticFunction.cardFactors u *
          (1 / 2 : ℝ) ^ ArithmeticFunction.cardFactors v := by
      rw [pow_add]

/-- Every source coordinate's two outer multiplicity factors are bounded
by the finite source squarefree weight. -/
theorem sourceOuterWeight_le_integerWeight
    {L N : ℕ} {A K : ℝ} {q : SourceTriple} (z : ℕ)
    (hq : q ∈ sourceCoordinateSet L N A K) :
    (1 / 4 : ℝ) ^ ArithmeticFunction.cardFactors (sourceU q) *
        (1 / 4 : ℝ) ^
          ArithmeticFunction.cardFactors (sourceU q + sourceV q) ≤
      centeredIntegerWeight (oddPrimesUpTo z)
        (sourceQU L) (sourceQV L) (sourceQSum L)
        (sourceU q) (sourceV q) := by
  have hqData := hq
  rw [sourceCoordinateSet, mem_filter] at hqData
  rcases hqData with
    ⟨hqBox, _hcop, _hv3u, hscore, _hpair, _hexact, _hLsum,
      _hbLower, _hbUpper, hoddU, hoddSum, _hoddD,
      _hrough, _hregular⟩
  rcases mem_product.mp hqBox with ⟨huvBox, _hdBox⟩
  rcases mem_product.mp huvBox with ⟨huBox, hvBox⟩
  have hu0 : sourceU q ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (mem_Icc.mp huBox).1
  have hv0 : sourceV q ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hvBox).1
  have hsum0 : sourceU q + sourceV q ≠ 0 := by omega
  have hscoreWeight := sourceScoreWeight_le hscore
  have hthree :=
    sourceMultiplicityWeight_le_integerWeight
      hu0 hv0 hsum0 hoddU hoddSum (z := z)
  calc
    (1 / 4 : ℝ) ^ ArithmeticFunction.cardFactors (sourceU q) *
          (1 / 4 : ℝ) ^
            ArithmeticFunction.cardFactors (sourceU q + sourceV q)
        ≤ ((1 / 2 : ℝ) ^
              ArithmeticFunction.cardFactors (sourceU q) *
            (1 / 2 : ℝ) ^
              ArithmeticFunction.cardFactors (sourceV q)) *
            (1 / 4 : ℝ) ^
              ArithmeticFunction.cardFactors
                (sourceU q + sourceV q) := by
      gcongr
    _ ≤ centeredIntegerWeight (oddPrimesUpTo z)
          (sourceQU L) (sourceQV L) (sourceQSum L)
          (sourceU q) (sourceV q) := hthree

end

end Erdos327.Analytic
