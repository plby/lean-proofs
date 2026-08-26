import ErdosProblems.Erdos327.Analytic.ThreeFormBoxBounds
import ErdosProblems.Erdos327.Analytic.WeightedLinearSieveBoundarySharp
import ErdosProblems.Erdos327.Analytic.FactorialTailBound

/-!
# Three-form box estimates with a polynomial boundary

These are the source and mixed specializations of the truncated-degree
finite-sieve boundary.  Unlike the earlier closed-boundary estimates, they
do not require charging every subset of the prime set and therefore have no
factor exponential in the number of primes.
-/

namespace Erdos327.Analytic

open Real Finset
open scoped BigOperators

noncomputable section

/-- The source three-form box estimate with the degree-truncated polynomial
boundary. -/
theorem source_threeFormBoxSum_le_sharp
    {L z X R : ℕ}
    (hL : 2 ≤ L) (hLz : L ≤ z) :
    finiteWeightBoxSum
        (centeredRetainedFamily (P := oddPrimesUpTo z)
          (sourceQU L) (sourceQV L) (sourceQSum L)) X ≤
      8 * (X : ℝ) ^ 2 * exp (sourceMertensEnvelope L z) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ((2 * R + 1 : ℕ) : ℝ) *
          (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  let w := centeredRetainedFamily (P := oddPrimesUpTo z)
    (sourceQU L) (sourceQV L) (sourceQSum L)
  let ell := centeredLossFamily (P := oddPrimesUpTo z)
    (sourceQU L) (sourceQV L) (sourceQSum L)
  have hprime : ∀ p ∈ oddPrimesUpTo z, p.Prime :=
    fun p hp ↦ (mem_oddPrimesUpTo.mp hp).1
  have hPz : oddPrimesUpTo z ⊆ Nat.primesLE z :=
    fun _ hp ↦ mem_of_mem_erase hp
  have hz : 1 ≤ z := by omega
  have hlocal (p : oddPrimesUpTo z)
      (u : ZMod (p : ℕ) × ZMod (p : ℕ)) :
      0 ≤ w p u ∧ w p u ≤ 1 := by
    dsimp [w]
    exact centeredLocalWeight_nonneg_le_one
      (sourceQU L p) (sourceQV L p) (sourceQSum L p)
      (sourceQU_nonneg_le_one L p).1
      (sourceQU_nonneg_le_one L p).2
      (sourceQV_nonneg_le_one L p).1
      (sourceQV_nonneg_le_one L p).2
      (sourceQSum_nonneg_le_one L p).1
      (sourceQSum_nonneg_le_one L p).2 u
  have hcomplement : ∀ (p : oddPrimesUpTo z) u,
      w p u + ell p u = 1 := by
    intro p u
    simp [w, ell, centeredLossFamily]
  have hell0 : ∀ (p : oddPrimesUpTo z) u, 0 ≤ ell p u :=
    fun p u ↦ sub_nonneg.mpr (hlocal p u).2
  have hell1 : ∀ (p : oddPrimesUpTo z) u, ell p u ≤ 1 :=
    fun p u ↦ sub_le_self _ (hlocal p u).1
  have hsupport : ∀ p : oddPrimesUpTo z,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤
        3 * (p : ℕ) := by
    intro p
    dsimp [ell]
    exact centeredLossFamily_support_card_le
      (sourceQU L) (sourceQV L) (sourceQSum L) p
  have hmean : ∀ p : oddPrimesUpTo z,
      localLossMean ell p ≤ 3 / (p : ℝ) :=
    localLossMean_le_three_div hprime ell hell1 hsupport
  have hbase :=
    finiteWeightBoxSum_le_primeInvSum_add_truncated_boundary
      (P := oddPrimesUpTo z) (z := z)
      hprime w ell hcomplement hell0 hell1 hsupport
      hPz hmean hz X R
  have hproduct :
      (∏ p : oddPrimesUpTo z, localWeightMean w p) ≤
        exp (sourceMertensEnvelope L z) := by
    dsimp [w]
    exact source_localMeanProduct_le_mertens hL hLz
  have hproductScaled :
      8 * (X : ℝ) ^ 2 *
          (∏ p : oddPrimesUpTo z, localWeightMean w p) ≤
        8 * (X : ℝ) ^ 2 *
          exp (sourceMertensEnvelope L z) :=
    mul_le_mul_of_nonneg_left hproduct (by positivity)
  change finiteWeightBoxSum w X ≤ _
  exact hbase.trans
    (add_le_add (add_le_add hproductScaled le_rfl) le_rfl)

/-- The mixed three-form box estimate with the degree-truncated polynomial
boundary. -/
theorem mixed_threeFormBoxSum_le_sharp
    {L z X R : ℕ} {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hL : 2 ≤ L) (hLz : L ≤ z) :
    finiteWeightBoxSum
        (crossRetainedFamily (P := oddPrimesUpTo z)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) X ≤
      8 * (X : ℝ) ^ 2 *
          exp (mixedMertensEnvelope L z alpha beta s) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ((2 * R + 1 : ℕ) : ℝ) *
          (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  let w := crossRetainedFamily (P := oddPrimesUpTo z)
    (mixedQU L alpha) (mixedQW L beta) (mixedQLinear L s)
  let ell := crossLossFamily (P := oddPrimesUpTo z)
    (mixedQU L alpha) (mixedQW L beta) (mixedQLinear L s)
  have hprime : ∀ p ∈ oddPrimesUpTo z, p.Prime :=
    fun p hp ↦ (mem_oddPrimesUpTo.mp hp).1
  have hodd : ∀ p ∈ oddPrimesUpTo z, p ≠ 2 :=
    fun p hp ↦ (mem_oddPrimesUpTo.mp hp).2.2
  have hPz : oddPrimesUpTo z ⊆ Nat.primesLE z :=
    fun _ hp ↦ mem_of_mem_erase hp
  have hz : 1 ≤ z := by omega
  have hlocal (p : oddPrimesUpTo z)
      (u : ZMod (p : ℕ) × ZMod (p : ℕ)) :
      0 ≤ w p u ∧ w p u ≤ 1 := by
    dsimp [w]
    exact crossLocalWeight_nonneg_le_one
      (mixedQU L alpha p) (mixedQW L beta p)
      (mixedQLinear L s p)
      (mixedQU_nonneg_le_one ha0 ha1 L p).1
      (mixedQU_nonneg_le_one ha0 ha1 L p).2
      (mixedQW_nonneg_le_one hb0 hb1 L p).1
      (mixedQW_nonneg_le_one hb0 hb1 L p).2
      (mixedQLinear_nonneg_le_one hs0 hs1 L p).1
      (mixedQLinear_nonneg_le_one hs0 hs1 L p).2 u
  have hcomplement : ∀ (p : oddPrimesUpTo z) u,
      w p u + ell p u = 1 := by
    intro p u
    simp [w, ell, crossLossFamily]
  have hell0 : ∀ (p : oddPrimesUpTo z) u, 0 ≤ ell p u :=
    fun p u ↦ sub_nonneg.mpr (hlocal p u).2
  have hell1 : ∀ (p : oddPrimesUpTo z) u, ell p u ≤ 1 :=
    fun p u ↦ sub_le_self _ (hlocal p u).1
  have hsupport : ∀ p : oddPrimesUpTo z,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤
        3 * (p : ℕ) := by
    intro p
    dsimp [ell]
    exact crossLossFamily_support_card_le hprime hodd
      (mixedQU L alpha) (mixedQW L beta)
      (mixedQLinear L s) p
  have hmean : ∀ p : oddPrimesUpTo z,
      localLossMean ell p ≤ 3 / (p : ℝ) :=
    localLossMean_le_three_div hprime ell hell1 hsupport
  have hbase :=
    finiteWeightBoxSum_le_primeInvSum_add_truncated_boundary
      (P := oddPrimesUpTo z) (z := z)
      hprime w ell hcomplement hell0 hell1 hsupport
      hPz hmean hz X R
  have hproduct :
      (∏ p : oddPrimesUpTo z, localWeightMean w p) ≤
        exp (mixedMertensEnvelope L z alpha beta s) := by
    dsimp [w]
    exact mixed_localMeanProduct_le_mertens
      ha0 ha1 hb0 hb1 hs0 hs1 hL hLz
  have hproductScaled :
      8 * (X : ℝ) ^ 2 *
          (∏ p : oddPrimesUpTo z, localWeightMean w p) ≤
        8 * (X : ℝ) ^ 2 *
          exp (mixedMertensEnvelope L z alpha beta s) :=
    mul_le_mul_of_nonneg_left hproduct (by positivity)
  change finiteWeightBoxSum w X ≤ _
  exact hbase.trans
    (add_le_add (add_le_add hproductScaled le_rfl) le_rfl)

/-- Source box bound after converting the factorial error to the geometric
tail `4⁻ᴿ`. -/
theorem source_threeFormBoxSum_le_geometricTail
    {L z X R : ℕ}
    (hL : 2 ≤ L) (hLz : L ≤ z) (hR : 1 ≤ R)
    (hmuR : 3 * primeInvSum z ≤ R)
    (hmuSq : (3 * primeInvSum z) ^ 2 ≤ (R : ℝ) / 4) :
    finiteWeightBoxSum
        (centeredRetainedFamily (P := oddPrimesUpTo z)
          (sourceQU L) (sourceQV L) (sourceQSum L)) X ≤
      8 * (X : ℝ) ^ 2 * exp (sourceMertensEnvelope L z) +
        8 * (X : ℝ) ^ 2 * (1 / 4 : ℝ) ^ R +
        ((2 * R + 1 : ℕ) : ℝ) *
          (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  have htail :=
    pow_div_factorial_two_mul_add_one_le
      (μ := 3 * primeInvSum z) (R := R)
      (mul_nonneg (by norm_num) (primeInvSum_nonneg z))
      hR hmuR hmuSq
  have htailScaled :
      8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) ≤
        8 * (X : ℝ) ^ 2 * (1 / 4 : ℝ) ^ R :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  exact (source_threeFormBoxSum_le_sharp hL hLz).trans
    (add_le_add (add_le_add le_rfl htailScaled) le_rfl)

/-- Mixed box bound after converting the factorial error to the geometric
tail `4⁻ᴿ`. -/
theorem mixed_threeFormBoxSum_le_geometricTail
    {L z X R : ℕ} {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hL : 2 ≤ L) (hLz : L ≤ z) (hR : 1 ≤ R)
    (hmuR : 3 * primeInvSum z ≤ R)
    (hmuSq : (3 * primeInvSum z) ^ 2 ≤ (R : ℝ) / 4) :
    finiteWeightBoxSum
        (crossRetainedFamily (P := oddPrimesUpTo z)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) X ≤
      8 * (X : ℝ) ^ 2 *
          exp (mixedMertensEnvelope L z alpha beta s) +
        8 * (X : ℝ) ^ 2 * (1 / 4 : ℝ) ^ R +
        ((2 * R + 1 : ℕ) : ℝ) *
          (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  have htail :=
    pow_div_factorial_two_mul_add_one_le
      (μ := 3 * primeInvSum z) (R := R)
      (mul_nonneg (by norm_num) (primeInvSum_nonneg z))
      hR hmuR hmuSq
  have htailScaled :
      8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) ≤
        8 * (X : ℝ) ^ 2 * (1 / 4 : ℝ) ^ R :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  exact (mixed_threeFormBoxSum_le_sharp
    ha0 ha1 hb0 hb1 hs0 hs1 hL hLz).trans
      (add_le_add (add_le_add le_rfl htailScaled) le_rfl)

end

end Erdos327.Analytic
