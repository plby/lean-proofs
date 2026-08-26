import ErdosProblems.Erdos327.Analytic.ThreeFormProductBounds

/-!
# Mixed Euler products and explicit three-form box bounds

This file completes the mixed local-mean product estimate and combines
both product estimates with the finite weighted-sieve cutoff theorem.
-/

namespace Erdos327.Analytic

open Real Finset
open scoped BigOperators

noncomputable section

/-- Multiplying a quantity known within a one-sided error interval by
an arbitrary real coefficient costs the absolute value of that
coefficient times the error. -/
theorem mul_le_center_add_abs_error
    {x center err c : ℝ}
    (hlo : center - err ≤ x) (hhi : x ≤ center)
    (herr : 0 ≤ err) :
    c * x ≤ c * center + |c| * err := by
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
    have h := mul_le_mul_of_nonneg_left hhi hc
    nlinarith [mul_nonneg hc herr]
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    rw [abs_of_nonpos hc']
    have h := mul_le_mul_of_nonpos_left hlo hc'
    nlinarith [mul_nonneg (neg_nonneg.mpr hc') herr]

/-- The quadratic coefficient in the mixed local polynomial is at
most two throughout the unit cube. -/
theorem mixed_quadraticCoefficient_le_two
    {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    2 - alpha - beta - s + alpha * beta * s ≤ 2 := by
  have hbs1 : beta * s ≤ 1 := mul_le_one₀ hb1 hs0 hs1
  have hprod : alpha * beta * s ≤ alpha := by
    rw [mul_assoc]
    exact mul_le_of_le_one_right ha0 hbs1
  linarith

/-- Finite exponent governing the mixed product.  Its two linear
coefficients are exactly `alpha + beta + s - 3` above `L` and
`1 - alpha - beta - s` at the lower cutoff. -/
noncomputable def mixedEulerExponent
    (L X : ℕ) (alpha beta s : ℝ) : ℝ :=
  (alpha + beta + s - 3) * oddPrimeInvSum X +
    (1 - alpha - beta - s) * oddPrimeInvBelow L X +
    2 * oddPrimeInvSqSum X

theorem mixed_localWeightMean_le_exp
    {L X : ℕ} {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (p : oddPrimesUpTo X) :
    localWeightMean
        (crossRetainedFamily (P := oddPrimesUpTo X)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) p ≤
      exp ((alpha + beta + s - 3) / (p : ℝ) +
        (if (p : ℕ) < L then
          (1 - alpha - beta - s) / (p : ℝ) else 0) +
        2 / (p : ℝ) ^ 2) := by
  by_cases hpL : (p : ℕ) < L
  · rw [mixed_localWeightMean_of_lt p hpL]
    simp only [if_pos hpL]
    let t : ℝ :=
      (alpha + beta + s - 3) / (p : ℝ) +
        (1 - alpha - beta - s) / (p : ℝ) +
        2 / (p : ℝ) ^ 2
    have hquad :
        1 / (p : ℝ) ^ 2 ≤ 2 / (p : ℝ) ^ 2 := by
      have hsq : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
      calc
        1 / (p : ℝ) ^ 2 ≤
            1 / (p : ℝ) ^ 2 + 1 / (p : ℝ) ^ 2 :=
          le_add_of_nonneg_right hsq
        _ = 2 / (p : ℝ) ^ 2 := by ring
    calc
      1 - 2 / (p : ℝ) + 1 / (p : ℝ) ^ 2 ≤
          1 - 2 / (p : ℝ) + 2 / (p : ℝ) ^ 2 := by
        linarith
      _ = 1 + t := by
        dsimp [t]
        ring
      _ ≤ exp t := by
        simpa [add_comm] using add_one_le_exp t
  · have hLp : L ≤ (p : ℕ) := Nat.le_of_not_gt hpL
    rw [mixed_localWeightMean_of_le p hLp]
    simp only [if_neg hpL, add_zero]
    let c : ℝ :=
      2 - alpha - beta - s + alpha * beta * s
    let t : ℝ :=
      (alpha + beta + s - 3) / (p : ℝ) +
        2 / (p : ℝ) ^ 2
    have hc : c ≤ 2 := by
      dsimp [c]
      exact mixed_quadraticCoefficient_le_two
        ha0 hb0 hb1 hs0 hs1
    have hsq : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
    have hquad :
        c / (p : ℝ) ^ 2 ≤ 2 / (p : ℝ) ^ 2 := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hc hsq
    calc
      1 + (alpha + beta + s - 3) / (p : ℝ) +
          (2 - alpha - beta - s + alpha * beta * s) /
            (p : ℝ) ^ 2 ≤
        1 + (alpha + beta + s - 3) / (p : ℝ) +
          2 / (p : ℝ) ^ 2 := by
            dsimp [c] at hquad
            linarith
      _ = 1 + t := by
        dsimp [t]
        ring
      _ ≤ exp t := by
        simpa [add_comm] using add_one_le_exp t

/-- Assemble the mixed pointwise bounds into a finite Euler product. -/
theorem mixed_localMeanProduct_le_exp
    {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (L X : ℕ) :
    (∏ p : oddPrimesUpTo X,
        localWeightMean
          (crossRetainedFamily (P := oddPrimesUpTo X)
            (mixedQU L alpha) (mixedQW L beta)
            (mixedQLinear L s)) p) ≤
      exp (mixedEulerExponent L X alpha beta s) := by
  let w := crossRetainedFamily (P := oddPrimesUpTo X)
    (mixedQU L alpha) (mixedQW L beta) (mixedQLinear L s)
  have hprime : ∀ p ∈ oddPrimesUpTo X, p.Prime :=
    fun p hp ↦ (mem_oddPrimesUpTo.mp hp).1
  have hodd : ∀ p ∈ oddPrimesUpTo X, p ≠ 2 :=
    fun p hp ↦ (mem_oddPrimesUpTo.mp hp).2.2
  have hw0 : ∀ (p : oddPrimesUpTo X) u, 0 ≤ w p u := by
    intro p u
    exact (crossLocalWeight_nonneg_le_one
      (mixedQU L alpha p) (mixedQW L beta p)
      (mixedQLinear L s p)
      (mixedQU_nonneg_le_one ha0 ha1 L p).1
      (mixedQU_nonneg_le_one ha0 ha1 L p).2
      (mixedQW_nonneg_le_one hb0 hb1 L p).1
      (mixedQW_nonneg_le_one hb0 hb1 L p).2
      (mixedQLinear_nonneg_le_one hs0 hs1 L p).1
      (mixedQLinear_nonneg_le_one hs0 hs1 L p).2 u).1
  calc
    (∏ p : oddPrimesUpTo X, localWeightMean w p) ≤
      ∏ p : oddPrimesUpTo X,
        exp ((alpha + beta + s - 3) / (p : ℝ) +
          (if (p : ℕ) < L then
            (1 - alpha - beta - s) / (p : ℝ) else 0) +
          2 / (p : ℝ) ^ 2) := by
      apply prod_le_prod
      · intro p _
        exact localWeightMean_nonneg w hw0 p
      · intro p _
        exact mixed_localWeightMean_le_exp
          ha0 hb0 hb1 hs0 hs1 p
    _ = exp (∑ p : oddPrimesUpTo X,
        ((alpha + beta + s - 3) / (p : ℝ) +
          (if (p : ℕ) < L then
            (1 - alpha - beta - s) / (p : ℝ) else 0) +
          2 / (p : ℝ) ^ 2)) := by
      rw [exp_sum]
    _ = exp (mixedEulerExponent L X alpha beta s) := by
      congr 1
      rw [show
        (∑ p : oddPrimesUpTo X,
          ((alpha + beta + s - 3) / (p : ℝ) +
            (if (p : ℕ) < L then
              (1 - alpha - beta - s) / (p : ℝ) else 0) +
            2 / (p : ℝ) ^ 2)) =
          ∑ p ∈ oddPrimesUpTo X,
            ((alpha + beta + s - 3) / (p : ℝ) +
              (if p < L then
                (1 - alpha - beta - s) / (p : ℝ) else 0) +
              2 / (p : ℝ) ^ 2) by
        simpa using sum_coe_sort (oddPrimesUpTo X)
          (fun p : ℕ ↦
            ((alpha + beta + s - 3) / (p : ℝ) +
              (if p < L then
                (1 - alpha - beta - s) / (p : ℝ) else 0) +
              2 / (p : ℝ) ^ 2))]
      unfold mixedEulerExponent oddPrimeInvSum oddPrimeInvBelow
        oddPrimeInvSqSum
      rw [sum_add_distrib, sum_add_distrib, ← sum_filter]
      simp_rw [div_eq_mul_inv]
      rw [← mul_sum, ← mul_sum, ← mul_sum]
      ring_nf

/-- Replace the odd-prime sums in the mixed exponent by the full
reciprocal-prime sums.  The endpoint uncertainty has the sign-uniform
cost `|1-alpha-beta-s|/L`. -/
theorem mixedEulerExponent_le_primeInvSum
    {L X : ℕ} {alpha beta s : ℝ}
    (hL : 2 ≤ L) (hLX : L ≤ X) :
    mixedEulerExponent L X alpha beta s ≤
      (alpha + beta + s - 3) * primeInvSum X +
        (1 - alpha - beta - s) * primeInvSum L +
        3 + |1 - alpha - beta - s| / (L : ℝ) := by
  have hX : 2 ≤ X := hL.trans hLX
  have hall := oddPrimeInvSum_eq_primeInvSum_sub_half hX
  have hlowLo :=
    primeInvSum_sub_half_sub_inv_le_oddPrimeInvBelow hL hLX
  have hlowHi := oddPrimeInvBelow_le_oddPrimeInvSum
    (L := L) (X := X)
  rw [oddPrimeInvSum_eq_primeInvSum_sub_half hL] at hlowHi
  have hband := mul_le_center_add_abs_error
    hlowLo hlowHi (show 0 ≤ 1 / (L : ℝ) by positivity)
    (c := 1 - alpha - beta - s)
  have hsq := oddPrimeInvSqSum_le_one X
  unfold mixedEulerExponent
  rw [hall]
  ring_nf at hband ⊢
  nlinarith

theorem mixed_localMeanProduct_le_exp_primeInvSum
    {L X : ℕ} {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hL : 2 ≤ L) (hLX : L ≤ X) :
    (∏ p : oddPrimesUpTo X,
        localWeightMean
          (crossRetainedFamily (P := oddPrimesUpTo X)
            (mixedQU L alpha) (mixedQW L beta)
            (mixedQLinear L s)) p) ≤
      exp ((alpha + beta + s - 3) * primeInvSum X +
        (1 - alpha - beta - s) * primeInvSum L +
        3 + |1 - alpha - beta - s| / (L : ℝ)) := by
  exact (mixed_localMeanProduct_le_exp
    ha0 ha1 hb0 hb1 hs0 hs1 L X).trans
      (exp_le_exp.mpr (mixedEulerExponent_le_primeInvSum hL hLX))

/-- Explicit sign-uniform Mertens envelope for the mixed product. -/
noncomputable def mixedMertensEnvelope
    (L X : ℕ) (alpha beta s : ℝ) : ℝ :=
  (alpha + beta + s - 3) * primeInvMertensCenter X +
    |alpha + beta + s - 3| * primeInvMertensError X +
    (1 - alpha - beta - s) * primeInvMertensCenter L +
    |1 - alpha - beta - s| * primeInvMertensError L +
    3 + |1 - alpha - beta - s| / (L : ℝ)

/-- The mixed product has logarithmic exponents
`alpha+beta+s-3` at `X` and `1-alpha-beta-s` at `L`. -/
theorem mixed_localMeanProduct_le_mertens
    {L X : ℕ} {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hL : 2 ≤ L) (hLX : L ≤ X) :
    (∏ p : oddPrimesUpTo X,
        localWeightMean
          (crossRetainedFamily (P := oddPrimesUpTo X)
            (mixedQU L alpha) (mixedQW L beta)
            (mixedQLinear L s)) p) ≤
      exp (mixedMertensEnvelope L X alpha beta s) := by
  have hX : 2 ≤ X := hL.trans hLX
  have hMX := mul_primeInvSum_le_mertensEnvelope hX
    (alpha + beta + s - 3)
  have hML := mul_primeInvSum_le_mertensEnvelope hL
    (1 - alpha - beta - s)
  refine (mixed_localMeanProduct_le_exp_primeInvSum
    ha0 ha1 hb0 hb1 hs0 hs1 hL hLX).trans ?_
  apply exp_le_exp.mpr
  unfold mixedMertensEnvelope
  linarith

/-- Explicit source three-form box bound, including the factorial
Bonferroni tail and the closed subset-boundary term. -/
theorem source_threeFormBoxSum_le
    {L z X R : ℕ}
    (hL : 2 ≤ L) (hLz : L ≤ z)
    (hzX : z ^ (2 * R) ≤ X) :
    finiteWeightBoxSum
        (centeredRetainedFamily (P := oddPrimesUpTo z)
          (sourceQU L) (sourceQV L) (sourceQSum L)) X ≤
      8 * (X : ℝ) ^ 2 * exp (sourceMertensEnvelope L z) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        10 * (X : ℝ) * (2 : ℝ) ^ (oddPrimesUpTo z).card *
          (3 : ℝ) ^ (2 * R) := by
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
    finiteWeightBoxSum_le_primeInvSum_add_closed_boundary_of_pow_le
      (P := oddPrimesUpTo z) (z := z)
      hprime w ell hcomplement hell0 hell1 hsupport
      hPz hmean hz X R hzX
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

/-- Explicit mixed three-form box bound, with the requested mixed
Mertens exponents and the same factorial and boundary errors. -/
theorem mixed_threeFormBoxSum_le
    {L z X R : ℕ} {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hL : 2 ≤ L) (hLz : L ≤ z)
    (hzX : z ^ (2 * R) ≤ X) :
    finiteWeightBoxSum
        (crossRetainedFamily (P := oddPrimesUpTo z)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) X ≤
      8 * (X : ℝ) ^ 2 *
          exp (mixedMertensEnvelope L z alpha beta s) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        10 * (X : ℝ) * (2 : ℝ) ^ (oddPrimesUpTo z).card *
          (3 : ℝ) ^ (2 * R) := by
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
    finiteWeightBoxSum_le_primeInvSum_add_closed_boundary_of_pow_le
      (P := oddPrimesUpTo z) (z := z)
      hprime w ell hcomplement hell0 hell1 hsupport
      hPz hmean hz X R hzX
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

end

end Erdos327.Analytic
