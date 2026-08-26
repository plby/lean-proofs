import ErdosProblems.Erdos327.Analytic.CoordinateCounting
import ErdosProblems.Erdos327.Analytic.FactorCounts

/-!
# The mixed-coordinate regularity indicator

This file combines the two endpoint regularity budgets for a mixed
coordinate `((t,u),w)`.  At the common cutoff `x = 2u+w`, the source
endpoint contributes the localized factor counts of `t`, `u`, and `x`,
while the odd endpoint contributes those of `t`, `w`, and `x`.
Factoring the resulting exponential gives the four weights used by the
mixed three-form estimate.
-/

namespace Erdos327.Analytic

open Finset Real
open scoped ArithmeticFunction.Omega

noncomputable section

/-- A nontrivial rough integer lies above its roughness cutoff. -/
theorem cutoff_le_of_rough
    {L n : ℕ} (hn : 2 ≤ n) (hrough : Rough L n) :
    L ≤ n := by
  obtain ⟨p, hpPrime, hpDvd⟩ :=
    Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hpL : L ≤ p := by
    by_contra hnot
    exact hrough p hpPrime (Nat.lt_of_not_ge hnot) hpDvd
  exact hpL.trans (Nat.le_of_dvd (by omega) hpDvd)

/-- The source-endpoint localized factor count is the sum of the
`t`, `u`, and `2u+w` counts.  Roughness turns the latter two into full
factor counts at the common cutoff. -/
theorem mixed_source_factorCount_eq
    {L N : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple}
    (hq : q ∈ mixedCoordinateSet L N Ab Kb Ao Ko) :
    primeFactorCountBetween L (mixedLinear q) (mixedT q) +
          ArithmeticFunction.cardFactors (mixedU q) +
          ArithmeticFunction.cardFactors (mixedLinear q) =
      primeFactorCountBetween L (mixedLinear q)
        (mixedSourceVertex q) := by
  have hqData := hq
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases hqData with
    ⟨hqBox, _hcop, _hw6u, _hx8u, _haHost, _hbLower,
      _hbUpper, htRough, huRough, hxRough, _htOdd,
      _huOdd, _hwOdd, _hxOdd, _hbRegular, _haRegular⟩
  rcases mem_product.mp hqBox with ⟨htuBox, hwBox⟩
  rcases mem_product.mp htuBox with ⟨htBox, huBox⟩
  have ht0 : 0 < mixedT q := (mem_Icc.mp htBox).1
  have hu0 : 0 < mixedU q := (mem_Icc.mp huBox).1
  have hw0 : 0 < mixedW q := (mem_Icc.mp hwBox).1
  have hx0 : 0 < mixedLinear q := by
    simp only [mixedLinear]
    omega
  have huLeX : mixedU q ≤ mixedLinear q := by
    simp only [mixedLinear]
    omega
  have huCount :
      primeFactorCountBetween L (mixedLinear q) (mixedU q) =
        ArithmeticFunction.cardFactors (mixedU q) :=
    primeFactorCountBetween_eq_cardFactors_of_rough
      hu0 huLeX huRough
  have hxCount :
      primeFactorCountBetween L (mixedLinear q) (mixedLinear q) =
        ArithmeticFunction.cardFactors (mixedLinear q) :=
    primeFactorCountBetween_eq_cardFactors_of_rough
      hx0 le_rfl hxRough
  rw [← huCount, ← hxCount]
  unfold mixedSourceVertex
  rw [primeFactorCountBetween_mul
    (Nat.mul_ne_zero ht0.ne' hu0.ne') hx0.ne',
    primeFactorCountBetween_mul ht0.ne' hu0.ne']

/-- The odd-endpoint localized factor count is the sum of the `t`, `w`,
and `2u+w` counts.  Only the last count is replaced by a full count;
`w` need not itself be rough. -/
theorem mixed_odd_factorCount_eq
    {L N : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple}
    (hq : q ∈ mixedCoordinateSet L N Ab Kb Ao Ko) :
    primeFactorCountBetween L (mixedLinear q) (mixedT q) +
          primeFactorCountBetween L (mixedLinear q) (mixedW q) +
          ArithmeticFunction.cardFactors (mixedLinear q) =
      primeFactorCountBetween L (mixedLinear q)
        (mixedOddVertex q) := by
  have hqData := hq
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases hqData with
    ⟨hqBox, _hcop, _hw6u, _hx8u, _haHost, _hbLower,
      _hbUpper, _htRough, _huRough, hxRough, _htOdd,
      _huOdd, _hwOdd, _hxOdd, _hbRegular, _haRegular⟩
  rcases mem_product.mp hqBox with ⟨htuBox, hwBox⟩
  rcases mem_product.mp htuBox with ⟨htBox, _huBox⟩
  have ht0 : 0 < mixedT q := (mem_Icc.mp htBox).1
  have hw0 : 0 < mixedW q := (mem_Icc.mp hwBox).1
  have hx0 : 0 < mixedLinear q := by
    simp only [mixedLinear]
    have hu0 : 0 < mixedU q := (mem_Icc.mp _huBox).1
    omega
  have hxCount :
      primeFactorCountBetween L (mixedLinear q) (mixedLinear q) =
        ArithmeticFunction.cardFactors (mixedLinear q) :=
    primeFactorCountBetween_eq_cardFactors_of_rough
      hx0 le_rfl hxRough
  rw [← hxCount]
  unfold mixedOddVertex
  rw [primeFactorCountBetween_mul
    (Nat.mul_ne_zero ht0.ne' hw0.ne') hx0.ne',
    primeFactorCountBetween_mul ht0.ne' hw0.ne']

/-- Source regularity at `x = 2u+w`, expressed in the three factor
counts appearing in the mixed weight. -/
theorem mixed_source_factorCount_real_le_regularity
    {L N : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple}
    (hq : q ∈ mixedCoordinateSet L N Ab Kb Ao Ko) :
    ((primeFactorCountBetween L (mixedLinear q) (mixedT q) +
        ArithmeticFunction.cardFactors (mixedU q) +
        ArithmeticFunction.cardFactors (mixedLinear q) : ℕ) : ℝ) ≤
      Ab * log (log (mixedLinear q) / log L) + Kb := by
  have hqData := hq
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases hqData.2 with
    ⟨_hcop, _hw6u, _hx8u, _haHost, _hbLower, _hbUpper,
      _htRough, _huRough, hxRough, _htOdd, _huOdd, _hwOdd,
      _hxOdd, hbRegular, _haRegular⟩
  have hu0 : 0 < mixedU q := by
    rcases mem_product.mp hqData.1 with ⟨htuBox, _hwBox⟩
    exact (mem_Icc.mp (mem_product.mp htuBox).2).1
  have hw0 : 0 < mixedW q := by
    rcases mem_product.mp hqData.1 with ⟨_htuBox, hwBox⟩
    exact (mem_Icc.mp hwBox).1
  have hx2 : 2 ≤ mixedLinear q := by
    simp only [mixedLinear]
    omega
  have hLx : L ≤ mixedLinear q :=
    cutoff_le_of_rough hx2 hxRough
  have hregular :=
    hbRegular (mixedLinear q) hLx
  rw [mixed_source_factorCount_eq hq]
  exact hregular

/-- Odd-endpoint regularity at `x = 2u+w`, expressed in the three factor
counts appearing in the mixed weight. -/
theorem mixed_odd_factorCount_real_le_regularity
    {L N : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple}
    (hq : q ∈ mixedCoordinateSet L N Ab Kb Ao Ko) :
    ((primeFactorCountBetween L (mixedLinear q) (mixedT q) +
        primeFactorCountBetween L (mixedLinear q) (mixedW q) +
        ArithmeticFunction.cardFactors (mixedLinear q) : ℕ) : ℝ) ≤
      Ao * log (log (mixedLinear q) / log L) + Ko := by
  have hqData := hq
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases hqData.2 with
    ⟨_hcop, _hw6u, _hx8u, _haHost, _hbLower, _hbUpper,
      _htRough, _huRough, hxRough, _htOdd, _huOdd, _hwOdd,
      _hxOdd, _hbRegular, haRegular⟩
  have hu0 : 0 < mixedU q := by
    rcases mem_product.mp hqData.1 with ⟨htuBox, _hwBox⟩
    exact (mem_Icc.mp (mem_product.mp htuBox).2).1
  have hw0 : 0 < mixedW q := by
    rcases mem_product.mp hqData.1 with ⟨_htuBox, hwBox⟩
    exact (mem_Icc.mp hwBox).1
  have hx2 : 2 ≤ mixedLinear q := by
    simp only [mixedLinear]
    omega
  have hLx : L ≤ mixedLinear q :=
    cutoff_le_of_rough hx2 hxRough
  have hregular :=
    haRegular (mixedLinear q) hLx
  rw [mixed_odd_factorCount_eq hq]
  exact hregular

/-- Lean-friendly exponential form of the joint mixed indicator. -/
theorem one_le_mixedIndicatorExp
    {L N : ℕ} {Ab Kb Ao Ko qb qo : ℝ} {q : MixedTriple}
    (hqb : 1 < qb) (hqo : 1 < qo)
    (hq : q ∈ mixedCoordinateSet L N Ab Kb Ao Ko) :
    (1 : ℝ) ≤
      exp (
        log qb *
          (Ab * log (log (mixedLinear q) / log L) + Kb -
            ((primeFactorCountBetween L (mixedLinear q) (mixedT q) +
              ArithmeticFunction.cardFactors (mixedU q) +
              ArithmeticFunction.cardFactors
                (mixedLinear q) : ℕ) : ℝ)) +
        log qo *
          (Ao * log (log (mixedLinear q) / log L) + Ko -
            ((primeFactorCountBetween L (mixedLinear q) (mixedT q) +
              primeFactorCountBetween L (mixedLinear q) (mixedW q) +
              ArithmeticFunction.cardFactors
                (mixedLinear q) : ℕ) : ℝ))) := by
  apply one_le_exp
  exact add_nonneg
    (mul_nonneg (log_pos hqb).le
      (sub_nonneg.mpr
        (mixed_source_factorCount_real_le_regularity hq)))
    (mul_nonneg (log_pos hqo).le
      (sub_nonneg.mpr
        (mixed_odd_factorCount_real_le_regularity hq)))

/-- The fully factored mixed-coordinate majorant.  Its exponent of the
common logarithmic ratio is
`Ab * log qb + Ao * log qo`; its four arithmetic weights correspond to
`u`, `w`, `2u+w`, and `t`, respectively. -/
noncomputable def mixedIndicatorMajorant
    (L : ℕ) (Ab Kb Ao Ko qb qo : ℝ) (q : MixedTriple) : ℝ :=
  qb ^ Kb * qo ^ Ko *
    (log (mixedLinear q) / log L) ^
      (Ab * log qb + Ao * log qo) *
    (1 / qb) ^ ArithmeticFunction.cardFactors (mixedU q) *
    (1 / qo) ^
      primeFactorCountBetween L (mixedLinear q) (mixedW q) *
    (1 / (qb * qo)) ^
      ArithmeticFunction.cardFactors (mixedLinear q) *
    (1 / (qb * qo)) ^
      primeFactorCountBetween L (mixedLinear q) (mixedT q)

/-- Both endpoint regularity conditions majorize the indicator of every
mixed coordinate by the explicit factored weight. -/
theorem one_le_mixedIndicatorMajorant
    {L N : ℕ} {Ab Kb Ao Ko qb qo : ℝ} {q : MixedTriple}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hq : q ∈ mixedCoordinateSet L N Ab Kb Ao Ko) :
    (1 : ℝ) ≤
      mixedIndicatorMajorant L Ab Kb Ao Ko qb qo q := by
  let x := mixedLinear q
  let countT := primeFactorCountBetween L x (mixedT q)
  let countU := ArithmeticFunction.cardFactors (mixedU q)
  let countW := primeFactorCountBetween L x (mixedW q)
  let countX := ArithmeticFunction.cardFactors x
  let ratio : ℝ := log x / log L
  have hqData := hq
  rw [mixedCoordinateSet, mem_filter] at hqData
  have hu0 : 0 < mixedU q := by
    rcases mem_product.mp hqData.1 with ⟨htuBox, _hwBox⟩
    exact (mem_Icc.mp (mem_product.mp htuBox).2).1
  have hw0 : 0 < mixedW q := by
    rcases mem_product.mp hqData.1 with ⟨_htuBox, hwBox⟩
    exact (mem_Icc.mp hwBox).1
  have hx2 : 2 ≤ x := by
    dsimp [x, mixedLinear]
    omega
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogX : 0 < log (x : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < x by omega))
  have hratio : 0 < ratio := div_pos hlogX hlogL
  have hqb0 : 0 < qb := zero_lt_one.trans hqb
  have hqo0 : 0 < qo := zero_lt_one.trans hqo
  have hqbqo0 : 0 < qb * qo := mul_pos hqb0 hqo0
  have hpowInv (r : ℝ) (hr : 0 < r) (n : ℕ) :
      (1 / r) ^ n = exp (-(n : ℝ) * log r) := by
    have hbase : exp (-log r) = (1 / r : ℝ) := by
      rw [exp_neg, exp_log hr]
      exact (one_div r).symm
    calc
      (1 / r) ^ n = exp (-log r) ^ n := by rw [hbase]
      _ = exp ((n : ℝ) * (-log r)) :=
        (exp_nat_mul (-log r) n).symm
      _ = exp (-(n : ℝ) * log r) := by ring_nf
  have hmajor :
      mixedIndicatorMajorant L Ab Kb Ao Ko qb qo q =
        exp (
          log qb *
            (Ab * log ratio + Kb -
              (((countT + countU + countX : ℕ) : ℝ))) +
          log qo *
            (Ao * log ratio + Ko -
              (((countT + countW + countX : ℕ) : ℝ)))) := by
    unfold mixedIndicatorMajorant
    dsimp [x, countT, countU, countW, countX, ratio]
    rw [Real.rpow_def_of_pos hqb0,
      Real.rpow_def_of_pos hqo0,
      Real.rpow_def_of_pos hratio,
      hpowInv qb hqb0, hpowInv qo hqo0,
      hpowInv (qb * qo) hqbqo0,
      hpowInv (qb * qo) hqbqo0,
      log_mul hqb0.ne' hqo0.ne']
    repeat' rw [← exp_add]
    congr 1
    push_cast
    ring
  rw [hmajor]
  simpa [x, ratio, countT, countU, countW, countX] using
    (one_le_mixedIndicatorExp hqb hqo hq)

end

end Erdos327.Analytic
