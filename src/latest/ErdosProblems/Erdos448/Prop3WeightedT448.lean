import ErdosProblems.Erdos448.HRLemma2Lean448
import ErdosProblems.Erdos448.TauInvCorrection448
import ErdosProblems.Erdos448.MertensEulerProduct448
import ErdosProblems.Erdos448.WeightedTauInv448
import ErdosProblems.Erdos448.Prop3ShiftedMean448

/-!
The weighted `t`-sum occurring in the second use of
Erdos--Tenenbaum Lemma 2 in the proof of Proposition 3.

This file fixes the finite-sum and endpoint conventions, defines the
truncated big-Omega weight, and packages the three mutually exclusive
size regimes.  The final theorem is deliberately parameterized by the
three analytic estimates: it is the lossless glue used after those estimates
have been obtained from the Halberstam--Richert engine.
-/

open scoped BigOperators
open Finset

namespace Prop3WeightedT448

/-! ## The first correction is genuinely of divisor-inverse type -/

/-- Reciprocal divisor count, with the arithmetic-function junk value `0`
at zero.  This is the unshifted local model for the first correction `w₁` in
ET Lemma 2. -/
noncomputable def tauInv (n : ℕ) : ℝ :=
  if n = 0 then 0 else 1 / (n.divisors.card : ℝ)

@[simp] lemma tauInv_zero : tauInv 0 = 0 := by
  simp [tauInv]

@[simp] lemma tauInv_one : tauInv 1 = 1 := by
  simp [tauInv]

lemma tauInv_nonneg (n : ℕ) : 0 ≤ tauInv n := by
  unfold tauInv
  split_ifs
  · exact le_rfl
  · positivity

lemma tauInv_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    tauInv (m * n) = tauInv m * tauInv n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp
  simp only [tauInv, if_neg hm, if_neg hn, if_neg (Nat.mul_ne_zero hm hn)]
  rw [hmn.card_divisors_mul]
  push_cast
  simp only [one_div, mul_inv]

/-- `tauInv` bundled for direct use as `u` in ET Lemma 2. -/
noncomputable def tauInvAF : ArithmeticFunction ℝ :=
  ⟨tauInv, tauInv_zero⟩

@[simp] lemma tauInvAF_apply (n : ℕ) : tauInvAF n = tauInv n := rfl

lemma tauInvAF_multiplicative :
    ArithmeticFunction.IsMultiplicative tauInvAF := by
  refine ⟨tauInv_one, ?_⟩
  intro m n hmn
  exact tauInv_mul_of_coprime hmn

/-- The exact prime-power identity behind the phrase "of tau-inverse type". -/
lemma tauInv_prime_pow {p nu : ℕ} (hp : p.Prime) :
    tauInv (p ^ nu) = 1 / ((nu + 1 : ℕ) : ℝ) := by
  have hpnu : p ^ nu ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [tauInv, if_neg hpnu, Nat.divisors_prime_pow hp]
  simp

/-- A named, checkable interface for the local estimate required of a
`tau`-inverse-type function.  The error term in the paper is allowed here;
`tauInv` itself satisfies the interface with error constant zero. -/
def IsTauInverseType (w : ℕ → ℝ) (C delta : ℝ) : Prop :=
  0 ≤ C ∧ 0 < delta ∧
    ∀ {p nu : ℕ}, p.Prime → 1 ≤ nu →
      |w (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)| ≤ C * (p : ℝ) ^ (-delta)

lemma tauInv_isTauInverseType : IsTauInverseType tauInv 0 1 := by
  refine ⟨le_rfl, zero_lt_one, ?_⟩
  intro p nu hp hnu
  rw [tauInv_prime_pow hp]
  norm_num

lemma IsTauInverseType.prime_pow_le
    {w : ℕ → ℝ} {C delta : ℝ} (hw : IsTauInverseType w C delta)
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu) :
    w (p ^ nu) ≤ 1 / ((nu + 1 : ℕ) : ℝ) + C * (p : ℝ) ^ (-delta) := by
  have habs := hw.2.2 hp hnu
  have hself : w (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ) ≤
      |w (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)| := le_abs_self _
  linarith

/-- `Omega(n,u)`: prime factors of `n` below `u`, counted with multiplicity. -/
def omegaBelow (n u : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p => p < u).length

@[simp] lemma omegaBelow_zero (u : ℕ) : omegaBelow 0 u = 0 := by
  simp [omegaBelow]

@[simp] lemma omegaBelow_one (u : ℕ) : omegaBelow 1 u = 0 := by
  simp [omegaBelow]

lemma omegaBelow_mul {a b u : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    omegaBelow (a * b) u = omegaBelow a u + omegaBelow b u := by
  unfold omegaBelow
  have hp := (Nat.perm_primeFactorsList_mul ha hb).filter (fun p => p < u)
  simpa using hp.length_eq

lemma omegaBelow_prime_pow {p j u : ℕ} (hp : p.Prime) :
    omegaBelow (p ^ j) u = if p < u then j else 0 := by
  rw [omegaBelow, hp.primeFactorsList_pow]
  by_cases hpu : p < u <;> simp [hpu]

/-- The specialized weight `2^(-Omega(t,2^k))`, written without integer
exponents. -/
noncomputable def omegaWeight (k t : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(omegaBelow t (2 ^ k) : ℤ))

lemma omegaWeight_pos (k t : ℕ) : 0 < omegaWeight k t := by
  exact zpow_pos (by norm_num) _

lemma omegaWeight_nonneg (k t : ℕ) : 0 ≤ omegaWeight k t :=
  (omegaWeight_pos k t).le

lemma omegaWeight_mul {a b k : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    omegaWeight k (a * b) = omegaWeight k a * omegaWeight k b := by
  rw [omegaWeight, omegaWeight, omegaWeight, omegaBelow_mul ha hb]
  push_cast
  rw [neg_add_rev, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  exact mul_comm _ _

/-- The truncated Rankin weight bundled for the second application of ET
Lemma 2. -/
noncomputable def omegaWeightAF (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else omegaWeight k n, by simp⟩

@[simp] lemma omegaWeightAF_zero (k : ℕ) : omegaWeightAF k 0 = 0 := by
  simp [omegaWeightAF]

@[simp] lemma omegaWeightAF_one (k : ℕ) : omegaWeightAF k 1 = 1 := by
  simp [omegaWeightAF, omegaWeight, omegaBelow]

lemma omegaWeightAF_nonneg (k n : ℕ) : 0 ≤ omegaWeightAF k n := by
  simp only [omegaWeightAF, ArithmeticFunction.coe_mk]
  split_ifs
  · exact le_rfl
  · exact omegaWeight_nonneg k n

lemma omegaWeightAF_multiplicative (k : ℕ) :
    ArithmeticFunction.IsMultiplicative (omegaWeightAF k) := by
  refine ⟨omegaWeightAF_one k, ?_⟩
  intro a b hab
  by_cases ha : a = 0
  · subst a
    have hb : b = 1 := by simpa using hab
    subst b
    simp
  by_cases hb : b = 0
  · subst b
    have ha1 : a = 1 := by simpa [Nat.coprime_comm] using hab
    subst a
    simp
  simp only [omegaWeightAF, ArithmeticFunction.coe_mk, if_neg ha, if_neg hb,
    if_neg (Nat.mul_ne_zero ha hb)]
  exact omegaWeight_mul ha hb

lemma omegaWeightAF_prime_pow {p j k : ℕ} (hp : p.Prime) :
    omegaWeightAF k (p ^ j) =
      if p < 2 ^ k then (2 : ℝ) ^ (-(j : ℤ)) else 1 := by
  have hpj : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [omegaWeightAF, ArithmeticFunction.coe_mk, if_neg hpj, omegaWeight,
    omegaBelow_prime_pow hp]
  by_cases hpk : p < 2 ^ k <;> simp [hpk]

lemma omegaWeightAF_le_one (k n : ℕ) : omegaWeightAF k n ≤ 1 := by
  simp only [omegaWeightAF, ArithmeticFunction.coe_mk]
  split_ifs
  · norm_num
  · unfold omegaWeight
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀
      (one_le_zpow₀ (by norm_num) (Int.ofNat_zero_le _))

/-- The local series in the second ET Lemma 2 application is summable under
the defining local estimate of a tau-inverse-type function. -/
lemma tauInverse_weighted_local_summable
    (w₁ : ArithmeticFunction ℝ)
    (hwOne : w₁ 1 = 1) (hwNonneg : ∀ n, 0 ≤ w₁ n)
    {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hwType : IsTauInverseType w₁ C delta)
    {p : ℕ} (hp : p.Prime) (i k : ℕ) :
    Summable (fun j : ℕ =>
      w₁ (p ^ (i + j)) * omegaWeightAF k (p ^ j) /
        ((p ^ j : ℕ) : ℝ)) ∧
    Summable (fun j : ℕ =>
      w₁ (p ^ (i + j)) * omegaWeightAF k (p ^ j) *
        (1 + (j : ℝ) * Real.log (p : ℝ)) /
        ((p ^ j : ℕ) : ℝ)) := by
  let A : ℝ := 1 + C * (p : ℝ) ^ (-delta)
  have hpcast : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpowNonneg : 0 ≤ (p : ℝ) ^ (-delta) := by positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply ErdosTenenbaumLemma2Scratch.localSeries_summable_of_prime_power_geometric
    w₁ (omegaWeightAF k) hp i A 1 hA (by norm_num) (by norm_num)
  · intro j
    exact mul_nonneg (hwNonneg _) (omegaWeightAF_nonneg k _)
  · intro j
    rw [one_pow, mul_one]
    have hwUpper : w₁ (p ^ (i + j)) ≤ A := by
      by_cases hij : i + j = 0
      · have hi : i = 0 := by omega
        have hj : j = 0 := by omega
        subst i
        subst j
        have hAone : (1 : ℝ) ≤ A := by
          dsimp [A]
          exact le_add_of_nonneg_right (mul_nonneg hC hpowNonneg)
        simpa only [zero_add, pow_zero, hwOne] using hAone
      · have hpos : 1 ≤ i + j := Nat.one_le_iff_ne_zero.mpr hij
        have hlocal := hwType.prime_pow_le hp hpos
        have hhalf : (1 : ℝ) / (((i + j + 1 : ℕ) : ℝ)) ≤ 1 := by
          have hdenpos : (0 : ℝ) < ((i + j + 1 : ℕ) : ℝ) := by positivity
          apply (div_le_one hdenpos).2
          exact_mod_cast Nat.succ_pos (i + j)
        dsimp [A]
        linarith
    calc
      w₁ (p ^ (i + j)) * omegaWeightAF k (p ^ j)
          ≤ A * omegaWeightAF k (p ^ j) :=
            mul_le_mul_of_nonneg_right hwUpper (omegaWeightAF_nonneg k _)
      _ ≤ A * 1 :=
        mul_le_mul_of_nonneg_left (omegaWeightAF_le_one k _) hA
      _ = A := mul_one A

/-- A small analytic helper used to turn a prime-power estimate into a local
Euler-factor estimate. -/
lemma tsum_le_one_add_geometric_tail
    (f : ℕ → ℝ) (A r : ℝ)
    (hf : Summable f) (hfzero : f 0 = 1)
    (hA : 0 ≤ A) (hrzero : 0 ≤ r) (hrone : r < 1)
    (htail : ∀ j : ℕ, f (j + 1) ≤ A * r ^ (j + 1)) :
    (∑' j : ℕ, f j) ≤ 1 + A * r / (1 - r) := by
  have hftail : Summable (fun j : ℕ => f (j + 1)) :=
    (summable_nat_add_iff 1).2 hf
  have hgeom : Summable (fun j : ℕ => A * r ^ (j + 1)) := by
    have hr := summable_geometric_of_lt_one hrzero hrone
    have := hr.mul_left (A * r)
    simpa only [pow_succ', mul_assoc] using this
  have htailTsum : (∑' j : ℕ, f (j + 1)) ≤
      ∑' j : ℕ, A * r ^ (j + 1) :=
    hftail.tsum_le_tsum htail hgeom
  have hgeomSum : (∑' j : ℕ, A * r ^ (j + 1)) =
      A * r / (1 - r) := by
    have hsum := ((hasSum_geometric_of_lt_one hrzero hrone).mul_left (A * r)).tsum_eq
    simpa only [pow_succ', mul_assoc, div_eq_mul_inv] using hsum
  rw [hf.tsum_eq_zero_add, hfzero]
  simpa [add_comm] using add_le_add_left (htailTsum.trans_eq hgeomSum) 1

/-- A convenient exact local majorant.  Its first branch has leading
coefficient `1/4` and its second branch leading coefficient `1/2`. -/
noncomputable def tauInverseWeightedLocalMajorant
    (C delta : ℝ) (k p : ℕ) : ℝ :=
  let A := (1 / 2 : ℝ) + C * (p : ℝ) ^ (-delta)
  if p < 2 ^ k then
    1 + A * ((2 : ℝ) * p)⁻¹ / (1 - ((2 : ℝ) * p)⁻¹)
  else
    1 + A * (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹)

/-- Uniform Euler-factor estimate obtained directly from the
`tau`-inverse-type prime-power hypothesis.  This is the local analytic input
whose product gives the two logarithmic regimes in Proposition 3. -/
theorem diagonalEuler_tauInverse_omegaWeight_le
    (w₁ : ArithmeticFunction ℝ)
    (hwOne : w₁ 1 = 1) (hwNonneg : ∀ n, 0 ≤ w₁ n)
    {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hwType : IsTauInverseType w₁ C delta)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ErdosTenenbaumLemma2Scratch.diagonalEuler w₁ (omegaWeightAF k) p ≤
      tauInverseWeightedLocalMajorant C delta k p := by
  let f : ℕ → ℝ := fun j =>
    w₁ (p ^ j) * omegaWeightAF k (p ^ j) / ((p ^ j : ℕ) : ℝ)
  let A : ℝ := (1 / 2 : ℝ) + C * (p : ℝ) ^ (-delta)
  have hpcast : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hf : Summable f := by
    simpa only [f, zero_add] using
      (tauInverse_weighted_local_summable w₁ hwOne hwNonneg hC hdelta
        hwType hp 0 k).1
  have hfzero : f 0 = 1 := by simp [f, hwOne]
  have hwTail : ∀ j : ℕ, w₁ (p ^ (j + 1)) ≤ A := by
    intro j
    have hlocal := hwType.prime_pow_le hp (by omega : 1 ≤ j + 1)
    have htwo : (2 : ℝ) ≤ ((j + 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 ≤ j + 1 + 1 by omega)
    have hrecip : (1 : ℝ) / (((j + 1 + 1 : ℕ) : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) htwo
    dsimp [A]
    linarith
  by_cases hsmall : p < 2 ^ k
  · let r : ℝ := ((2 : ℝ) * p)⁻¹
    have hrzero : 0 ≤ r := by dsimp [r]; positivity
    have hrone : r < 1 := by
      dsimp [r]
      apply inv_lt_one_of_one_lt₀
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      nlinarith
    have htail : ∀ j : ℕ, f (j + 1) ≤ A * r ^ (j + 1) := by
      intro j
      have hv : omegaWeightAF k (p ^ (j + 1)) =
          ((2 : ℝ)⁻¹) ^ (j + 1) := by
        rw [omegaWeightAF_prime_pow hp, if_pos hsmall, zpow_neg,
          zpow_natCast, inv_pow]
      have hden : (0 : ℝ) ≤ ((p ^ (j + 1) : ℕ) : ℝ) := by positivity
      calc
        f (j + 1) =
            w₁ (p ^ (j + 1)) * omegaWeightAF k (p ^ (j + 1)) /
              ((p ^ (j + 1) : ℕ) : ℝ) := rfl
        _ ≤ A * omegaWeightAF k (p ^ (j + 1)) /
              ((p ^ (j + 1) : ℕ) : ℝ) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hwTail j) (omegaWeightAF_nonneg k _)) hden
        _ = A * r ^ (j + 1) := by
            rw [hv]
            dsimp [r]
            push_cast
            rw [mul_inv, mul_pow]
            simp only [inv_pow]
            ring
    change (∑' j : ℕ, f j) ≤ _
    rw [tauInverseWeightedLocalMajorant, if_pos hsmall]
    exact tsum_le_one_add_geometric_tail f A r hf hfzero hA hrzero hrone htail
  · let r : ℝ := (p : ℝ)⁻¹
    have hrzero : 0 ≤ r := by dsimp [r]; positivity
    have hrone : r < 1 := by
      dsimp [r]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    have htail : ∀ j : ℕ, f (j + 1) ≤ A * r ^ (j + 1) := by
      intro j
      have hv : omegaWeightAF k (p ^ (j + 1)) = 1 := by
        rw [omegaWeightAF_prime_pow hp, if_neg hsmall]
      have hden : (0 : ℝ) ≤ ((p ^ (j + 1) : ℕ) : ℝ) := by positivity
      calc
        f (j + 1) =
            w₁ (p ^ (j + 1)) * omegaWeightAF k (p ^ (j + 1)) /
              ((p ^ (j + 1) : ℕ) : ℝ) := rfl
        _ ≤ A * omegaWeightAF k (p ^ (j + 1)) /
              ((p ^ (j + 1) : ℕ) : ℝ) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hwTail j) (omegaWeightAF_nonneg k _)) hden
        _ = A * r ^ (j + 1) := by
            rw [hv, mul_one]
            dsimp [r]
            push_cast
            simp only [inv_pow]
            ring
    change (∑' j : ℕ, f j) ≤ _
    rw [tauInverseWeightedLocalMajorant, if_neg hsmall]
    exact tsum_le_one_add_geometric_tail f A r hf hfzero hA hrzero hrone htail

/-- The main local factor after discarding the summable error. -/
noncomputable def mixedHalfQuarterLocal (k p : ℕ) : ℝ :=
  if p < 2 ^ k then
    1 + (1 / 2 : ℝ) * ((2 : ℝ) * p)⁻¹ /
      (1 - ((2 : ℝ) * p)⁻¹)
  else
    1 + (1 / 2 : ℝ) * (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹)

/-- The absolutely convergent error factor left by the `O(p^-delta)` term
in a tau-inverse-type function. -/
noncomputable def tauInverseWeightedErrorFactor
    (C delta : ℝ) (k p : ℕ) : ℝ :=
  if p < 2 ^ k then
    1 + C * (p : ℝ) ^ (-delta) * ((2 : ℝ) * p)⁻¹ /
      (1 - ((2 : ℝ) * p)⁻¹)
  else
    1 + C * (p : ℝ) ^ (-delta) * (p : ℝ)⁻¹ /
      (1 - (p : ℝ)⁻¹)

private lemma one_add_sum_le_product
    {e r : ℝ} (he : 0 ≤ e) (hrzero : 0 ≤ r) (hrone : r < 1) :
    1 + ((1 / 2 : ℝ) + e) * r / (1 - r) ≤
      (1 + (1 / 2 : ℝ) * r / (1 - r)) *
        (1 + e * r / (1 - r)) := by
  have hden : 0 < 1 - r := sub_pos.mpr hrone
  have hx : 0 ≤ (1 / 2 : ℝ) * r / (1 - r) := by positivity
  have hy : 0 ≤ e * r / (1 - r) := by positivity
  have hsplit : (((1 / 2 : ℝ) + e) * r / (1 - r)) =
      (1 / 2 : ℝ) * r / (1 - r) + e * r / (1 - r) := by ring
  rw [hsplit]
  nlinarith [mul_nonneg hx hy]

lemma tauInverseWeightedLocalMajorant_le_main_mul_error
    {C delta : ℝ} (hC : 0 ≤ C) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    tauInverseWeightedLocalMajorant C delta k p ≤
      mixedHalfQuarterLocal k p * tauInverseWeightedErrorFactor C delta k p := by
  have he : 0 ≤ C * (p : ℝ) ^ (-delta) := by positivity
  by_cases hsmall : p < 2 ^ k
  · let r : ℝ := ((2 : ℝ) * p)⁻¹
    have hrzero : 0 ≤ r := by dsimp [r]; positivity
    have hrone : r < 1 := by
      dsimp [r]
      apply inv_lt_one_of_one_lt₀
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      nlinarith
    simpa [tauInverseWeightedLocalMajorant, mixedHalfQuarterLocal,
      tauInverseWeightedErrorFactor, hsmall, r] using
      one_add_sum_le_product he hrzero hrone
  · let r : ℝ := (p : ℝ)⁻¹
    have hrzero : 0 ≤ r := by dsimp [r]; positivity
    have hrone : r < 1 := by
      dsimp [r]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    simpa [tauInverseWeightedLocalMajorant, mixedHalfQuarterLocal,
      tauInverseWeightedErrorFactor, hsmall, r] using
      one_add_sum_le_product he hrzero hrone

/-- Product-level separation into the Mertens main factor and the uniformly
bounded convergent error product. -/
theorem diagonalEuler_product_le_mixed_mul_error
    (w₁ : ArithmeticFunction ℝ)
    (hwOne : w₁ 1 = 1) (hwNonneg : ∀ n, 0 ≤ w₁ n)
    {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hwType : IsTauInverseType w₁ C delta)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : ℕ) :
    (∏ p ∈ S,
      ErdosTenenbaumLemma2Scratch.diagonalEuler w₁ (omegaWeightAF k) p) ≤
      (∏ p ∈ S, mixedHalfQuarterLocal k p) *
        ∏ p ∈ S, tauInverseWeightedErrorFactor C delta k p := by
  calc
    (∏ p ∈ S,
        ErdosTenenbaumLemma2Scratch.diagonalEuler w₁ (omegaWeightAF k) p)
        ≤ ∏ p ∈ S, tauInverseWeightedLocalMajorant C delta k p := by
          apply Finset.prod_le_prod
          · intro p hpS
            unfold ErdosTenenbaumLemma2Scratch.diagonalEuler
            exact tsum_nonneg fun j =>
              div_nonneg
                (mul_nonneg (hwNonneg _) (omegaWeightAF_nonneg k _))
                (Nat.cast_nonneg _)
          · intro p hpS
            exact diagonalEuler_tauInverse_omegaWeight_le w₁ hwOne hwNonneg
              hC hdelta hwType (hS p hpS) k
    _ ≤ ∏ p ∈ S,
        mixedHalfQuarterLocal k p * tauInverseWeightedErrorFactor C delta k p := by
          apply Finset.prod_le_prod
          · intro p hpS
            have hdiagNonneg : 0 ≤
                ErdosTenenbaumLemma2Scratch.diagonalEuler
                  w₁ (omegaWeightAF k) p := by
              unfold ErdosTenenbaumLemma2Scratch.diagonalEuler
              exact tsum_nonneg fun j =>
                div_nonneg
                  (mul_nonneg (hwNonneg _) (omegaWeightAF_nonneg k _))
                  (Nat.cast_nonneg _)
            exact hdiagNonneg.trans
              (diagonalEuler_tauInverse_omegaWeight_le w₁ hwOne hwNonneg
                hC hdelta hwType (hS p hpS) k)
          · intro p hpS
            exact tauInverseWeightedLocalMajorant_le_main_mul_error
              hC (hS p hpS) k
    _ = (∏ p ∈ S, mixedHalfQuarterLocal k p) *
          ∏ p ∈ S, tauInverseWeightedErrorFactor C delta k p := by
          rw [Finset.prod_mul_distrib]

lemma tauInverseWeightedErrorFactor_sub_one_nonneg
    {C delta : ℝ} (hC : 0 ≤ C) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ tauInverseWeightedErrorFactor C delta k p - 1 := by
  have hpcast : (0 : ℝ) < p := by exact_mod_cast hp.pos
  by_cases hsmall : p < 2 ^ k
  · rw [tauInverseWeightedErrorFactor, if_pos hsmall]
    have hr : ((2 : ℝ) * p)⁻¹ < 1 := by
      apply inv_lt_one_of_one_lt₀
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      nlinarith
    simp only [add_sub_cancel_left]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity))
      (sub_nonneg.mpr hr.le)
  · rw [tauInverseWeightedErrorFactor, if_neg hsmall]
    have hr : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    simp only [add_sub_cancel_left]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity))
      (sub_nonneg.mpr hr.le)

lemma tauInverseWeightedErrorFactor_sub_one_le
    {C delta : ℝ} (hC : 0 ≤ C) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    tauInverseWeightedErrorFactor C delta k p - 1 ≤
      2 * C * (p : ℝ) ^ (-(1 + delta)) := by
  have hpcast : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpow : 0 ≤ (p : ℝ) ^ (-delta) := by positivity
  have hrpow : (p : ℝ) ^ (-delta) * (p : ℝ)⁻¹ =
      (p : ℝ) ^ (-(1 + delta)) := by
    rw [← Real.rpow_neg_one p, ← Real.rpow_add hpcast]
    congr 1
    ring
  by_cases hsmall : p < 2 ^ k
  · have hratioEq :
        ((2 : ℝ) * p)⁻¹ / (1 - ((2 : ℝ) * p)⁻¹) =
          1 / ((2 : ℝ) * p - 1) := by
      have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpcast
      have hden : (2 : ℝ) * p - 1 ≠ 0 := by nlinarith
      field_simp [hpne, hden]
    have hratio :
        ((2 : ℝ) * p)⁻¹ / (1 - ((2 : ℝ) * p)⁻¹) ≤
          (p : ℝ)⁻¹ := by
      rw [hratioEq]
      have hdenpos : (0 : ℝ) < (2 : ℝ) * p - 1 := by nlinarith
      have hp_le : (p : ℝ) ≤ 2 * p - 1 := by nlinarith
      simpa [one_div] using one_div_le_one_div_of_le hpcast hp_le
    rw [tauInverseWeightedErrorFactor, if_pos hsmall]
    simp only [add_sub_cancel_left]
    have hmul := mul_le_mul_of_nonneg_left hratio
      (mul_nonneg hC hpow)
    have htarget : C * (p : ℝ) ^ (-delta) * (p : ℝ)⁻¹ ≤
        2 * C * (p : ℝ) ^ (-(1 + delta)) := by
      rw [mul_assoc, hrpow]
      have hn : 0 ≤ C * (p : ℝ) ^ (-(1 + delta)) := by positivity
      nlinarith
    have hmul' :
        C * (p : ℝ) ^ (-delta) *
              (((2 : ℝ) * p)⁻¹ / (1 - ((2 : ℝ) * p)⁻¹)) ≤
            C * (p : ℝ) ^ (-delta) * (p : ℝ)⁻¹ := by
      simpa [mul_assoc] using hmul
    calc
      C * (p : ℝ) ^ (-delta) * ((2 : ℝ) * p)⁻¹ /
            (1 - ((2 : ℝ) * p)⁻¹) =
          C * (p : ℝ) ^ (-delta) *
            (((2 : ℝ) * p)⁻¹ / (1 - ((2 : ℝ) * p)⁻¹)) := by ring
      _ ≤ C * (p : ℝ) ^ (-delta) * (p : ℝ)⁻¹ := hmul'
      _ ≤ 2 * C * (p : ℝ) ^ (-(1 + delta)) := htarget
  · have hratioEq :
        (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) =
          1 / ((p : ℝ) - 1) := by
      have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpcast
      have hden : (p : ℝ) - 1 ≠ 0 := by nlinarith
      field_simp [hpne, hden]
    have hratio :
        (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) ≤
          2 * (p : ℝ)⁻¹ := by
      rw [hratioEq]
      have hdenpos : (0 : ℝ) < (p : ℝ) - 1 := by
        linarith [show (1 : ℝ) < p by exact_mod_cast hp.one_lt]
      rw [show 2 * (p : ℝ)⁻¹ = 2 / (p : ℝ) by ring]
      exact (div_le_div_iff₀ hdenpos hpcast).2 (by nlinarith)
    rw [tauInverseWeightedErrorFactor, if_neg hsmall]
    simp only [add_sub_cancel_left]
    have hmul := mul_le_mul_of_nonneg_left hratio
      (mul_nonneg hC hpow)
    calc
      C * (p : ℝ) ^ (-delta) * (p : ℝ)⁻¹ /
            (1 - (p : ℝ)⁻¹)
          = C * (p : ℝ) ^ (-delta) *
            ((p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹))
            := by ring
      _
          ≤ C * (p : ℝ) ^ (-delta) * (2 * (p : ℝ)⁻¹) := by
            exact hmul
      _ = 2 * (C * ((p : ℝ) ^ (-delta) * (p : ℝ)⁻¹)) := by ring
      _ = 2 * C * (p : ℝ) ^ (-(1 + delta)) := by
            rw [hrpow]
            ring

/-- The error product is bounded uniformly in the cutoff and in the finite
set of primes. -/
theorem exists_uniform_tauInverseWeightedErrorProduct_bound
    {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ E : ℝ, 0 < E ∧ ∀ (S : Finset ℕ),
      (∀ p ∈ S, p.Prime) → ∀ k : ℕ,
        (∏ p ∈ S, tauInverseWeightedErrorFactor C delta k p) ≤ E := by
  let g : ℕ → ℝ := fun n => 2 * C * (n : ℝ) ^ (-(1 + delta))
  have hg : Summable g := by
    apply Summable.mul_left
    exact Real.summable_nat_rpow.mpr (by linarith)
  refine ⟨Real.exp (∑' n : ℕ, g n), Real.exp_pos _, ?_⟩
  intro S hS k
  let e : ℕ → ℝ := fun p => tauInverseWeightedErrorFactor C delta k p - 1
  have heNonneg : ∀ p ∈ S, 0 ≤ e p := by
    intro p hpS
    exact tauInverseWeightedErrorFactor_sub_one_nonneg hC (hS p hpS) k
  have hprod : (S.prod fun p => 1 + e p) ≤ Real.exp (S.sum e) := by
    calc
      (S.prod fun p => 1 + e p) ≤ S.prod (fun p => Real.exp (e p)) := by
        exact Finset.prod_le_prod
          (fun p hpS => add_nonneg zero_le_one (heNonneg p hpS))
          (fun p hpS => by simpa [add_comm] using Real.add_one_le_exp (e p))
      _ = Real.exp (S.sum e) := by rw [← Real.exp_sum]
  have hsum : S.sum e ≤ ∑' n : ℕ, g n := by
    calc
      S.sum e ≤ S.sum g := by
        exact Finset.sum_le_sum fun p hpS =>
          tauInverseWeightedErrorFactor_sub_one_le hC (hS p hpS) k
      _ ≤ ∑' n : ℕ, g n := by
        exact hg.sum_le_tsum S (fun n hn => by positivity)
  calc
    (∏ p ∈ S, tauInverseWeightedErrorFactor C delta k p) =
        S.prod (fun p => 1 + e p) := by
          apply Finset.prod_congr rfl
          intro p hpS
          simp [e]
    _ ≤ Real.exp (S.sum e) := hprod
    _ ≤ Real.exp (∑' n : ℕ, g n) := Real.exp_le_exp.mpr hsum

/-! ## The genuine correction weight furnished by ET Lemma 2 -/

/-- A cutoff-independent multiplicative envelope for the two kinds of
prime-power factors in the shifted form of ET Lemma 2.  At every prime power
it is the maximum of the Euler correction and the original weight. -/
noncomputable def hybridCorrectionWeight
    (u v : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else n.factorization.prod fun p i =>
    if i = 0 then 1
    else max (ErdosTenenbaumLemma2Scratch.eulerCorrection u v p i) (u (p ^ i))

@[simp] lemma hybridCorrectionWeight_zero
    (u v : ArithmeticFunction ℝ) :
    hybridCorrectionWeight u v 0 = 0 := by
  simp [hybridCorrectionWeight]

@[simp] lemma hybridCorrectionWeight_one
    (u v : ArithmeticFunction ℝ) :
    hybridCorrectionWeight u v 1 = 1 := by
  simp [hybridCorrectionWeight]

lemma hybridCorrectionWeight_mul_of_coprime
    (u v : ArithmeticFunction ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    hybridCorrectionWeight u v (m * n) =
      hybridCorrectionWeight u v m * hybridCorrectionWeight u v n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  simp only [hybridCorrectionWeight, if_neg hm, if_neg hn, if_neg hmn0]
  rw [Nat.factorization_mul_of_coprime hmn, ← Finsupp.prod_add_index_of_disjoint]
  exact hmn.disjoint_primeFactors

lemma hybridCorrectionWeight_prime_pow
    (u v : ArithmeticFunction ℝ) {p nu : ℕ}
    (hp : p.Prime) (hnu : 1 ≤ nu) :
    hybridCorrectionWeight u v (p ^ nu) =
      max (ErdosTenenbaumLemma2Scratch.eulerCorrection u v p nu)
        (u (p ^ nu)) := by
  have hnu0 : nu ≠ 0 := Nat.one_le_iff_ne_zero.mp hnu
  have hpnu0 : p ^ nu ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [hybridCorrectionWeight, if_neg hpnu0, hp.factorization_pow]
  rw [Finsupp.prod_single_index (by simp)]
  simp [hnu0]

/-- The envelope still has the literal logarithmic `tau`-inverse local
error, uniformly in the Rankin cutoff. -/
theorem hybridCorrectionWeight_isTauInverseLogType
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {C : ℝ} (huType : TauInvCorrection448.IsTauInverseLogType u C)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1) :
    TauInvCorrection448.IsTauInverseLogType (hybridCorrectionWeight u v)
      (max (16 + 17 * C) C) := by
  have hcorr := TauInvCorrection448.correctionWeight_isTauInverseLogType
    u v huOne hvOne huNonneg hvNonneg huType hvPowLe
  have hmax := TauInvCorrection448.max_isTauInverseLogType hcorr huType
  refine ⟨hmax.1, ?_⟩
  intro p nu hp hnu
  rw [hybridCorrectionWeight_prime_pow u v hp hnu]
  rw [← TauInvCorrection448.correctionWeight_prime_pow u v hp hnu]
  exact hmax.2 hp hnu

lemma hybridCorrectionWeight_nonneg
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {C : ℝ} (huType : TauInvCorrection448.IsTauInverseLogType u C)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1)
    (n : ℕ) :
    0 ≤ hybridCorrectionWeight u v n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  rw [hybridCorrectionWeight, if_neg hn]
  change 0 ≤ ∏ p ∈ n.factorization.support,
    (if n.factorization p = 0 then 1 else
      max (ErdosTenenbaumLemma2Scratch.eulerCorrection
        u v p (n.factorization p)) (u (p ^ n.factorization p)))
  apply Finset.prod_nonneg
  intro p hpSupport
  split_ifs with hi0
  · norm_num
  · have hpMem : p ∈ n.primeFactors := by
      simpa only [Nat.support_factorization] using hpSupport
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hi : 1 ≤ n.factorization p := Nat.one_le_iff_ne_zero.mpr hi0
    have hcorr : 0 ≤
        ErdosTenenbaumLemma2Scratch.eulerCorrection
          u v p (n.factorization p) := by
      rw [← TauInvCorrection448.correctionWeight_prime_pow u v hpPrime hi]
      exact TauInvCorrection448.correctionWeight_nonneg
        u v huOne hvOne huNonneg hvNonneg huType hvPowLe _
    exact hcorr.trans (le_max_left _ _)

/-- The correction product below the mean-value cutoff and the original
prime-power product above it are both bounded by one cutoff-independent
hybrid correction weight. -/
theorem correctedInfinite_mul_largePrime_le_diagonal_mul_hybrid
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {C : ℝ} (huType : TauInvCorrection448.IsTauInverseLogType u C)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1)
    {q N : ℕ} (hq : q ≠ 0) :
    ErdosTenenbaumLemma2Scratch.correctedInfiniteEulerProduct u v q N *
        ErdosTenenbaumLemma2Scratch.largePrimeShiftProduct u q N ≤
      (∏ p ∈ (N + 1).primesBelow,
          ErdosTenenbaumLemma2Scratch.diagonalEuler u v p) *
        hybridCorrectionWeight u v q := by
  classical
  let S := q.primeFactors
  let P := (N + 1).primesBelow
  let T := S ∩ P
  let U := S \ P
  let a : ℕ → ℝ := fun p =>
    ErdosTenenbaumLemma2Scratch.eulerCorrection u v p (q.factorization p)
  let b : ℕ → ℝ := fun p => u (p ^ q.factorization p)
  let c : ℕ → ℝ := fun p => max (a p) (b p)
  have hcorrNonneg : ∀ p ∈ T, 0 ≤ a p := by
    intro p hpT
    have hpS : p ∈ S := (Finset.mem_inter.mp hpT).1
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hi : 1 ≤ q.factorization p := by
      have hpS' : p ∈ q.primeFactors := by simpa [S] using hpS
      rw [← Nat.support_factorization] at hpS'
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hpS')
    dsimp [a]
    rw [← TauInvCorrection448.correctionWeight_prime_pow u v hpPrime hi]
    exact TauInvCorrection448.correctionWeight_nonneg
      u v huOne hvOne huNonneg hvNonneg huType hvPowLe _
  have hbNonneg : ∀ p ∈ U, 0 ≤ b p := by
    intro p hpU
    exact huNonneg _
  have hT : (∏ p ∈ T, a p) ≤ ∏ p ∈ T, c p := by
    exact Finset.prod_le_prod hcorrNonneg fun p hp => le_max_left _ _
  have hU : (∏ p ∈ U, b p) ≤ ∏ p ∈ U, c p := by
    exact Finset.prod_le_prod hbNonneg fun p hp => le_max_right _ _
  have hTcNonneg : 0 ≤ ∏ p ∈ T, c p := by
    apply Finset.prod_nonneg
    intro p hp
    exact (hcorrNonneg p hp).trans (le_max_left _ _)
  have hUbNonneg : 0 ≤ ∏ p ∈ U, b p :=
    Finset.prod_nonneg hbNonneg
  have hTU : T ∪ U = S := by
    ext p
    simp only [T, U, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro hpS
      by_cases hpP : p ∈ P
      · exact Or.inl ⟨hpS, hpP⟩
      · exact Or.inr ⟨hpS, hpP⟩
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro p hpT hpU
    simp only [T, U, Finset.mem_inter, Finset.mem_sdiff] at hpT hpU
    exact hpU.2 hpT.2
  have hhybrid : hybridCorrectionWeight u v q = ∏ p ∈ S, c p := by
    rw [hybridCorrectionWeight, if_neg hq]
    change (∏ p ∈ q.factorization.support,
      (if q.factorization p = 0 then 1 else
        max (ErdosTenenbaumLemma2Scratch.eulerCorrection
          u v p (q.factorization p)) (u (p ^ q.factorization p)))) = _
    rw [Nat.support_factorization]
    apply Finset.prod_congr rfl
    intro p hpS
    have hi : q.factorization p ≠ 0 := by
      have hpS' : p ∈ q.primeFactors := by simpa [S] using hpS
      rw [← Nat.support_factorization] at hpS'
      exact Finsupp.mem_support_iff.mp hpS'
    simp [a, b, c, hi]
  have hfactor :
      (∏ p ∈ T, a p) * (∏ p ∈ U, b p) ≤ hybridCorrectionWeight u v q := by
    calc
      (∏ p ∈ T, a p) * (∏ p ∈ U, b p)
          ≤ (∏ p ∈ T, c p) * (∏ p ∈ U, c p) :=
            mul_le_mul hT hU hUbNonneg hTcNonneg
      _ = ∏ p ∈ T ∪ U, c p := by rw [Finset.prod_union hdisj]
      _ = ∏ p ∈ S, c p := by rw [hTU]
      _ = hybridCorrectionWeight u v q := hhybrid.symm
  unfold ErdosTenenbaumLemma2Scratch.correctedInfiniteEulerProduct
    ErdosTenenbaumLemma2Scratch.largePrimeShiftProduct
  change ((∏ p ∈ T, a p) * ∏ p ∈ P,
      ErdosTenenbaumLemma2Scratch.diagonalEuler u v p) *
      (∏ p ∈ U, b p) ≤ _
  calc
    ((∏ p ∈ T, a p) * ∏ p ∈ P,
        ErdosTenenbaumLemma2Scratch.diagonalEuler u v p) *
        (∏ p ∈ U, b p) =
      (∏ p ∈ P, ErdosTenenbaumLemma2Scratch.diagonalEuler u v p) *
        ((∏ p ∈ T, a p) * ∏ p ∈ U, b p) := by ring
    _ ≤ (∏ p ∈ P, ErdosTenenbaumLemma2Scratch.diagonalEuler u v p) *
        hybridCorrectionWeight u v q := by
      apply mul_le_mul_of_nonneg_left hfactor
      apply Finset.prod_nonneg
      intro p hpP
      unfold ErdosTenenbaumLemma2Scratch.diagonalEuler
      exact tsum_nonneg fun j =>
        div_nonneg (mul_nonneg (huNonneg _) (hvNonneg _)) (Nat.cast_nonneg _)
    _ = _ := by rfl

/-- Indicator of the condition that every prime factor is at least `sigma`.
At `sigma = 2` this is one on every positive integer. -/
def roughIndicator (sigma n : ℕ) : ℝ :=
  if ∀ p ∈ n.primeFactors, sigma ≤ p then 1 else 0

lemma roughIndicator_nonneg (sigma n : ℕ) :
    0 ≤ roughIndicator sigma n := by
  unfold roughIndicator
  split_ifs <;> norm_num

lemma roughIndicator_le_one (sigma n : ℕ) :
    roughIndicator sigma n ≤ 1 := by
  unfold roughIndicator
  split_ifs <;> norm_num

lemma roughIndicator_two_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    roughIndicator 2 n = 1 := by
  rw [roughIndicator, if_pos]
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).two_le

/-- The exact weighted kernel before summing over positive `t < z`. -/
noncomputable def weightedTKernel
    (w₁ : ℕ → ℝ) (q k sigma t : ℕ) : ℝ :=
  omegaWeight k t * roughIndicator sigma t * w₁ (t * q)

lemma weightedTKernel_nonneg
    (w₁ : ℕ → ℝ) (hw₁ : ∀ n, 0 ≤ w₁ n)
    (q k sigma t : ℕ) :
    0 ≤ weightedTKernel w₁ q k sigma t := by
  exact mul_nonneg
    (mul_nonneg (omegaWeight_nonneg k t) (roughIndicator_nonneg sigma t))
    (hw₁ _)

/-- The finite interpretation of the paper's sum over `0 < t < z`. -/
noncomputable def weightedTSum
    (w₁ : ℕ → ℝ) (q k sigma z : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico 1 z, weightedTKernel w₁ q k sigma t

lemma weightedTSum_nonneg
    (w₁ : ℕ → ℝ) (hw₁ : ∀ n, 0 ≤ w₁ n)
    (q k sigma z : ℕ) :
    0 ≤ weightedTSum w₁ q k sigma z := by
  unfold weightedTSum
  exact Finset.sum_nonneg fun t ht => weightedTKernel_nonneg w₁ hw₁ q k sigma t

lemma weightedTSum_succ_eq_shiftedConvolutionSum
    (u : ArithmeticFunction ℝ) (q k N : ℕ) :
    weightedTSum u q k 2 (N + 1) =
      ErdosTenenbaumLemma2Scratch.shiftedConvolutionSum
        u (omegaWeightAF k) q N := by
  unfold weightedTSum ErdosTenenbaumLemma2Scratch.shiftedConvolutionSum
  have hset : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
    ext t
    simp
  rw [hset]
  apply Finset.sum_congr rfl
  intro t ht
  have htOne : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have ht0 : t ≠ 0 := Nat.ne_of_gt (zero_lt_one.trans_le htOne)
  rw [weightedTKernel, roughIndicator_two_of_ne_zero ht0]
  simp [omegaWeightAF, ht0, Nat.mul_comm, mul_comm]

/-- The actual second ET-Lemma-2 estimate before Mertens simplification.
It derives the correction weight and all local summability hypotheses; the
only extra local hypothesis is the normalized prime-power bound required by
the unconditional Halberstam--Richert engine itself. -/
theorem weightedTSum_succ_le_HR_corrected
    (u : ArithmeticFunction ℝ)
    (huMult : u.IsMultiplicative)
    (huOne : u 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n)
    (huPos : ∀ n, n ≠ 0 → 0 < u n)
    {Cpow delta : ℝ} (hCpow : 0 ≤ Cpow) (hdelta : 0 < delta)
    (huPowType : IsTauInverseType u Cpow delta)
    {Clog : ℝ}
    (huLogType : TauInvCorrection448.IsTauInverseLogType u Clog)
    {q : ℕ} (hq : q ≠ 0)
    (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2) (hlambda2_lt : lambda2 < 2)
    (k : ℕ)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ,
      u (p ^ (q.factorization p + (j + 1))) *
            omegaWeightAF k (p ^ (j + 1)) /
          u (p ^ q.factorization p) ≤ lambda1 * lambda2 ^ j)
    (N : ℕ) (hN : 2 ≤ N) :
    weightedTSum u q k 2 (N + 1) ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ((∏ p ∈ (N + 1).primesBelow,
              ErdosTenenbaumLemma2Scratch.diagonalEuler
                u (omegaWeightAF k) p) *
            hybridCorrectionWeight u (omegaWeightAF k) q) := by
  have hHR :=
    ErdosTenenbaumLemma2Scratch.multiplicative_convolution_mean_value_II
      u (omegaWeightAF k) huMult (omegaWeightAF_multiplicative k)
      huOne (omegaWeightAF_one k) huNonneg (omegaWeightAF_nonneg k)
      huPos hq lambda1 lambda2 hlambda1 hlambda2 hlambda2_lt hpow N hN
      (by
        intro p hpP
        have hp := Nat.prime_of_mem_primesBelow hpP
        simpa only [Nat.zero_add] using
          (tauInverse_weighted_local_summable u huOne huNonneg
            hCpow hdelta huPowType hp 0 k).1)
      (by
        intro p hpP
        have hp := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hpP).1
        exact (tauInverse_weighted_local_summable u huOne huNonneg
          hCpow hdelta huPowType hp (q.factorization p) k).1)
      (by
        intro p hpP
        have hp := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hpP).1
        exact (tauInverse_weighted_local_summable u huOne huNonneg
          hCpow hdelta huPowType hp (q.factorization p) k).2)
  have hcorr := correctedInfinite_mul_largePrime_le_diagonal_mul_hybrid
    u (omegaWeightAF k) huOne (omegaWeightAF_one k)
    huNonneg (omegaWeightAF_nonneg k) huLogType
    (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) (q := q) (N := N) hq
  have hscale : 0 ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    apply div_nonneg
    · exact mul_nonneg
        (by
          have hm := HalberstamScratch.explicitMassConstant_nonneg
            hlambda1 hlambda2
          linarith)
        (Nat.cast_nonneg N)
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  rw [weightedTSum_succ_eq_shiftedConvolutionSum]
  calc
    ErdosTenenbaumLemma2Scratch.shiftedConvolutionSum
        u (omegaWeightAF k) q N ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
        ErdosTenenbaumLemma2Scratch.correctedInfiniteEulerProduct
          u (omegaWeightAF k) q N *
        ErdosTenenbaumLemma2Scratch.largePrimeShiftProduct u q N := hHR
    _ = ((HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
          (N : ℝ) / Real.log (N : ℝ)) *
        (ErdosTenenbaumLemma2Scratch.correctedInfiniteEulerProduct
          u (omegaWeightAF k) q N *
        ErdosTenenbaumLemma2Scratch.largePrimeShiftProduct u q N) := by ring
    _ ≤ ((HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
          (N : ℝ) / Real.log (N : ℝ)) *
        ((∏ p ∈ (N + 1).primesBelow,
          ErdosTenenbaumLemma2Scratch.diagonalEuler
            u (omegaWeightAF k) p) *
          hybridCorrectionWeight u (omegaWeightAF k) q) :=
      mul_le_mul_of_nonneg_left hcorr hscale
    _ = _ := by ring

/-- Constant in the final shifted dyadic weighted mean. -/
noncomputable def weightedShiftedDyadicConstant
    (Clog lambda1 lambda2 : ℝ) : ℝ :=
  4 * (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
    Real.exp (2 + 24 * Clog * Real.log 2) *
    TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
    (Real.log 2) ^ (-(3 : ℝ) / 4)

lemma weightedShiftedDyadicConstant_nonneg
    {Clog lambda1 lambda2 : ℝ}
    (hC : 0 ≤ Clog) (h₁ : 0 ≤ lambda1) (h₂ : 0 ≤ lambda2) :
    0 ≤ weightedShiftedDyadicConstant Clog lambda1 lambda2 := by
  have hm := HalberstamScratch.explicitMassConstant_nonneg h₁ h₂
  have hc := TauInvTypeMean448.cleanMertensConstant_pos.le
  unfold weightedShiftedDyadicConstant
  positivity

/-- Specialized second mean estimate at the exact Proposition-3 frontier
`N = 4 * 2^k`.  The output weight is constructed from the genuine ET Euler
correction and is logarithmic-`tau`-inverse type by
`hybridCorrectionWeight_isTauInverseLogType`. -/
theorem weightedTSum_dyadic_le
    (u : ArithmeticFunction ℝ)
    (huMult : u.IsMultiplicative)
    (huOne : u 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n)
    (huPos : ∀ n, n ≠ 0 → 0 < u n)
    {Cpow delta : ℝ} (hCpow : 0 ≤ Cpow) (hdelta : 0 < delta)
    (huPowType : IsTauInverseType u Cpow delta)
    {Clog : ℝ}
    (huLogType : TauInvCorrection448.IsTauInverseLogType u Clog)
    {q : ℕ} (hq : q ≠ 0)
    (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2) (hlambda2_lt : lambda2 < 2)
    (k : ℕ) (hk : 1 ≤ k)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ,
      u (p ^ (q.factorization p + (j + 1))) *
            omegaWeightAF k (p ^ (j + 1)) /
          u (p ^ q.factorization p) ≤ lambda1 * lambda2 ^ j) :
    weightedTSum u q k 2 (2 ^ (k + 2) + 1) ≤
      weightedShiftedDyadicConstant Clog lambda1 lambda2 *
        ((2 ^ k : ℕ) : ℝ) * (k : ℝ) ^ (-(3 : ℝ) / 4) *
          hybridCorrectionWeight u (omegaWeightAF k) q := by
  let N : ℕ := 2 ^ (k + 2)
  have hN : 2 ≤ N := by
    dsimp [N]
    have hpowTwo : 2 ^ 1 ≤ 2 ^ (k + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have huMeanType : TauInvTypeMean448.IsTauInverseLogType u (3 * Clog) :=
    { C_nonneg := mul_nonneg (by norm_num) huLogType.1
      map_zero := u.map_zero
      map_one := huOne
      map_mul_of_coprime := fun hmn => huMult.map_mul_of_coprime hmn
      nonneg := huNonneg
      prime_pow_close := by
        intro p nu hp hnu
        have hlocal := huLogType.2 hp hnu
        have hscale := TauInvCorrection448.one_add_log_le_three_log hp
        have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
        calc
          |u (p ^ nu) - 1 / (((nu + 1 : ℕ) : ℝ))| ≤
              Clog * (1 + Real.log (p : ℝ)) / (p : ℝ) := hlocal
          _ ≤ Clog * (3 * Real.log (p : ℝ)) / (p : ℝ) := by
            apply div_le_div_of_nonneg_right _ hpR.le
            exact mul_le_mul_of_nonneg_left hscale huLogType.1
          _ = 3 * Clog * Real.log (p : ℝ) / (p : ℝ) := by ring }
  have hbase := weightedTSum_succ_le_HR_corrected
    u huMult huOne huNonneg huPos hCpow hdelta huPowType huLogType hq
    lambda1 lambda2 hlambda1 hlambda2 hlambda2_lt k hpow N hN
  have heuler :
      (∏ p ∈ (N + 1).primesBelow,
          ErdosTenenbaumLemma2Scratch.diagonalEuler
            u (omegaWeightAF k) p) ≤
        Real.exp ((1 / 4 : ℝ) *
            Real.log (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) +
          2 + 24 * Clog * Real.log 2) := by
    have h := WeightedTauInv448.weighted_eulerProduct_le huMeanType k hk
    have homega : omegaWeightAF k = WeightedTauInv448.omegaWeightAF k := by
      rfl
    rw [homega]
    dsimp [N]
    change
      (∏ p ∈ (2 ^ (k + 2) + 1).primesBelow,
        ∑' j : ℕ, WeightedTauInv448.weightedFunction u k (p ^ j) /
          (((p ^ j : ℕ) : ℝ))) ≤ _
    convert h using 1 <;> ring_nf
  have hhybrid : 0 ≤ hybridCorrectionWeight u (omegaWeightAF k) q :=
    hybridCorrectionWeight_nonneg u (omegaWeightAF k)
      huOne (omegaWeightAF_one k) huNonneg (omegaWeightAF_nonneg k)
      huLogType (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) q
  have heulerHybrid :
      (∏ p ∈ (N + 1).primesBelow,
          ErdosTenenbaumLemma2Scratch.diagonalEuler
            u (omegaWeightAF k) p) *
          hybridCorrectionWeight u (omegaWeightAF k) q ≤
        Real.exp ((1 / 4 : ℝ) *
            Real.log (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) +
          2 + 24 * Clog * Real.log 2) *
          hybridCorrectionWeight u (omegaWeightAF k) q :=
    mul_le_mul_of_nonneg_right heuler hhybrid
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale : 0 ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    have hm := HalberstamScratch.explicitMassConstant_nonneg
      hlambda1 hlambda2
    have hc := TauInvTypeMean448.cleanMertensConstant_pos.le
    positivity
  have hraw : weightedTSum u q k 2 (N + 1) ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          (Real.exp ((1 / 4 : ℝ) *
              Real.log (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) +
            2 + 24 * Clog * Real.log 2) *
            hybridCorrectionWeight u (omegaWeightAF k) q) :=
    hbase.trans (mul_le_mul_of_nonneg_left heulerHybrid hscale)
  have hmertensLog : 0 < TauInvTypeMean448.cleanMertensConstant *
      Real.log (N : ℝ) := by
    exact mul_pos TauInvTypeMean448.cleanMertensConstant_pos hlogN
  have hexpQuarter :
      Real.exp ((1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ))) =
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
          (Real.log (N : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [← Real.mul_rpow TauInvTypeMean448.cleanMertensConstant_pos.le hlogN.le,
      Real.rpow_def_of_pos hmertensLog]
    congr 1
    ring
  have hexpSplit :
      Real.exp ((1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) +
          2 + 24 * Clog * Real.log 2) =
        Real.exp ((1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ))) *
          Real.exp (2 + 24 * Clog * Real.log 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogEq :
      Real.log (N : ℝ) = ((k + 2 : ℕ) : ℝ) * Real.log 2 := by
    dsimp [N]
    rw [show (((2 ^ (k + 2) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 2) by norm_num,
      Real.log_pow]
  have hlogGe : (k : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    rw [hlogEq]
    gcongr
    norm_num
  have hrpow :
      (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4) ≤
        ((k : ℝ) * Real.log 2) ^ (-(3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hkR hlog2) hlogGe (by norm_num)
  have hcoeff : 0 ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) * Real.exp (2 + 24 * Clog * Real.log 2) *
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) := by
    have hm := HalberstamScratch.explicitMassConstant_nonneg
      hlambda1 hlambda2
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by linarith [hm]) (Nat.cast_nonneg N))
        (Real.exp_pos _).le)
      (Real.rpow_nonneg TauInvTypeMean448.cleanMertensConstant_pos.le _)
  have hcancel :
      (N : ℝ) / Real.log (N : ℝ) *
          (Real.log (N : ℝ)) ^ (1 / 4 : ℝ) =
        (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4) := by
    calc
      (N : ℝ) / Real.log (N : ℝ) *
          (Real.log (N : ℝ)) ^ (1 / 4 : ℝ) =
        (N : ℝ) * ((Real.log (N : ℝ))⁻¹ *
          (Real.log (N : ℝ)) ^ (1 / 4 : ℝ)) := by ring
      _ = (N : ℝ) * ((Real.log (N : ℝ)) ^ (-(1 : ℝ)) *
          (Real.log (N : ℝ)) ^ (1 / 4 : ℝ)) := by rw [Real.rpow_neg_one]
      _ = (N : ℝ) * (Real.log (N : ℝ)) ^
          (-(1 : ℝ) + 1 / 4) := by rw [Real.rpow_add hlogN]
      _ = (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4) := by
        congr 2
        ring
  change weightedTSum u q k 2 (N + 1) ≤ _
  calc
    weightedTSum u q k 2 (N + 1) ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          (Real.exp ((1 / 4 : ℝ) *
              Real.log (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) +
            2 + 24 * Clog * Real.log 2) *
            hybridCorrectionWeight u (omegaWeightAF k) q) := hraw
    _ = (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) * Real.exp (2 + 24 * Clog * Real.log 2) *
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
        (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4) *
        hybridCorrectionWeight u (omegaWeightAF k) q := by
      rw [hexpSplit, hexpQuarter]
      rw [show
        (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
              (N : ℝ) / Real.log (N : ℝ) *
              (TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
                (Real.log (N : ℝ)) ^ (1 / 4 : ℝ) *
                Real.exp (2 + 24 * Clog * Real.log 2) *
                hybridCorrectionWeight u (omegaWeightAF k) q) =
            (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
              Real.exp (2 + 24 * Clog * Real.log 2) *
              TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
              ((N : ℝ) / Real.log (N : ℝ) *
                (Real.log (N : ℝ)) ^ (1 / 4 : ℝ)) *
              hybridCorrectionWeight u (omegaWeightAF k) q by ring,
        hcancel]
      ring
    _ ≤ (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) * Real.exp (2 + 24 * Clog * Real.log 2) *
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
        (((k : ℝ) * Real.log 2) ^ (-(3 : ℝ) / 4)) *
        hybridCorrectionWeight u (omegaWeightAF k) q := by
      have hcore := mul_le_mul_of_nonneg_left hrpow hcoeff
      have hout := mul_le_mul_of_nonneg_right hcore hhybrid
      convert hout using 1 <;> ring
    _ = weightedShiftedDyadicConstant Clog lambda1 lambda2 *
        ((2 ^ k : ℕ) : ℝ) * (k : ℝ) ^ (-(3 : ℝ) / 4) *
        hybridCorrectionWeight u (omegaWeightAF k) q := by
      have hNcast : (N : ℝ) = 4 * ((2 ^ k : ℕ) : ℝ) := by
        dsimp [N]
        norm_num [pow_add]
        ring
      rw [hNcast, Real.mul_rpow hkR.le hlog2.le]
      unfold weightedShiftedDyadicConstant
      ring

/-! ## Discharging the normalized HR hypothesis for the genuine first correction -/

noncomputable def sharpShiftedReciprocalWeightAF : ArithmeticFunction ℝ :=
  ⟨Prop3ShiftedMean448.sharpShiftedReciprocalWeight, by
    simp [Prop3ShiftedMean448.sharpShiftedReciprocalWeight]⟩

@[simp] lemma sharpShiftedReciprocalWeightAF_apply (n : ℕ) :
    sharpShiftedReciprocalWeightAF n =
      Prop3ShiftedMean448.sharpShiftedReciprocalWeight n := rfl

@[simp] lemma sharpShiftedReciprocalWeightAF_one :
    sharpShiftedReciprocalWeightAF 1 = 1 := by
  simp [sharpShiftedReciprocalWeightAF,
    Prop3ShiftedMean448.sharpShiftedReciprocalWeight]

lemma sharpShiftedReciprocalWeightAF_multiplicative :
    sharpShiftedReciprocalWeightAF.IsMultiplicative := by
  refine ⟨sharpShiftedReciprocalWeightAF_one, ?_⟩
  intro m n hmn
  exact Prop3ShiftedMean448.sharpShiftedReciprocalWeight_mul_of_coprime hmn

lemma sharpShiftedReciprocalWeightAF_nonneg (n : ℕ) :
    0 ≤ sharpShiftedReciprocalWeightAF n :=
  Prop3ShiftedMean448.sharpShiftedReciprocalWeight_nonneg n

lemma sharpShiftedReciprocalWeightAF_pos {n : ℕ} (hn : n ≠ 0) :
    0 < sharpShiftedReciprocalWeightAF n := by
  rw [sharpShiftedReciprocalWeightAF_apply,
    Prop3ShiftedMean448.sharpShiftedReciprocalWeight, if_neg hn]
  have hcard : (0 : ℝ) < n.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  apply mul_pos (one_div_pos.mpr hcard)
  apply Finset.prod_pos
  intro p hp
  exact lt_of_lt_of_le zero_lt_one
    (Prop3ShiftedMean448.one_le_sharpLocalCorrection
      (Nat.prime_of_mem_primeFactors hp))

lemma sharpShiftedReciprocalWeightAF_prime_pow
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu) :
    sharpShiftedReciprocalWeightAF (p ^ nu) =
      Prop3ShiftedMean448.sharpLocalCorrection p / (nu + 1 : ℝ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.one_le_iff_ne_zero.mp hnu)
  rw [sharpShiftedReciprocalWeightAF_apply]
  convert Prop3ShiftedMean448.sharpShiftedReciprocalWeight_prime_pow_succ
      (p := p) (nu := j) hp using 1
  push_cast
  ring

lemma sharpLocalCorrection_le_two {p : ℕ} (hp : p.Prime) :
    Prop3ShiftedMean448.sharpLocalCorrection p ≤ 2 := by
  unfold Prop3ShiftedMean448.sharpLocalCorrection
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : (0 : ℝ) < 2 * p - 1 := by nlinarith
  rw [div_le_iff₀ hden]
  nlinarith

lemma sharpShiftedReciprocalWeightAF_prime_pow_le_one
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu) :
    sharpShiftedReciprocalWeightAF (p ^ nu) ≤ 1 := by
  rw [sharpShiftedReciprocalWeightAF_prime_pow hp hnu]
  have hden : (2 : ℝ) ≤ (nu : ℝ) + 1 := by exact_mod_cast (by omega : 2 ≤ nu + 1)
  have hdenPos : (0 : ℝ) < (nu : ℝ) + 1 := by positivity
  apply (div_le_one hdenPos).2
  exact (sharpLocalCorrection_le_two hp).trans hden

lemma sharpShiftedReciprocalWeightAF_ratio_le_one
    {p i j : ℕ} (hp : p.Prime) :
    sharpShiftedReciprocalWeightAF (p ^ (i + (j + 1))) /
        sharpShiftedReciprocalWeightAF (p ^ i) ≤ 1 := by
  by_cases hi : i = 0
  · subst i
    simp only [zero_add, pow_zero, sharpShiftedReciprocalWeightAF_one, div_one]
    exact sharpShiftedReciprocalWeightAF_prime_pow_le_one hp (by omega)
  · have hiOne : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
    have hijOne : 1 ≤ i + (j + 1) := by omega
    rw [sharpShiftedReciprocalWeightAF_prime_pow hp hijOne,
      sharpShiftedReciprocalWeightAF_prime_pow hp hiOne]
    have hLpos : 0 < Prop3ShiftedMean448.sharpLocalCorrection p :=
      zero_lt_one.trans_le
        (Prop3ShiftedMean448.one_le_sharpLocalCorrection hp)
    have hiPos : (0 : ℝ) < (i + 1 : ℕ) := by positivity
    have hijPos : (0 : ℝ) < (i + (j + 1) + 1 : ℕ) := by positivity
    have heq :
        (Prop3ShiftedMean448.sharpLocalCorrection p /
            ((i + (j + 1) + 1 : ℕ) : ℝ)) /
          (Prop3ShiftedMean448.sharpLocalCorrection p /
            ((i + 1 : ℕ) : ℝ)) =
          ((i + 1 : ℕ) : ℝ) / ((i + (j + 1) + 1 : ℕ) : ℝ) := by
      field_simp [hLpos.ne', hiPos.ne', hijPos.ne']
    push_cast at heq ⊢
    rw [heq]
    apply (div_le_one (by positivity : (0 : ℝ) < i + (j + 1) + 1)).2
    exact_mod_cast (show i + 1 ≤ i + (j + 1) + 1 by omega)

lemma sharpShiftedReciprocalWeightAF_weighted_normalized_le
    (k : ℕ) {p i j : ℕ} (hp : p.Prime) :
    sharpShiftedReciprocalWeightAF (p ^ (i + (j + 1))) *
          omegaWeightAF k (p ^ (j + 1)) /
        sharpShiftedReciprocalWeightAF (p ^ i) ≤ 1 := by
  have hratio := sharpShiftedReciprocalWeightAF_ratio_le_one
    (p := p) (i := i) (j := j) hp
  have hdenPos : 0 < sharpShiftedReciprocalWeightAF (p ^ i) := by
    apply sharpShiftedReciprocalWeightAF_pos
    exact pow_ne_zero _ hp.ne_zero
  have hnum : 0 ≤ sharpShiftedReciprocalWeightAF (p ^ (i + (j + 1))) :=
    sharpShiftedReciprocalWeightAF_nonneg _
  have hratioNonneg : 0 ≤
      sharpShiftedReciprocalWeightAF (p ^ (i + (j + 1))) /
        sharpShiftedReciprocalWeightAF (p ^ i) :=
    div_nonneg hnum hdenPos.le
  have homega := omegaWeightAF_le_one k (p ^ (j + 1))
  calc
    sharpShiftedReciprocalWeightAF (p ^ (i + (j + 1))) *
          omegaWeightAF k (p ^ (j + 1)) /
        sharpShiftedReciprocalWeightAF (p ^ i) =
      (sharpShiftedReciprocalWeightAF (p ^ (i + (j + 1))) /
        sharpShiftedReciprocalWeightAF (p ^ i)) *
          omegaWeightAF k (p ^ (j + 1)) := by ring
    _ ≤ (sharpShiftedReciprocalWeightAF (p ^ (i + (j + 1))) /
        sharpShiftedReciprocalWeightAF (p ^ i)) * 1 :=
      mul_le_mul_of_nonneg_left homega hratioNonneg
    _ ≤ 1 := by simpa using hratio

lemma sharpShiftedReciprocalWeightAF_prime_pow_close_inv
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu) :
    |sharpShiftedReciprocalWeightAF (p ^ nu) -
        1 / ((nu + 1 : ℕ) : ℝ)| ≤ (p : ℝ)⁻¹ := by
  rw [sharpShiftedReciprocalWeightAF_prime_pow hp hnu]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdenNu : (0 : ℝ) < (nu : ℝ) + 1 := by positivity
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold Prop3ShiftedMean448.sharpLocalCorrection
  have hdenP : (0 : ℝ) < 2 * p - 1 := by nlinarith
  have hdiff :
      (2 * (p : ℝ) / (2 * p - 1)) / ((nu : ℝ) + 1) -
          1 / ((nu : ℝ) + 1) =
        1 / ((2 * p - 1) * ((nu : ℝ) + 1)) := by
    field_simp [hdenP.ne', hdenNu.ne']
    ring
  push_cast
  rw [hdiff, abs_of_pos (by positivity)]
  have hdenGe : (p : ℝ) ≤ (2 * p - 1) * ((nu : ℝ) + 1) := by
    have hnuGe : (1 : ℝ) ≤ (nu : ℝ) + 1 := by
      exact_mod_cast (show 1 ≤ nu + 1 by omega)
    nlinarith
  simpa [one_div] using one_div_le_one_div_of_le hpR hdenGe

lemma sharpShiftedReciprocalWeightAF_logType :
    TauInvCorrection448.IsTauInverseLogType sharpShiftedReciprocalWeightAF 1 := by
  refine ⟨zero_le_one, ?_⟩
  intro p nu hp hnu
  have hlocal := sharpShiftedReciprocalWeightAF_prime_pow_close_inv hp hnu
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  calc
    |sharpShiftedReciprocalWeightAF (p ^ nu) -
        1 / ((nu + 1 : ℕ) : ℝ)| ≤ (p : ℝ)⁻¹ := hlocal
    _ ≤ (1 + Real.log (p : ℝ)) / (p : ℝ) := by
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith) hpR.le
    _ = 1 * (1 + Real.log (p : ℝ)) / (p : ℝ) := by ring

lemma sharpShiftedReciprocalWeightAF_powType :
    IsTauInverseType sharpShiftedReciprocalWeightAF 1 1 := by
  refine ⟨zero_le_one, zero_lt_one, ?_⟩
  intro p nu hp hnu
  simpa [Real.rpow_neg_one] using
    (sharpShiftedReciprocalWeightAF_prime_pow_close_inv hp hnu)

/-- Fully unconditional specialization for the concrete first correction:
the normalized prime-power hypothesis of HR is proved above with
`lambda1=lambda2=1`. -/
theorem sharpWeightedTSum_dyadic_le
    {q : ℕ} (hq : q ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    weightedTSum sharpShiftedReciprocalWeightAF q k 2
        (2 ^ (k + 2) + 1) ≤
      weightedShiftedDyadicConstant 1 1 1 *
        ((2 ^ k : ℕ) : ℝ) * (k : ℝ) ^ (-(3 : ℝ) / 4) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q := by
  apply weightedTSum_dyadic_le sharpShiftedReciprocalWeightAF
    sharpShiftedReciprocalWeightAF_multiplicative
    sharpShiftedReciprocalWeightAF_one
    sharpShiftedReciprocalWeightAF_nonneg
    (fun n hn => sharpShiftedReciprocalWeightAF_pos hn)
    (Cpow := 1) (delta := 1) zero_le_one zero_lt_one
    sharpShiftedReciprocalWeightAF_powType
    sharpShiftedReciprocalWeightAF_logType hq 1 1 zero_le_one zero_le_one
    (by norm_num) k hk
  intro p hp j
  simpa using sharpShiftedReciprocalWeightAF_weighted_normalized_le
    k (p := p) (i := q.factorization p) (j := j) hp

/-- The concrete output correction in `sharpWeightedTSum_dyadic_le` is
itself a bundled logarithmic-`tau`-inverse-type multiplicative function,
uniformly in the scale `k`. -/
theorem sharpHybridCorrection_meanType (k : ℕ) :
    TauInvTypeMean448.IsTauInverseLogType
      (hybridCorrectionWeight sharpShiftedReciprocalWeightAF
        (omegaWeightAF k)) 99 := by
  let w : ℕ → ℝ := hybridCorrectionWeight sharpShiftedReciprocalWeightAF
    (omegaWeightAF k)
  have hlocal : TauInvCorrection448.IsTauInverseLogType w 33 := by
    convert hybridCorrectionWeight_isTauInverseLogType
      sharpShiftedReciprocalWeightAF (omegaWeightAF k)
      sharpShiftedReciprocalWeightAF_one (omegaWeightAF_one k)
      sharpShiftedReciprocalWeightAF_nonneg (omegaWeightAF_nonneg k)
      sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) using 1 <;>
      simp [w] <;> norm_num
  refine
    { C_nonneg := by norm_num
      map_zero := hybridCorrectionWeight_zero _ _
      map_one := hybridCorrectionWeight_one _ _
      map_mul_of_coprime := fun hmn =>
        hybridCorrectionWeight_mul_of_coprime _ _ hmn
      nonneg := fun n =>
        hybridCorrectionWeight_nonneg
          sharpShiftedReciprocalWeightAF (omegaWeightAF k)
          sharpShiftedReciprocalWeightAF_one (omegaWeightAF_one k)
          sharpShiftedReciprocalWeightAF_nonneg (omegaWeightAF_nonneg k)
          sharpShiftedReciprocalWeightAF_logType
          (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) n
      prime_pow_close := ?_ }
  intro p nu hp hnu
  have h := hlocal.2 hp hnu
  have hscale := TauInvCorrection448.one_add_log_le_three_log hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    |w (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)| ≤
        33 * (1 + Real.log (p : ℝ)) / (p : ℝ) := h
    _ ≤ 33 * (3 * Real.log (p : ℝ)) / (p : ℝ) := by
      apply div_le_div_of_nonneg_right _ hpR.le
      exact mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = 99 * Real.log (p : ℝ) / (p : ℝ) := by ring

/-! ## Uniform Mertens input for arbitrary residual length -/

/-- A positive constant in the weak Mertens lower bound.  It is kept
separate from the upper-bound constant because the two asymptotic estimates
have different witnesses. -/
noncomputable def cleanMertensLowerConstant : ℝ :=
  Classical.choose weak_mertens_third_lower_all

lemma cleanMertensLowerConstant_pos : 0 < cleanMertensLowerConstant :=
  (Classical.choose_spec weak_mertens_third_lower_all).1

lemma cleanMertensLowerConstant_mul_log_le_partialEulerProduct
    (N : ℕ) (hN : 1 ≤ N) :
    cleanMertensLowerConstant * Real.log (N : ℝ) ≤
      partial_euler_product N := by
  have h := (Classical.choose_spec weak_mertens_third_lower_all).2
    (N : ℝ) (by exact_mod_cast hN)
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hprod : 0 ≤ partial_euler_product N :=
    zero_le_one.trans partial_euler_trivial_lower_bound
  change (Classical.choose weak_mertens_third_lower_all) *
    Real.log (N : ℝ) ≤ _
  simpa [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hprod] using h

/-- Lower reciprocal-prime estimate with coefficient one.  The additive
constant is the elementary convergent correction
`sum 1/(p*(p-1)) ≤ 1`. -/
theorem reciprocal_prime_sum_lower (N : ℕ) (hN : 2 ≤ N) :
    Real.log (cleanMertensLowerConstant * Real.log (N : ℝ)) - 1 ≤
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) := by
  classical
  let P : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  have hterm : ∀ p ∈ P,
      -Real.log (1 - 1 / (p : ℝ)) ≤
        (1 : ℝ) / (p : ℝ) +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hpP
    have hp : p.Prime := (Finset.mem_filter.mp hpP).2
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hbase : 0 < (1 : ℝ) - 1 / (p : ℝ) := by
      exact sub_pos.mpr (by simpa [one_div] using inv_lt_one_of_one_lt₀ hpR)
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hbase)
    have hinvLog : Real.log ((1 - 1 / (p : ℝ))⁻¹) =
        -Real.log (1 - 1 / (p : ℝ)) := by
      rw [Real.log_inv]
    have halg :
        (1 - 1 / (p : ℝ))⁻¹ - 1 =
          (1 : ℝ) / (p : ℝ) +
            1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp [hp0, hp1]
      ring
    rw [hinvLog, halg] at hlog
    exact hlog
  have hlogProduct :
      Real.log (partial_euler_product N) ≤
        (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) +
          ∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    calc
      Real.log (partial_euler_product N) =
          ∑ p ∈ P, -Real.log (1 - 1 / (p : ℝ)) := by
        rw [show partial_euler_product N =
            ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ by
          simp [P, partial_euler_product]]
        rw [Real.log_prod]
        · apply Finset.sum_congr rfl
          intro p hpP
          rw [Real.log_inv]
        · intro p hpP
          have hp : p.Prime := (Finset.mem_filter.mp hpP).2
          have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
          exact inv_ne_zero (ne_of_gt (sub_pos.mpr
            (by simpa [one_div] using inv_lt_one_of_one_lt₀ hpR)))
      _ ≤ ∑ p ∈ P,
          ((1 : ℝ) / (p : ℝ) +
            1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        Finset.sum_le_sum hterm
      _ = (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) +
          ∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        rw [Finset.sum_add_distrib]
  have hcorr :
      (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
    have hsub : P ⊆ Finset.Icc 2 N := by
      intro p hpP
      have hpP' : p ∈ (Finset.Icc 1 N).filter Nat.Prime := by
        simpa [P] using hpP
      have hp' := Finset.mem_filter.mp hpP'
      exact Finset.mem_Icc.mpr
        ⟨hp'.2.two_le, (Finset.mem_Icc.mp hp'.1).2⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ => by
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        exact div_nonneg zero_le_one
          (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (by linarith))))).trans
      (TauInvTypeMean448.sum_Icc_two_inv_mul_pred_le_one N)
  have hclogPos : 0 < cleanMertensLowerConstant * Real.log (N : ℝ) := by
    exact mul_pos cleanMertensLowerConstant_pos
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  have hprodPos : 0 < partial_euler_product N :=
    zero_lt_one.trans_le partial_euler_trivial_lower_bound
  have hlogLower := Real.log_le_log hclogPos
    (cleanMertensLowerConstant_mul_log_le_partialEulerProduct N (by omega))
  change Real.log (cleanMertensLowerConstant * Real.log (N : ℝ)) - 1 ≤ _
  change _ ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ)
  linarith

/-- The clean upper reciprocal-prime estimate also holds at the endpoint
`N=2`; the proof of the imported version only recorded `N≥3`. -/
theorem reciprocal_prime_sum_upper_of_two (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ)) ≤
        Real.log (TauInvTypeMean448.cleanMertensConstant *
          Real.log (N : ℝ)) := by
  by_cases hN3 : 3 ≤ N
  · exact TauInvTypeMean448.reciprocal_prime_sum_upper N hN3
  · have hNeq : N = 2 := by omega
    subst N
    have hset : (Finset.Icc 1 2).filter Nat.Prime = {2} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hp1, hp2⟩, hp⟩
        exact le_antisymm hp2 hp.two_le
      · intro hp
        subst p
        norm_num
    have hupper := TauInvTypeMean448.partialEulerProduct_le_cleanMertens 2
      (by norm_num)
    have hprodPos : 0 < partial_euler_product 2 :=
      zero_lt_one.trans_le partial_euler_trivial_lower_bound
    have hlogUpper := Real.log_le_log hprodPos hupper
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) Real.log_two_gt_d9.le
    have hprod : partial_euler_product 2 = 2 := by
      rw [partial_euler_product, hset]
      norm_num
    rw [hprod] at hlogUpper
    rw [hset]
    norm_num
    exact hhalf.trans hlogUpper

private lemma primesBelow_succ_eq_filter_Icc (N : ℕ) :
    (N + 1).primesBelow = (Finset.Icc 1 N).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hpN, hp⟩
    exact ⟨⟨hp.one_le, Nat.le_of_lt_succ hpN⟩, hp⟩
  · rintro ⟨⟨_, hpN⟩, hp⟩
    exact ⟨Nat.lt_succ_of_le hpN, hp⟩

private lemma mixed_secondary_sum_le_one (N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow,
      1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
  classical
  have hsub : (N + 1).primesBelow ⊆ Finset.Icc 2 N := by
    intro p hpP
    have hp' := Nat.mem_primesBelow.mp hpP
    exact Finset.mem_Icc.mpr
      ⟨hp'.2.two_le, Nat.le_of_lt_succ hp'.1⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n hn _ => by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      exact div_nonneg zero_le_one
        (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (by linarith))))).trans
    (TauInvTypeMean448.sum_Icc_two_inv_mul_pred_le_one N)

private lemma mixed_error_sum_le (N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow,
      6 * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) ≤
        24 * Real.log 2 := by
  classical
  rw [← Finset.mul_sum]
  calc
    6 * ∑ p ∈ (N + 1).primesBelow,
        Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
      6 * (4 * Real.log 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [primesBelow_succ_eq_filter_Icc]
        have hset : (Finset.Icc 1 N).filter Nat.Prime = Nat.primesLE N := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
          constructor
          · rintro ⟨⟨_, hpN⟩, hp⟩
            exact ⟨hpN, hp⟩
          · rintro ⟨hpN, hp⟩
            exact ⟨⟨hp.one_le, hpN⟩, hp⟩
        rw [hset]
        exact TauInvTypeMean448.sum_primesLE_log_div_sq_le N
    _ = 24 * Real.log 2 := by ring

/-- Mixed Euler exponent in the middle regime `N < 2^k`. -/
theorem sum_mixedLocalExponent_middle_le
    (N k : ℕ) (hN : 2 ≤ N) (hNk : N < 2 ^ k) :
    (∑ p ∈ (N + 1).primesBelow,
        WeightedTauInv448.mixedLocalExponent 3 k p) ≤
      (1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) +
        1 + 24 * Real.log 2 := by
  classical
  have hbase :
      (∑ p ∈ (N + 1).primesBelow,
        (if p < 2 ^ k then (1 : ℝ) / (4 * (p : ℝ))
          else 1 / (2 * (p : ℝ)))) ≤
        (1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) := by
    have hall : ∀ p ∈ (N + 1).primesBelow, p < 2 ^ k := by
      intro p hpP
      exact (Nat.mem_primesBelow.mp hpP).1.trans_le (Nat.succ_le_iff.mp hNk)
    rw [show (∑ p ∈ (N + 1).primesBelow,
        (if p < 2 ^ k then (1 : ℝ) / (4 * (p : ℝ))
          else 1 / (2 * (p : ℝ)))) =
        ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / (4 * (p : ℝ)) by
      apply Finset.sum_congr rfl
      intro p hpP
      rw [if_pos (hall p hpP)]]
    calc
      (∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / (4 * (p : ℝ))) =
          (1 / 4 : ℝ) *
            ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / (p : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hpP
        ring
      _ ≤ (1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) := by
        rw [primesBelow_succ_eq_filter_Icc]
        exact mul_le_mul_of_nonneg_left
          (reciprocal_prime_sum_upper_of_two N hN) (by norm_num)
  have hsecondary := mixed_secondary_sum_le_one N
  have herr := mixed_error_sum_le N
  simp_rw [WeightedTauInv448.mixedLocalExponent,
    Finset.sum_add_distrib]
  linarith

/-- Mixed Euler exponent in the large regime.  For `k≥2`, the missing
quarter of the prime mass below `2^k` is recovered from the weak Mertens
lower bound. -/
theorem sum_mixedLocalExponent_large_le
    (N k : ℕ) (hN : 2 ≤ N) (hk : 2 ≤ k) (hkN : 2 ^ k ≤ N) :
    (∑ p ∈ (N + 1).primesBelow,
        WeightedTauInv448.mixedLocalExponent 3 k p) ≤
      (1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) -
        (1 / 4 : ℝ) * Real.log
          (cleanMertensLowerConstant * Real.log ((2 ^ k : ℕ) : ℝ)) +
        (5 / 4 : ℝ) + 24 * Real.log 2 := by
  classical
  let Y : ℕ := 2 ^ k
  let P : Finset ℕ := (N + 1).primesBelow
  have hY2 : 2 ≤ Y := by
    dsimp [Y]
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
    omega
  have hYcomp : ¬Nat.Prime Y := by
    intro hprime
    have h2dvd : 2 ∣ Y := by
      dsimp [Y]
      exact dvd_pow_self 2 (by omega : k ≠ 0)
    have hEq : 2 = Y :=
      (Nat.dvd_prime_two_le hprime (by norm_num)).mp h2dvd
    have hfour : 4 ≤ Y := by
      dsimp [Y]
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
      simpa using this
    omega
  have hsmallSet :
      P.filter (fun p => p < Y) = (Finset.Icc 1 Y).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, P, Nat.mem_primesBelow, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hpN, hp⟩, hpY⟩
      exact ⟨⟨hp.one_le, Nat.le_of_lt hpY⟩, hp⟩
    · rintro ⟨⟨_, hpY⟩, hp⟩
      have hpYlt : p < Y := lt_of_le_of_ne hpY (by
        intro hEq
        apply hYcomp
        simpa [hEq] using hp)
      exact ⟨⟨Nat.lt_succ_of_lt (lt_of_lt_of_le hpYlt hkN), hp⟩, hpYlt⟩
  have hsplit :
      (∑ p ∈ P, if p < Y then (1 : ℝ) / (4 * (p : ℝ))
          else 1 / (2 * (p : ℝ))) =
        (1 / 2 : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) -
          (1 / 4 : ℝ) *
            (∑ p ∈ P.filter (fun p => p < Y), (1 : ℝ) / (p : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hpP
    by_cases hpY : p < Y <;> simp [hpY] <;> ring
  have hupper :
      (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ≤
        Real.log (TauInvTypeMean448.cleanMertensConstant *
          Real.log (N : ℝ)) := by
    rw [show P = (Finset.Icc 1 N).filter Nat.Prime by
      simpa [P] using primesBelow_succ_eq_filter_Icc N]
    exact reciprocal_prime_sum_upper_of_two N hN
  have hlower :
      Real.log (cleanMertensLowerConstant * Real.log (Y : ℝ)) - 1 ≤
        ∑ p ∈ P.filter (fun p => p < Y), (1 : ℝ) / (p : ℝ) := by
    rw [hsmallSet]
    exact reciprocal_prime_sum_lower Y hY2
  have hbase :
      (∑ p ∈ P, if p < Y then (1 : ℝ) / (4 * (p : ℝ))
          else 1 / (2 * (p : ℝ))) ≤
        (1 / 2 : ℝ) * Real.log
            (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) -
          (1 / 4 : ℝ) * Real.log
            (cleanMertensLowerConstant * Real.log (Y : ℝ)) + 1 / 4 := by
    rw [hsplit]
    nlinarith
  have hsecondary := mixed_secondary_sum_le_one N
  have herr := mixed_error_sum_le N
  change (∑ p ∈ P,
    WeightedTauInv448.mixedLocalExponent 3 k p) ≤ _
  simp_rw [WeightedTauInv448.mixedLocalExponent,
    Finset.sum_add_distrib]
  simp only [show (2 : ℝ) * 3 = 6 by norm_num]
  change
    (∑ p ∈ P, if p < 2 ^ k then (1 : ℝ) / (4 * (p : ℝ))
      else 1 / (2 * (p : ℝ))) +
      (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) +
      (∑ p ∈ P, 6 * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) ≤ _
  dsimp [Y] at hbase
  linarith

/-- Crude half-density exponent bound, used only for the exceptional
cutoff `k=1`. -/
theorem sum_mixedLocalExponent_crude_le
    (N k : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ (N + 1).primesBelow,
        WeightedTauInv448.mixedLocalExponent 3 k p) ≤
      (1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) +
        1 + 24 * Real.log 2 := by
  classical
  have hbase :
      (∑ p ∈ (N + 1).primesBelow,
        (if p < 2 ^ k then (1 : ℝ) / (4 * (p : ℝ))
          else 1 / (2 * (p : ℝ)))) ≤
        (1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) := by
    calc
      (∑ p ∈ (N + 1).primesBelow,
          (if p < 2 ^ k then (1 : ℝ) / (4 * (p : ℝ))
            else 1 / (2 * (p : ℝ)))) ≤
          ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / (2 * (p : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hpP
        by_cases hp : p < 2 ^ k
        · rw [if_pos hp]
          have hpPos : (0 : ℝ) < p := by
            exact_mod_cast (Nat.prime_of_mem_primesBelow hpP).pos
          have hden : 0 < 2 * (p : ℝ) := by positivity
          exact one_div_le_one_div_of_le hden (by nlinarith)
        · rw [if_neg hp]
      _ = (1 / 2 : ℝ) *
          ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / (p : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hpP
        ring
      _ ≤ (1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) := by
        rw [primesBelow_succ_eq_filter_Icc]
        exact mul_le_mul_of_nonneg_left
          (reciprocal_prime_sum_upper_of_two N hN) (by norm_num)
  have hsecondary := mixed_secondary_sum_le_one N
  have herr := mixed_error_sum_le N
  simp_rw [WeightedTauInv448.mixedLocalExponent,
    Finset.sum_add_distrib]
  linarith

/-- The concrete sharp first correction in the coefficient-one global
logarithmic interface used by `WeightedTauInv448`. -/
theorem sharpShiftedReciprocalWeightAF_meanType :
    TauInvTypeMean448.IsTauInverseLogType
      sharpShiftedReciprocalWeightAF 3 := by
  refine
    { C_nonneg := by norm_num
      map_zero := sharpShiftedReciprocalWeightAF.map_zero
      map_one := sharpShiftedReciprocalWeightAF_one
      map_mul_of_coprime := fun hmn =>
        sharpShiftedReciprocalWeightAF_multiplicative.map_mul_of_coprime hmn
      nonneg := sharpShiftedReciprocalWeightAF_nonneg
      prime_pow_close := ?_ }
  intro p nu hp hnu
  have hlocal := sharpShiftedReciprocalWeightAF_prime_pow_close_inv hp hnu
  have hscale := TauInvCorrection448.one_add_log_le_three_log hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    |sharpShiftedReciprocalWeightAF (p ^ nu) -
        1 / ((nu + 1 : ℕ) : ℝ)| ≤ (1 : ℝ) / (p : ℝ) := by
      simpa [one_div] using hlocal
    _ ≤ (1 + Real.log (p : ℝ)) / (p : ℝ) := by
      apply div_le_div_of_nonneg_right _ hpR.le
      have hlog : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hp.one_le)
      linarith
    _ ≤ (3 * Real.log (p : ℝ)) / (p : ℝ) :=
      div_le_div_of_nonneg_right hscale hpR.le
    _ = 3 * Real.log (p : ℝ) / (p : ℝ) := rfl

private theorem sharp_diagonalEuler_product_le_exp_sum (N k : ℕ) :
    (∏ p ∈ (N + 1).primesBelow,
        ErdosTenenbaumLemma2Scratch.diagonalEuler
          sharpShiftedReciprocalWeightAF (omegaWeightAF k) p) ≤
      Real.exp (∑ p ∈ (N + 1).primesBelow,
        WeightedTauInv448.mixedLocalExponent 3 k p) := by
  classical
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ErdosTenenbaumLemma2Scratch.diagonalEuler
          sharpShiftedReciprocalWeightAF (omegaWeightAF k) p) ≤
      ∏ p ∈ (N + 1).primesBelow,
        Real.exp (WeightedTauInv448.mixedLocalExponent 3 k p) := by
          apply Finset.prod_le_prod
          · intro p hpP
            unfold ErdosTenenbaumLemma2Scratch.diagonalEuler
            exact tsum_nonneg fun j =>
              div_nonneg
                (mul_nonneg (sharpShiftedReciprocalWeightAF_nonneg _)
                  (omegaWeightAF_nonneg k _))
                (Nat.cast_nonneg _)
          · intro p hpP
            have h := WeightedTauInv448.weighted_localEuler_le_exp
              sharpShiftedReciprocalWeightAF_meanType k
              (Nat.prime_of_mem_primesBelow hpP)
            change
              (∑' j : ℕ,
                sharpShiftedReciprocalWeightAF (p ^ j) *
                    omegaWeightAF k (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤ _
            exact h
    _ = Real.exp (∑ p ∈ (N + 1).primesBelow,
        WeightedTauInv448.mixedLocalExponent 3 k p) := by
      rw [Real.exp_sum]

theorem sharp_diagonalEuler_product_middle_le
    (N k : ℕ) (hN : 2 ≤ N) (hNk : N < 2 ^ k) :
    (∏ p ∈ (N + 1).primesBelow,
        ErdosTenenbaumLemma2Scratch.diagonalEuler
          sharpShiftedReciprocalWeightAF (omegaWeightAF k) p) ≤
      Real.exp ((1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) +
        1 + 24 * Real.log 2) := by
  exact (sharp_diagonalEuler_product_le_exp_sum N k).trans
    (Real.exp_le_exp.mpr (sum_mixedLocalExponent_middle_le N k hN hNk))

theorem sharp_diagonalEuler_product_large_le
    (N k : ℕ) (hN : 2 ≤ N) (hk : 2 ≤ k) (hkN : 2 ^ k ≤ N) :
    (∏ p ∈ (N + 1).primesBelow,
        ErdosTenenbaumLemma2Scratch.diagonalEuler
          sharpShiftedReciprocalWeightAF (omegaWeightAF k) p) ≤
      Real.exp ((1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) -
        (1 / 4 : ℝ) * Real.log
          (cleanMertensLowerConstant * Real.log ((2 ^ k : ℕ) : ℝ)) +
        (5 / 4 : ℝ) + 24 * Real.log 2) := by
  exact (sharp_diagonalEuler_product_le_exp_sum N k).trans
    (Real.exp_le_exp.mpr (sum_mixedLocalExponent_large_le N k hN hk hkN))

theorem sharp_diagonalEuler_product_crude_le
    (N k : ℕ) (hN : 2 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow,
        ErdosTenenbaumLemma2Scratch.diagonalEuler
          sharpShiftedReciprocalWeightAF (omegaWeightAF k) p) ≤
      Real.exp ((1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (N : ℝ)) +
        1 + 24 * Real.log 2) := by
  exact (sharp_diagonalEuler_product_le_exp_sum N k).trans
    (Real.exp_le_exp.mpr (sum_mixedLocalExponent_crude_le N k hN))

/-! ## The unconditional arbitrary-residual estimate -/

lemma weightedTSum_le_succ
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (q k sigma z : ℕ) :
    weightedTSum w q k sigma z ≤ weightedTSum w q k sigma (z + 1) := by
  unfold weightedTSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    have ht' := Finset.mem_Ico.mp ht
    exact Finset.mem_Ico.mpr ⟨ht'.1, ht'.2.trans (Nat.lt_succ_self z)⟩
  · intro t ht _
    exact weightedTKernel_nonneg w hw q k sigma t

/-- HR Lemma 2 specialized to the concrete sharp first correction, at an
arbitrary mean-value length. -/
theorem sharpWeightedTSum_succ_le_HR
    {q : ℕ} (hq : q ≠ 0) (k N : ℕ) (hN : 2 ≤ N) :
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 (N + 1) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ((∏ p ∈ (N + 1).primesBelow,
              ErdosTenenbaumLemma2Scratch.diagonalEuler
                sharpShiftedReciprocalWeightAF (omegaWeightAF k) p) *
            hybridCorrectionWeight sharpShiftedReciprocalWeightAF
              (omegaWeightAF k) q) := by
  apply weightedTSum_succ_le_HR_corrected
    sharpShiftedReciprocalWeightAF
    sharpShiftedReciprocalWeightAF_multiplicative
    sharpShiftedReciprocalWeightAF_one
    sharpShiftedReciprocalWeightAF_nonneg
    (fun n hn => sharpShiftedReciprocalWeightAF_pos hn)
    (Cpow := 1) (delta := 1) zero_le_one zero_lt_one
    sharpShiftedReciprocalWeightAF_powType
    sharpShiftedReciprocalWeightAF_logType hq 1 1 zero_le_one zero_le_one
    (by norm_num) k ?_ N hN
  intro p hp j
  simpa using sharpShiftedReciprocalWeightAF_weighted_normalized_le
    k (p := p) (i := q.factorization p) (j := j) hp

noncomputable def sharpWeightedMiddleConstant : ℝ :=
  (HalberstamScratch.explicitMassConstant 1 1 + 1) *
    Real.exp (1 + 24 * Real.log 2) *
    TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
    (Real.log 2) ^ (1 / 4 : ℝ)

noncomputable def sharpWeightedLargeConstant : ℝ :=
  (HalberstamScratch.explicitMassConstant 1 1 + 1) *
    Real.exp ((5 / 4 : ℝ) + 24 * Real.log 2) *
    TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
    cleanMertensLowerConstant ^ (-(1 : ℝ) / 4)

noncomputable def sharpWeightedLargeOneConstant : ℝ :=
  (HalberstamScratch.explicitMassConstant 1 1 + 1) *
    Real.exp (1 + 24 * Real.log 2) *
    TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
    (Real.log 2) ^ (1 / 4 : ℝ)

/-- A single explicit uniform constant valid in all three regimes. -/
noncomputable def sharpWeightedThreeRegimeConstant : ℝ :=
  1 + sharpWeightedMiddleConstant + sharpWeightedLargeConstant +
    sharpWeightedLargeOneConstant

lemma sharpWeightedMiddleConstant_nonneg :
    0 ≤ sharpWeightedMiddleConstant := by
  have hm := HalberstamScratch.explicitMassConstant_nonneg
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
  unfold sharpWeightedMiddleConstant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by linarith) (Real.exp_pos _).le)
      (Real.rpow_nonneg TauInvTypeMean448.cleanMertensConstant_pos.le _))
    (Real.rpow_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le _)

lemma sharpWeightedLargeConstant_nonneg :
    0 ≤ sharpWeightedLargeConstant := by
  have hm := HalberstamScratch.explicitMassConstant_nonneg
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
  unfold sharpWeightedLargeConstant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by linarith) (Real.exp_pos _).le)
      (Real.rpow_nonneg TauInvTypeMean448.cleanMertensConstant_pos.le _))
    (Real.rpow_nonneg cleanMertensLowerConstant_pos.le _)

lemma sharpWeightedLargeOneConstant_nonneg :
    0 ≤ sharpWeightedLargeOneConstant := by
  have hm := HalberstamScratch.explicitMassConstant_nonneg
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
  unfold sharpWeightedLargeOneConstant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by linarith) (Real.exp_pos _).le)
      (Real.rpow_nonneg TauInvTypeMean448.cleanMertensConstant_pos.le _))
    (Real.rpow_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le _)

lemma sharpWeightedThreeRegimeConstant_nonneg :
    0 ≤ sharpWeightedThreeRegimeConstant := by
  unfold sharpWeightedThreeRegimeConstant
  linarith [sharpWeightedMiddleConstant_nonneg,
    sharpWeightedLargeConstant_nonneg,
    sharpWeightedLargeOneConstant_nonneg]

theorem sharpWeightedTSum_middle_le
    {q : ℕ} (hq : q ≠ 0) (k z : ℕ)
    (hz : 2 ≤ z) (hzk : z < 2 ^ k) :
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 z ≤
      sharpWeightedMiddleConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(3 : ℝ) / 4) := by
  have hmono := weightedTSum_le_succ sharpShiftedReciprocalWeightAF
    sharpShiftedReciprocalWeightAF_nonneg q k 2 z
  have hHR := sharpWeightedTSum_succ_le_HR hq k z hz
  have heuler := sharp_diagonalEuler_product_middle_le z k hz hzk
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hw2 : 0 ≤ hybridCorrectionWeight sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) q :=
    hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) q
  have hM : 0 ≤ HalberstamScratch.explicitMassConstant 1 1 + 1 := by
    have hm := HalberstamScratch.explicitMassConstant_nonneg
      (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
    linarith
  have hscale : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (z : ℝ) / Real.log (z : ℝ) :=
    div_nonneg (mul_nonneg hM (Nat.cast_nonneg z)) hlogz.le
  have hraw := hmono.trans (hHR.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right heuler hw2) hscale))
  have hX : 0 < TauInvTypeMean448.cleanMertensConstant *
      Real.log (z : ℝ) :=
    mul_pos TauInvTypeMean448.cleanMertensConstant_pos hlogz
  have hexp :
      Real.exp ((1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ)) +
        1 + 24 * Real.log 2) =
      Real.exp (1 + 24 * Real.log 2) *
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
        (Real.log (z : ℝ)) ^ (1 / 4 : ℝ) := by
    have hqexp :
        Real.exp ((1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ))) =
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
          (Real.log (z : ℝ)) ^ (1 / 4 : ℝ) := by
      rw [← Real.mul_rpow TauInvTypeMean448.cleanMertensConstant_pos.le hlogz.le,
        Real.rpow_def_of_pos hX]
      congr 1
      ring
    rw [show (1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ)) +
          1 + 24 * Real.log 2 =
        (1 / 4 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ)) +
          (1 + 24 * Real.log 2) by ring,
      Real.exp_add, hqexp]
    ring
  rw [hexp] at hraw
  have hzCancel : (Real.log (z : ℝ))⁻¹ *
      (Real.log (z : ℝ)) ^ (1 / 4 : ℝ) =
        (Real.log (z : ℝ)) ^ (-(3 : ℝ) / 4) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hlogz]
    congr 1
    ring
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htwoCancel :
      (Real.log 2) ^ (1 / 4 : ℝ) *
        (Real.log 2) ^ (-(1 : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add hlog2]
    norm_num
  calc
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 z ≤
        (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (z : ℝ) / Real.log (z : ℝ) *
          ((Real.exp (1 + 24 * Real.log 2) *
              TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
              (Real.log (z : ℝ)) ^ (1 / 4 : ℝ)) *
            hybridCorrectionWeight sharpShiftedReciprocalWeightAF
              (omegaWeightAF k) q) := hraw
    _ = (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          Real.exp (1 + 24 * Real.log 2) *
          TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
          (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log (z : ℝ)) ^ (-(3 : ℝ) / 4) := by
      rw [div_eq_mul_inv]
      calc
        _ = (HalberstamScratch.explicitMassConstant 1 1 + 1) *
              Real.exp (1 + 24 * Real.log 2) *
              TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
              (z : ℝ) *
              hybridCorrectionWeight sharpShiftedReciprocalWeightAF
                (omegaWeightAF k) q *
              ((Real.log (z : ℝ))⁻¹ *
                (Real.log (z : ℝ)) ^ (1 / 4 : ℝ)) := by ring
        _ = _ := by rw [hzCancel]
    _ = sharpWeightedMiddleConstant * (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(3 : ℝ) / 4) := by
      unfold sharpWeightedMiddleConstant
      calc
        _ = (HalberstamScratch.explicitMassConstant 1 1 + 1) *
              Real.exp (1 + 24 * Real.log 2) *
              TauInvTypeMean448.cleanMertensConstant ^ (1 / 4 : ℝ) *
              (z : ℝ) *
              hybridCorrectionWeight sharpShiftedReciprocalWeightAF
                (omegaWeightAF k) q *
              ((Real.log 2) ^ (1 / 4 : ℝ) *
                (Real.log 2) ^ (-(1 : ℝ) / 4)) *
              (Real.log z) ^ (-(3 : ℝ) / 4) := by rw [htwoCancel]; ring
        _ = _ := by ring

theorem sharpWeightedTSum_large_of_two_le_k
    {q : ℕ} (hq : q ≠ 0) (k z : ℕ)
    (hk : 2 ≤ k) (hkz : 2 ^ k ≤ z) :
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 z ≤
      sharpWeightedLargeConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(1 : ℝ) / 2) := by
  have hz : 2 ≤ z := by
    have htwo : 2 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
      omega
    exact htwo.trans hkz
  have hmono := weightedTSum_le_succ sharpShiftedReciprocalWeightAF
    sharpShiftedReciprocalWeightAF_nonneg q k 2 z
  have hHR := sharpWeightedTSum_succ_le_HR hq k z hz
  have heuler := sharp_diagonalEuler_product_large_le z k hz hk hkz
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogY : 0 < Real.log ((2 ^ k : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 2 ^ k by
      have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (show 1 ≤ k by omega)
      omega)
  have hw2 : 0 ≤ hybridCorrectionWeight sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) q :=
    hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) q
  have hM : 0 ≤ HalberstamScratch.explicitMassConstant 1 1 + 1 := by
    have hm := HalberstamScratch.explicitMassConstant_nonneg
      (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
    linarith
  have hscale : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (z : ℝ) / Real.log (z : ℝ) :=
    div_nonneg (mul_nonneg hM (Nat.cast_nonneg z)) hlogz.le
  have hraw := hmono.trans (hHR.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right heuler hw2) hscale))
  have hX : 0 < TauInvTypeMean448.cleanMertensConstant *
      Real.log (z : ℝ) :=
    mul_pos TauInvTypeMean448.cleanMertensConstant_pos hlogz
  have hY : 0 < cleanMertensLowerConstant *
      Real.log ((2 ^ k : ℕ) : ℝ) :=
    mul_pos cleanMertensLowerConstant_pos hlogY
  have hxpow :
      Real.exp ((1 / 2 : ℝ) * Real.log
        (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ))) =
      TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
        (Real.log (z : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow TauInvTypeMean448.cleanMertensConstant_pos.le hlogz.le,
      Real.rpow_def_of_pos hX]
    congr 1
    ring
  have hypow :
      Real.exp (-(1 / 4 : ℝ) * Real.log
        (cleanMertensLowerConstant * Real.log ((2 ^ k : ℕ) : ℝ))) =
      cleanMertensLowerConstant ^ (-(1 : ℝ) / 4) *
        (Real.log ((2 ^ k : ℕ) : ℝ)) ^ (-(1 : ℝ) / 4) := by
    rw [← Real.mul_rpow cleanMertensLowerConstant_pos.le hlogY.le,
      Real.rpow_def_of_pos hY]
    congr 1
    ring
  have hexp :
      Real.exp ((1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ)) -
        (1 / 4 : ℝ) * Real.log
          (cleanMertensLowerConstant * Real.log ((2 ^ k : ℕ) : ℝ)) +
        (5 / 4 : ℝ) + 24 * Real.log 2) =
      Real.exp ((5 / 4 : ℝ) + 24 * Real.log 2) *
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
        (Real.log (z : ℝ)) ^ (1 / 2 : ℝ) *
        cleanMertensLowerConstant ^ (-(1 : ℝ) / 4) *
        (Real.log ((2 ^ k : ℕ) : ℝ)) ^ (-(1 : ℝ) / 4) := by
    rw [show (1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ)) -
        (1 / 4 : ℝ) * Real.log
          (cleanMertensLowerConstant * Real.log ((2 ^ k : ℕ) : ℝ)) +
        (5 / 4 : ℝ) + 24 * Real.log 2 =
      (1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ)) +
      (-(1 / 4 : ℝ) * Real.log
          (cleanMertensLowerConstant * Real.log ((2 ^ k : ℕ) : ℝ))) +
      ((5 / 4 : ℝ) + 24 * Real.log 2) by ring,
      Real.exp_add, Real.exp_add, hxpow, hypow]
    ring
  rw [hexp] at hraw
  have hlogPow :
      Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
    rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num,
      Real.log_pow]
  have hcutoffPow :
      (Real.log ((2 ^ k : ℕ) : ℝ)) ^ (-(1 : ℝ) / 4) =
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
          (Real.log 2) ^ (-(1 : ℝ) / 4) := by
    rw [hlogPow, Real.mul_rpow hkR.le hlog2.le]
  rw [hcutoffPow] at hraw
  have hzCancel : (Real.log (z : ℝ))⁻¹ *
      (Real.log (z : ℝ)) ^ (1 / 2 : ℝ) =
        (Real.log (z : ℝ)) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hlogz]
    congr 1
    ring
  calc
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 z ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (z : ℝ) / Real.log (z : ℝ) *
        ((Real.exp ((5 / 4 : ℝ) + 24 * Real.log 2) *
            TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
            (Real.log (z : ℝ)) ^ (1 / 2 : ℝ) *
            cleanMertensLowerConstant ^ (-(1 : ℝ) / 4) *
            ((k : ℝ) ^ (-(1 : ℝ) / 4) *
              (Real.log 2) ^ (-(1 : ℝ) / 4))) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q) := hraw
    _ = sharpWeightedLargeConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(1 : ℝ) / 2) := by
      rw [div_eq_mul_inv]
      unfold sharpWeightedLargeConstant
      calc
        _ = (HalberstamScratch.explicitMassConstant 1 1 + 1) *
            Real.exp ((5 / 4 : ℝ) + 24 * Real.log 2) *
            TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
            cleanMertensLowerConstant ^ (-(1 : ℝ) / 4) *
            (z : ℝ) *
            hybridCorrectionWeight sharpShiftedReciprocalWeightAF
              (omegaWeightAF k) q *
            (Real.log 2) ^ (-(1 : ℝ) / 4) *
            (k : ℝ) ^ (-(1 : ℝ) / 4) *
            ((Real.log (z : ℝ))⁻¹ *
              (Real.log (z : ℝ)) ^ (1 / 2 : ℝ)) := by ring
        _ = _ := by rw [hzCancel]

theorem sharpWeightedTSum_large_one
    {q : ℕ} (hq : q ≠ 0) (z : ℕ) (hz : 2 ≤ z) :
    weightedTSum sharpShiftedReciprocalWeightAF q 1 2 z ≤
      sharpWeightedLargeOneConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF 1) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (1 : ℝ) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(1 : ℝ) / 2) := by
  have hmono := weightedTSum_le_succ sharpShiftedReciprocalWeightAF
    sharpShiftedReciprocalWeightAF_nonneg q 1 2 z
  have hHR := sharpWeightedTSum_succ_le_HR hq 1 z hz
  have heuler := sharp_diagonalEuler_product_crude_le z 1 hz
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hw2 : 0 ≤ hybridCorrectionWeight sharpShiftedReciprocalWeightAF
      (omegaWeightAF 1) q :=
    hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF 1) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one 1) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg 1) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp j => omegaWeightAF_le_one 1 (p ^ j)) q
  have hM : 0 ≤ HalberstamScratch.explicitMassConstant 1 1 + 1 := by
    have hm := HalberstamScratch.explicitMassConstant_nonneg
      (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
    linarith
  have hscale : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (z : ℝ) / Real.log (z : ℝ) :=
    div_nonneg (mul_nonneg hM (Nat.cast_nonneg z)) hlogz.le
  have hraw := hmono.trans (hHR.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right heuler hw2) hscale))
  have hX : 0 < TauInvTypeMean448.cleanMertensConstant *
      Real.log (z : ℝ) :=
    mul_pos TauInvTypeMean448.cleanMertensConstant_pos hlogz
  have hexp :
      Real.exp ((1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ)) +
        1 + 24 * Real.log 2) =
      Real.exp (1 + 24 * Real.log 2) *
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
        (Real.log (z : ℝ)) ^ (1 / 2 : ℝ) := by
    have hhexp :
        Real.exp ((1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ))) =
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
          (Real.log (z : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [← Real.mul_rpow TauInvTypeMean448.cleanMertensConstant_pos.le hlogz.le,
        Real.rpow_def_of_pos hX]
      congr 1
      ring
    rw [show (1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ)) +
          1 + 24 * Real.log 2 =
        (1 / 2 : ℝ) * Real.log
          (TauInvTypeMean448.cleanMertensConstant * Real.log (z : ℝ)) +
          (1 + 24 * Real.log 2) by ring,
      Real.exp_add, hhexp]
    ring
  rw [hexp] at hraw
  have hzCancel : (Real.log (z : ℝ))⁻¹ *
      (Real.log (z : ℝ)) ^ (1 / 2 : ℝ) =
        (Real.log (z : ℝ)) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hlogz]
    congr 1
    ring
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htwoCancel :
      (Real.log 2) ^ (1 / 4 : ℝ) *
        (Real.log 2) ^ (-(1 : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add hlog2]
    norm_num
  calc
    weightedTSum sharpShiftedReciprocalWeightAF q 1 2 z ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (z : ℝ) / Real.log (z : ℝ) *
        ((Real.exp (1 + 24 * Real.log 2) *
            TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
            (Real.log (z : ℝ)) ^ (1 / 2 : ℝ)) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF 1) q) := hraw
    _ = (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        Real.exp (1 + 24 * Real.log 2) *
        TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
        (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF 1) q *
        (Real.log (z : ℝ)) ^ (-(1 : ℝ) / 2) := by
      rw [div_eq_mul_inv]
      calc
        _ = (HalberstamScratch.explicitMassConstant 1 1 + 1) *
            Real.exp (1 + 24 * Real.log 2) *
            TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
            (z : ℝ) *
            hybridCorrectionWeight sharpShiftedReciprocalWeightAF
              (omegaWeightAF 1) q *
            ((Real.log (z : ℝ))⁻¹ *
              (Real.log (z : ℝ)) ^ (1 / 2 : ℝ)) := by ring
        _ = _ := by rw [hzCancel]
    _ = sharpWeightedLargeOneConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF 1) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (1 : ℝ) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(1 : ℝ) / 2) := by
      unfold sharpWeightedLargeOneConstant
      rw [Real.one_rpow]
      calc
        _ = (HalberstamScratch.explicitMassConstant 1 1 + 1) *
            Real.exp (1 + 24 * Real.log 2) *
            TauInvTypeMean448.cleanMertensConstant ^ (1 / 2 : ℝ) *
            (z : ℝ) *
            hybridCorrectionWeight sharpShiftedReciprocalWeightAF
              (omegaWeightAF 1) q *
            ((Real.log 2) ^ (1 / 4 : ℝ) *
              (Real.log 2) ^ (-(1 : ℝ) / 4)) *
            (Real.log z) ^ (-(1 : ℝ) / 2) := by rw [htwoCancel]; ring
        _ = _ := by ring

theorem sharpWeightedTSum_large_le
    {q : ℕ} (hq : q ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (z : ℕ) (hkz : 2 ^ k ≤ z) :
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 z ≤
      (max sharpWeightedLargeConstant sharpWeightedLargeOneConstant) *
        (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(1 : ℝ) / 2) := by
  by_cases hk1 : k = 1
  · subst k
    have h := sharpWeightedTSum_large_one hq z (by simpa using hkz)
    have hfac : 0 ≤ (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF 1) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (1 : ℝ) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(1 : ℝ) / 2) := by
      have hw2 := hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
        (omegaWeightAF 1) sharpShiftedReciprocalWeightAF_one
        (omegaWeightAF_one 1) sharpShiftedReciprocalWeightAF_nonneg
        (omegaWeightAF_nonneg 1) sharpShiftedReciprocalWeightAF_logType
        (fun {p} hp j => omegaWeightAF_le_one 1 (p ^ j)) q
      positivity
    calc
      weightedTSum sharpShiftedReciprocalWeightAF q 1 2 z ≤ _ := h
      _ = sharpWeightedLargeOneConstant *
          ((z : ℝ) * hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF 1) q *
          (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (1 : ℝ) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(1 : ℝ) / 2)) := by ring
      _ ≤ max sharpWeightedLargeConstant sharpWeightedLargeOneConstant *
          ((z : ℝ) * hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF 1) q *
          (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (1 : ℝ) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hfac
      _ = _ := by ring
  · have hk2 : 2 ≤ k := by omega
    have h := sharpWeightedTSum_large_of_two_le_k hq k z hk2 hkz
    have hw2 := hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) q
    have hfac : 0 ≤ (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(1 : ℝ) / 2) := by positivity
    calc
      weightedTSum sharpShiftedReciprocalWeightAF q k 2 z ≤ _ := h
      _ = sharpWeightedLargeConstant *
          ((z : ℝ) * hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(1 : ℝ) / 2)) := by ring
      _ ≤ max sharpWeightedLargeConstant sharpWeightedLargeOneConstant *
          ((z : ℝ) * hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hfac
      _ = _ := by ring

/-- The unconditional, arbitrary-residual second mean estimate at
`y=1/2`, `theta=sigma=2`.  Both weights are concrete: the first is the
sharp shifted reciprocal-divisor correction, and the second is its genuine
hybrid Euler correction produced by HR Lemma 2. -/
theorem sharpWeightedTSum_half_le
    {q : ℕ} (hq : q ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    ∀ z, weightedTSum sharpShiftedReciprocalWeightAF q k 2 z ≤
      if 2 ^ k ≤ z then
        sharpWeightedThreeRegimeConstant * (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(1 : ℝ) / 2)
      else if 2 ≤ z then
        sharpWeightedThreeRegimeConstant * (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(3 : ℝ) / 4)
      else
        sharpWeightedThreeRegimeConstant *
          sharpShiftedReciprocalWeightAF q := by
  intro z
  split_ifs with hkz hz
  ·
    have h := sharpWeightedTSum_large_le hq k hk z hkz
    have hw2 := hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) q
    have hz2 : 2 ≤ z := by
      have hpow : 2 ≤ 2 ^ k := by
        have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
        omega
      exact hpow.trans hkz
    have hlogz : 0 < Real.log (z : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < z by omega))
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hfac : 0 ≤ (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(1 : ℝ) / 2) := by positivity
    have hmax :
        max sharpWeightedLargeConstant sharpWeightedLargeOneConstant ≤
          sharpWeightedThreeRegimeConstant := by
      apply max_le
      · unfold sharpWeightedThreeRegimeConstant
        linarith [sharpWeightedMiddleConstant_nonneg,
          sharpWeightedLargeOneConstant_nonneg]
      · unfold sharpWeightedThreeRegimeConstant
        linarith [sharpWeightedMiddleConstant_nonneg,
          sharpWeightedLargeConstant_nonneg]
    calc
      weightedTSum sharpShiftedReciprocalWeightAF q k 2 z ≤
        max sharpWeightedLargeConstant sharpWeightedLargeOneConstant *
          ((z : ℝ) *
            hybridCorrectionWeight sharpShiftedReciprocalWeightAF
              (omegaWeightAF k) q *
            (Real.log 2) ^ (-(1 : ℝ) / 4) *
            (k : ℝ) ^ (-(1 : ℝ) / 4) *
            (Real.log z) ^ (-(1 : ℝ) / 2)) := by
          simpa only [mul_assoc] using h
      _ ≤ sharpWeightedThreeRegimeConstant *
          ((z : ℝ) *
            hybridCorrectionWeight sharpShiftedReciprocalWeightAF
              (omegaWeightAF k) q *
            (Real.log 2) ^ (-(1 : ℝ) / 4) *
            (k : ℝ) ^ (-(1 : ℝ) / 4) *
            (Real.log z) ^ (-(1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hmax hfac
      _ = _ := by ring
  · have hzk : z < 2 ^ k := Nat.lt_of_not_ge hkz
    have h := sharpWeightedTSum_middle_le hq k z hz hzk
    have hw2 := hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) q
    have hlogz : 0 < Real.log (z : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < z by omega))
    have hfac : 0 ≤ (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (Real.log z) ^ (-(3 : ℝ) / 4) := by positivity
    have hmid : sharpWeightedMiddleConstant ≤
        sharpWeightedThreeRegimeConstant := by
      unfold sharpWeightedThreeRegimeConstant
      linarith [sharpWeightedLargeConstant_nonneg,
        sharpWeightedLargeOneConstant_nonneg]
    calc
      weightedTSum sharpShiftedReciprocalWeightAF q k 2 z ≤
        sharpWeightedMiddleConstant *
          ((z : ℝ) *
            hybridCorrectionWeight sharpShiftedReciprocalWeightAF
              (omegaWeightAF k) q *
            (Real.log 2) ^ (-(1 : ℝ) / 4) *
            (Real.log z) ^ (-(3 : ℝ) / 4)) := by
          simpa only [mul_assoc] using h
      _ ≤ sharpWeightedThreeRegimeConstant *
          ((z : ℝ) *
            hybridCorrectionWeight sharpShiftedReciprocalWeightAF
              (omegaWeightAF k) q *
            (Real.log 2) ^ (-(1 : ℝ) / 4) *
            (Real.log z) ^ (-(3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hmid hfac
      _ = _ := by ring
  · have hz' : z < 2 := Nat.lt_of_not_ge hz
    have hright : 0 ≤ sharpWeightedThreeRegimeConstant *
        sharpShiftedReciprocalWeightAF q :=
      mul_nonneg sharpWeightedThreeRegimeConstant_nonneg
        (sharpShiftedReciprocalWeightAF_nonneg q)
    have hzCases : z = 0 ∨ z = 1 := by omega
    rcases hzCases with rfl | rfl <;>
      simpa [weightedTSum] using hright
/-- The three mutually exclusive regimes in the second mean estimate. -/
inductive SizeRegime (sigma thetaPow z : ℕ)
  | large (h : thetaPow ≤ z)
  | middle (h₁ : sigma ≤ z) (h₂ : z < thetaPow)
  | small (h : z < sigma)

lemma sizeRegime_exists {sigma thetaPow z : ℕ}
    (horder : sigma ≤ thetaPow) : Nonempty (SizeRegime sigma thetaPow z) := by
  by_cases hlarge : thetaPow ≤ z
  · exact ⟨SizeRegime.large hlarge⟩
  · have hztheta : z < thetaPow := Nat.lt_of_not_ge hlarge
    by_cases hmiddle : sigma ≤ z
    · exact ⟨SizeRegime.middle hmiddle hztheta⟩
    · exact ⟨SizeRegime.small (Nat.lt_of_not_ge hmiddle)⟩

/-- An exact indicator partition: precisely one copy of `a` survives. -/
lemma exact_three_regime_partition
    {sigma thetaPow z : ℕ} (horder : sigma ≤ thetaPow) (a : ℝ) :
    a =
      (if thetaPow ≤ z then a else 0) +
      (if sigma ≤ z ∧ z < thetaPow then a else 0) +
      (if z < sigma then a else 0) := by
  by_cases hlarge : thetaPow ≤ z
  · have hnotMid : ¬ (sigma ≤ z ∧ z < thetaPow) := fun h => (not_lt_of_ge hlarge) h.2
    have hnotSmall : ¬ z < sigma := not_lt_of_ge (horder.trans hlarge)
    simp [hlarge, hnotMid, hnotSmall]
  · have hztheta : z < thetaPow := Nat.lt_of_not_ge hlarge
    by_cases hmiddle : sigma ≤ z
    · have hnotSmall : ¬ z < sigma := not_lt_of_ge hmiddle
      simp [hlarge, hmiddle, hztheta, hnotSmall]
    · have hzsigma : z < sigma := Nat.lt_of_not_ge hmiddle
      have hnotMid : ¬ (sigma ≤ z ∧ z < thetaPow) := fun h => hmiddle h.1
      simp [hlarge, hmiddle, hnotMid, hzsigma]

/-- Exact partition specialized to the weighted `t`-sum. -/
lemma weightedTSum_three_regime_partition
    (w₁ : ℕ → ℝ) (q k sigma thetaPow z : ℕ)
    (horder : sigma ≤ thetaPow) :
    weightedTSum w₁ q k sigma z =
      (if thetaPow ≤ z then weightedTSum w₁ q k sigma z else 0) +
      (if sigma ≤ z ∧ z < thetaPow then weightedTSum w₁ q k sigma z else 0) +
      (if z < sigma then weightedTSum w₁ q k sigma z else 0) := by
  exact exact_three_regime_partition horder _

/-- The piecewise right-hand side, kept abstract from the analytic formulas. -/
def piecewiseBound
    (largeBound middleBound smallBound : ℕ → ℝ)
    (sigma thetaPow z : ℕ) : ℝ :=
  if thetaPow ≤ z then largeBound z
  else if sigma ≤ z then middleBound z
  else smallBound z

/-- Lossless consumer theorem for the three analytic estimates. -/
theorem weightedTSum_le_piecewiseBound
    (w₁ : ℕ → ℝ) (q k sigma thetaPow : ℕ)
    (largeBound middleBound smallBound : ℕ → ℝ)
    (hlarge : ∀ z, thetaPow ≤ z →
      weightedTSum w₁ q k sigma z ≤ largeBound z)
    (hmiddle : ∀ z, sigma ≤ z → z < thetaPow →
      weightedTSum w₁ q k sigma z ≤ middleBound z)
    (hsmall : ∀ z, z < sigma →
      weightedTSum w₁ q k sigma z ≤ smallBound z) :
    ∀ z, weightedTSum w₁ q k sigma z ≤
      piecewiseBound largeBound middleBound smallBound sigma thetaPow z := by
  intro z
  unfold piecewiseBound
  split_ifs with htheta hsigma
  · exact hlarge z htheta
  · exact hmiddle z hsigma (Nat.lt_of_not_ge htheta)
  · exact hsmall z (Nat.lt_of_not_ge hsigma)

/-- Specialization of the preceding wrapper to the exponents in
Proposition 3 at `y = 1/2`, `theta = sigma = 2`.

The constant and the `w₂(q)` correction are supplied by the second
application of ET Lemma 2.  Keeping the real logarithmic formula here avoids
rounding changes when this lemma is used by the Proposition 3 assembly.
-/
theorem weightedTSum_half_le
    (w₁ w₂ : ℕ → ℝ) (C : ℝ) (q k : ℕ)
    (hlarge : ∀ z, 2 ^ k ≤ z →
      weightedTSum w₁ q k 2 z ≤
        C * (z : ℝ) * w₂ q * (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(1 : ℝ) / 2))
    (hmiddle : ∀ z, 2 ≤ z → z < 2 ^ k →
      weightedTSum w₁ q k 2 z ≤
        C * (z : ℝ) * w₂ q * (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(3 : ℝ) / 4))
    (hsmall : ∀ z, z < 2 →
      weightedTSum w₁ q k 2 z ≤ C * w₁ q) :
    ∀ z, weightedTSum w₁ q k 2 z ≤
      if 2 ^ k ≤ z then
        C * (z : ℝ) * w₂ q * (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(1 : ℝ) / 2)
      else if 2 ≤ z then
        C * (z : ℝ) * w₂ q * (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (Real.log z) ^ (-(3 : ℝ) / 4)
      else C * w₁ q := by
  intro z
  split_ifs with htheta hsigma
  · exact hlarge z htheta
  · exact hmiddle z hsigma (Nat.lt_of_not_ge htheta)
  · exact hsmall z (Nat.lt_of_not_ge hsigma)

end Prop3WeightedT448

#print axioms Prop3WeightedT448.weightedTSum_half_le
#print axioms Prop3WeightedT448.weightedTSum_dyadic_le
#print axioms Prop3WeightedT448.sharpWeightedTSum_dyadic_le
#print axioms Prop3WeightedT448.sharpHybridCorrection_meanType
#print axioms Prop3WeightedT448.sharpWeightedTSum_half_le
