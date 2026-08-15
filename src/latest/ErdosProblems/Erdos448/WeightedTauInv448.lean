import ErdosProblems.Erdos448.TauInvTypeMean448

/-!
An explicit mixed quarter/half Euler-product estimate.  The cutoff weight
`2 ^ (-Omega(n, 2^k))` changes the coefficient of `1/p` from `1/2` to
`1/4` below `2^k`.  Since the summation frontier is only `4 * 2^k`, the
remaining quarter-prime mass is bounded elementarily.
-/

open scoped BigOperators
open Finset

namespace WeightedTauInv448

open TauInvTypeMean448

/-- Prime factors below `u`, counted with multiplicity. -/
def omegaBelow (n u : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p => p < u).length

lemma omegaBelow_mul {a b u : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    omegaBelow (a * b) u = omegaBelow a u + omegaBelow b u := by
  unfold omegaBelow
  have hp := (Nat.perm_primeFactorsList_mul ha hb).filter (fun p => p < u)
  simpa using hp.length_eq

lemma omegaBelow_prime_pow {p j u : ℕ} (hp : p.Prime) :
    omegaBelow (p ^ j) u = if p < u then j else 0 := by
  rw [omegaBelow, hp.primeFactorsList_pow]
  by_cases hpu : p < u <;> simp [hpu]

/-- `2 ^ (-Omega(n,2^k))`. -/
noncomputable def omegaWeight (k n : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(omegaBelow n (2 ^ k) : ℤ))

lemma omegaWeight_nonneg (k n : ℕ) : 0 ≤ omegaWeight k n := by
  exact (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le

lemma omegaWeight_mul {a b k : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    omegaWeight k (a * b) = omegaWeight k a * omegaWeight k b := by
  rw [omegaWeight, omegaWeight, omegaWeight, omegaBelow_mul ha hb]
  push_cast
  rw [neg_add_rev, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  exact mul_comm _ _

noncomputable def omegaWeightAF (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else omegaWeight k n, by simp⟩

@[simp] lemma omegaWeightAF_one (k : ℕ) : omegaWeightAF k 1 = 1 := by
  simp [omegaWeightAF, omegaWeight, omegaBelow]

lemma omegaWeightAF_nonneg (k n : ℕ) : 0 ≤ omegaWeightAF k n := by
  simp only [omegaWeightAF, ArithmeticFunction.coe_mk]
  split_ifs
  · exact le_rfl
  · exact omegaWeight_nonneg k n

lemma omegaWeightAF_multiplicative (k : ℕ) :
    ArithmeticFunction.IsMultiplicative (omegaWeightAF k) := by
  refine ⟨by simp [omegaWeightAF, omegaWeight, omegaBelow], ?_⟩
  intro a b hab
  by_cases ha : a = 0
  · subst a
    have hb : b = 1 := by simpa using hab
    subst b
    simp [omegaWeightAF]
  by_cases hb : b = 0
  · subst b
    have ha1 : a = 1 := by simpa [Nat.coprime_comm] using hab
    subst a
    simp [omegaWeightAF]
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
      (one_le_zpow₀ (by norm_num) (Int.natCast_nonneg _))

/-- Product of a logarithmic-error divisor-reciprocal weight with the
truncated Rankin weight. -/
noncomputable def weightedFunction (w : ℕ → ℝ) (k n : ℕ) : ℝ :=
  w n * omegaWeightAF k n

@[simp] lemma weightedFunction_zero
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C) (k : ℕ) :
    weightedFunction w k 0 = 0 := by
  simp [weightedFunction, hw.map_zero]

@[simp] lemma weightedFunction_one
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C) (k : ℕ) :
    weightedFunction w k 1 = 1 := by
  simp [weightedFunction, hw.map_one]

lemma weightedFunction_nonneg
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C) (k n : ℕ) :
    0 ≤ weightedFunction w k n :=
  mul_nonneg (hw.nonneg n) (omegaWeightAF_nonneg k n)

lemma weightedFunction_mul_of_coprime
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C) (k : ℕ)
    {m n : ℕ} (hmn : m.Coprime n) :
    weightedFunction w k (m * n) =
      weightedFunction w k m * weightedFunction w k n := by
  simp only [weightedFunction]
  rw [hw.map_mul_of_coprime hmn,
    (omegaWeightAF_multiplicative k).map_mul_of_coprime hmn]
  ring

lemma weightedFunction_prime_pow_le_one_add_C
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C) (k : ℕ)
    {p j : ℕ} (hp : p.Prime) :
    weightedFunction w k (p ^ (j + 1)) ≤ 1 + C := by
  have hv0 : 0 ≤ omegaWeightAF k (p ^ (j + 1)) :=
    omegaWeightAF_nonneg k _
  have hv1 : omegaWeightAF k (p ^ (j + 1)) ≤ 1 :=
    omegaWeightAF_le_one k _
  have hw0 : 0 ≤ w (p ^ (j + 1)) := hw.nonneg _
  calc
    weightedFunction w k (p ^ (j + 1)) =
        w (p ^ (j + 1)) * omegaWeightAF k (p ^ (j + 1)) := rfl
    _ ≤ w (p ^ (j + 1)) * 1 :=
      mul_le_mul_of_nonneg_left hv1 hw0
    _ ≤ 1 + C := by
      simpa using hw.prime_pow_le_one_add_C hp (by omega : 1 ≤ j + 1)

/-- A local majorant retaining the quarter coefficient below the cutoff. -/
noncomputable def mixedLocalMajorant (C : ℝ) (k p j : ℕ) : ℝ :=
  if j = 0 then 1
  else if p < 2 ^ k then
    (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) *
      (((2 : ℝ) * p)⁻¹) ^ j
  else
    (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) *
      ((p : ℝ)⁻¹) ^ j

lemma mixedLocalMajorant_nonneg {C : ℝ} (hC : 0 ≤ C)
    {p : ℕ} (hp : p.Prime) (k j : ℕ) :
    0 ≤ mixedLocalMajorant C k p j := by
  unfold mixedLocalMajorant
  split_ifs
  · norm_num
  · have : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_le)
    positivity
  · have : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_le)
    positivity

lemma weighted_local_term_le_majorant
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    (k : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    weightedFunction w k (p ^ j) / (((p ^ j : ℕ) : ℝ)) ≤
      mixedLocalMajorant C k p j := by
  by_cases hj : j = 0
  · subst j
    simp [mixedLocalMajorant, weightedFunction, hw.map_one]
  · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    have hpj0 : 0 < (((p ^ j : ℕ) : ℝ)) := by
      exact_mod_cast (Nat.pow_pos hp.pos : 0 < p ^ j)
    have hwupper := hw.prime_pow_upper hp hj1
    have hhalf : 1 / (((j + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast (show 2 ≤ j + 1 by omega))
    have hwupper' : w (p ^ j) ≤
        1 / 2 + C * Real.log (p : ℝ) / (p : ℝ) := by linarith
    by_cases hsmall : p < 2 ^ k
    · have hv : omegaWeightAF k (p ^ j) = ((2 : ℝ)⁻¹) ^ j := by
        rw [omegaWeightAF_prime_pow hp, if_pos hsmall, zpow_neg,
          zpow_natCast, inv_pow]
      rw [weightedFunction, mixedLocalMajorant, if_neg hj, if_pos hsmall, hv]
      calc
        w (p ^ j) * ((2 : ℝ)⁻¹) ^ j / (((p ^ j : ℕ) : ℝ)) ≤
            (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) *
              ((2 : ℝ)⁻¹) ^ j / (((p ^ j : ℕ) : ℝ)) := by
          gcongr
        _ = (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) *
              (((2 : ℝ) * p)⁻¹) ^ j := by
          push_cast
          rw [mul_inv, mul_pow]
          simp only [inv_pow]
          ring
    · have hv : omegaWeightAF k (p ^ j) = 1 := by
        rw [omegaWeightAF_prime_pow hp, if_neg hsmall]
      rw [weightedFunction, mixedLocalMajorant, if_neg hj, if_neg hsmall, hv,
        mul_one]
      calc
        w (p ^ j) / (((p ^ j : ℕ) : ℝ)) ≤
            (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
              (((p ^ j : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right hwupper' hpj0.le
        _ = (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) *
              ((p : ℝ)⁻¹) ^ j := by
          push_cast
          simp only [div_eq_mul_inv, inv_pow]

lemma mixedLocalMajorant_summable {C : ℝ} (hC : 0 ≤ C)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Summable (mixedLocalMajorant C k p) := by
  by_cases hsmall : p < 2 ^ k
  · let A : ℝ := 1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)
    let r : ℝ := ((2 : ℝ) * p)⁻¹
    have hr : ‖r‖ < 1 := by
      rw [Real.norm_of_nonneg (by dsimp [r]; positivity)]
      dsimp [r]
      apply inv_lt_one_of_one_lt₀
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      nlinarith
    have hg : Summable (fun j : ℕ => A * r ^ j) :=
      (summable_geometric_of_norm_lt_one hr).mul_left A
    have hs : Summable (fun j : ℕ => if j = 0 then 1 - A else 0) :=
      (hasSum_ite_eq 0 (1 - A)).summable
    have heq : mixedLocalMajorant C k p = fun j : ℕ =>
        A * r ^ j + if j = 0 then 1 - A else 0 := by
      funext j
      by_cases hj : j = 0
      · subst j
        simp [mixedLocalMajorant, A, r]
      · simp [mixedLocalMajorant, A, r, hj, hsmall]
    rw [heq]
    exact hg.add hs
  · let A : ℝ := 1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)
    let r : ℝ := (p : ℝ)⁻¹
    have hr : ‖r‖ < 1 := by
      rw [Real.norm_of_nonneg (by dsimp [r]; positivity)]
      dsimp [r]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    have hg : Summable (fun j : ℕ => A * r ^ j) :=
      (summable_geometric_of_norm_lt_one hr).mul_left A
    have hs : Summable (fun j : ℕ => if j = 0 then 1 - A else 0) :=
      (hasSum_ite_eq 0 (1 - A)).summable
    have heq : mixedLocalMajorant C k p = fun j : ℕ =>
        A * r ^ j + if j = 0 then 1 - A else 0 := by
      funext j
      by_cases hj : j = 0
      · subst j
        simp [mixedLocalMajorant, A, r]
      · simp [mixedLocalMajorant, A, r, hj, hsmall]
    rw [heq]
    exact hg.add hs

lemma weighted_local_summable
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    (k : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ =>
      weightedFunction w k (p ^ j) / (((p ^ j : ℕ) : ℝ))) := by
  rw [← summable_norm_iff]
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      (mixedLocalMajorant_summable hw.C_nonneg hp k)
  rw [Real.norm_of_nonneg
    (div_nonneg (weightedFunction_nonneg hw k _) (by positivity))]
  exact weighted_local_term_le_majorant hw k hp j

lemma mixedLocalMajorant_tsum {C : ℝ} {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∑' j : ℕ, mixedLocalMajorant C k p j) =
      if p < 2 ^ k then
        1 + (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
          (2 * (p : ℝ) - 1)
      else
        1 + (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
          ((p : ℝ) - 1) := by
  by_cases hsmall : p < 2 ^ k
  · let A : ℝ := 1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)
    let r : ℝ := ((2 : ℝ) * p)⁻¹
    have hr : ‖r‖ < 1 := by
      rw [Real.norm_of_nonneg (by dsimp [r]; positivity)]
      dsimp [r]
      apply inv_lt_one_of_one_lt₀
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      nlinarith
    have hg : Summable (fun j : ℕ => A * r ^ j) :=
      (summable_geometric_of_norm_lt_one hr).mul_left A
    have hs : Summable (fun j : ℕ => if j = 0 then 1 - A else 0) :=
      (hasSum_ite_eq 0 (1 - A)).summable
    have heq : mixedLocalMajorant C k p = fun j : ℕ =>
        A * r ^ j + if j = 0 then 1 - A else 0 := by
      funext j
      by_cases hj : j = 0
      · subst j
        simp [mixedLocalMajorant, A, r]
      · simp [mixedLocalMajorant, A, r, hj, hsmall]
    rw [heq, hg.tsum_add hs, tsum_mul_left,
      tsum_geometric_of_norm_lt_one hr]
    simp only [tsum_ite_eq, if_pos hsmall]
    dsimp [A, r]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hd : 2 * (p : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < 2 * p := by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        nlinarith
      linarith
    field_simp [hp0, hd]
    ring
  · let A : ℝ := 1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)
    let r : ℝ := (p : ℝ)⁻¹
    have hr : ‖r‖ < 1 := by
      rw [Real.norm_of_nonneg (by dsimp [r]; positivity)]
      dsimp [r]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    have hg : Summable (fun j : ℕ => A * r ^ j) :=
      (summable_geometric_of_norm_lt_one hr).mul_left A
    have hs : Summable (fun j : ℕ => if j = 0 then 1 - A else 0) :=
      (hasSum_ite_eq 0 (1 - A)).summable
    have heq : mixedLocalMajorant C k p = fun j : ℕ =>
        A * r ^ j + if j = 0 then 1 - A else 0 := by
      funext j
      by_cases hj : j = 0
      · subst j
        simp [mixedLocalMajorant, A, r]
      · simp [mixedLocalMajorant, A, r, hj, hsmall]
    rw [heq, hg.tsum_add hs, tsum_mul_left,
      tsum_geometric_of_norm_lt_one hr]
    simp only [tsum_ite_eq, if_neg hsmall]
    dsimp [A, r]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hd : (p : ℝ) - 1 ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
    field_simp [hp0, hd]
    ring

/-- Exponent used for the mixed local Euler factor. -/
noncomputable def mixedLocalExponent (C : ℝ) (k p : ℕ) : ℝ :=
  (if p < 2 ^ k then (1 : ℝ) / (4 * p) else 1 / (2 * p)) +
    1 / ((p : ℝ) * ((p : ℝ) - 1)) +
    2 * C * (Real.log (p : ℝ) / (p : ℝ) ^ 2)

private lemma small_base_le {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) / (2 * (2 * (p : ℝ) - 1)) ≤
      1 / (4 * (p : ℝ)) +
        1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1pos : 0 < (p : ℝ) - 1 := by linarith
  have hdenSmall : 0 < 4 * ((p : ℝ) - 1) :=
    mul_pos (by norm_num) hp1pos
  have hfirst :
      (1 : ℝ) / (2 * (2 * (p : ℝ) - 1)) ≤
        1 / (4 * ((p : ℝ) - 1)) := by
    apply one_div_le_one_div_of_le hdenSmall
    nlinarith
  have heq :
      (1 : ℝ) / (4 * ((p : ℝ) - 1)) =
        1 / (4 * (p : ℝ)) +
          1 / (4 * (p : ℝ) * ((p : ℝ) - 1)) := by
    field_simp [hp0, hp1]
    ring
  have hcorr :
      (1 : ℝ) / (4 * (p : ℝ) * ((p : ℝ) - 1)) ≤
        1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    have hp0pos : 0 < (p : ℝ) := by linarith
    have hq : 0 ≤ (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
      div_nonneg zero_le_one (mul_nonneg hp0pos.le hp1pos.le)
    calc
      (1 : ℝ) / (4 * (p : ℝ) * ((p : ℝ) - 1)) =
          (1 / 4 : ℝ) *
            (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        field_simp [hp0, hp1]
      _ ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by nlinarith
  rw [heq] at hfirst
  linarith

private lemma large_base_le {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) / (2 * ((p : ℝ) - 1)) ≤
      1 / (2 * (p : ℝ)) +
        1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  have heq :
      (1 / (2 * (p : ℝ)) +
          1 / ((p : ℝ) * ((p : ℝ) - 1))) -
          1 / (2 * ((p : ℝ) - 1)) =
        1 / (2 * (p : ℝ) * ((p : ℝ) - 1)) := by
    field_simp [hp0, hp1] <;> ring_nf
  rw [← sub_nonneg, heq]
  have hp1pos : 0 < (p : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hp.one_lt)
  exact div_nonneg zero_le_one
    (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hp1pos.le)

lemma weighted_localEuler_le_exp
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    (k : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ,
        weightedFunction w k (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
      Real.exp (mixedLocalExponent C k p) := by
  have hsum := Summable.tsum_le_tsum
    (fun j => weighted_local_term_le_majorant hw k hp j)
    (weighted_local_summable hw k hp)
    (mixedLocalMajorant_summable hw.C_nonneg hp k)
  rw [mixedLocalMajorant_tsum hp k] at hsum
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp1pos : 0 < (p : ℝ) - 1 := sub_pos.mpr hpR
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hpR.le
  have herr := error_prime_term_le hw.C_nonneg hp
  by_cases hsmall : p < 2 ^ k
  · rw [if_pos hsmall] at hsum
    have hdenpos : 0 < 2 * (p : ℝ) - 1 := by nlinarith
    have hsplit :
        (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
            (2 * (p : ℝ) - 1) =
          1 / (2 * (2 * (p : ℝ) - 1)) +
            (C * Real.log (p : ℝ) / (p : ℝ)) /
              (2 * (p : ℝ) - 1) := by
      field_simp [hdenpos.ne']
    have herrSmall :
        (C * Real.log (p : ℝ) / (p : ℝ)) /
            (2 * (p : ℝ) - 1) ≤
          C * Real.log (p : ℝ) /
            ((p : ℝ) * ((p : ℝ) - 1)) := by
      have hp0pos : 0 < (p : ℝ) := zero_lt_one.trans hpR
      have hnum : 0 ≤ C * Real.log (p : ℝ) / (p : ℝ) :=
        div_nonneg (mul_nonneg hw.C_nonneg hlog) hp0pos.le
      calc
        (C * Real.log (p : ℝ) / (p : ℝ)) /
              (2 * (p : ℝ) - 1) ≤
            (C * Real.log (p : ℝ) / (p : ℝ)) /
              ((p : ℝ) - 1) :=
          div_le_div_of_nonneg_left hnum hp1pos (by linarith)
        _ = C * Real.log (p : ℝ) /
              ((p : ℝ) * ((p : ℝ) - 1)) := by
          field_simp [ne_of_gt (show (0 : ℝ) < p by positivity), hp1pos.ne']
    have hx :
        (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
            (2 * (p : ℝ) - 1) ≤ mixedLocalExponent C k p := by
      rw [hsplit, mixedLocalExponent, if_pos hsmall]
      linarith [small_base_le hp, herrSmall]
    calc
      (∑' j : ℕ,
          weightedFunction w k (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
          1 + (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
            (2 * (p : ℝ) - 1) := hsum
      _ ≤ 1 + mixedLocalExponent C k p := by linarith
      _ ≤ Real.exp (mixedLocalExponent C k p) := by
        simpa [add_comm] using Real.add_one_le_exp (mixedLocalExponent C k p)
  · rw [if_neg hsmall] at hsum
    have hsplit :
        (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
            ((p : ℝ) - 1) =
          1 / (2 * ((p : ℝ) - 1)) +
            C * Real.log (p : ℝ) /
              ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp [ne_of_gt (show (0 : ℝ) < p by positivity), hp1pos.ne']
    have hx :
        (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
            ((p : ℝ) - 1) ≤ mixedLocalExponent C k p := by
      rw [hsplit, mixedLocalExponent, if_neg hsmall]
      linarith [large_base_le hp]
    calc
      (∑' j : ℕ,
          weightedFunction w k (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
          1 + (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
            ((p : ℝ) - 1) := hsum
      _ ≤ 1 + mixedLocalExponent C k p := by linarith
      _ ≤ Real.exp (mixedLocalExponent C k p) := by
        simpa [add_comm] using Real.add_one_le_exp (mixedLocalExponent C k p)

private lemma high_quarter_prime_sum_le_one (k : ℕ) :
    Finset.sum (2 ^ (k + 2) + 1).primesBelow
      (fun p : ℕ => if p < 2 ^ k then 0
        else (1 : ℝ) / (4 * (p : ℝ))) ≤ 1 := by
  classical
  let N : ℕ := 2 ^ (k + 2)
  let Y : ℕ := 2 ^ k
  let P : Finset ℕ := (N + 1).primesBelow
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYcast : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hpoint : ∀ p ∈ P,
      (if p < Y then 0 else (1 : ℝ) / (4 * (p : ℝ))) ≤
        1 / (4 * (Y : ℝ)) := by
    intro p hpP
    by_cases hpY : p < Y
    · simp [hpY]
    · rw [if_neg hpY]
      have hYp : (Y : ℝ) ≤ p := by exact_mod_cast (Nat.le_of_not_gt hpY)
      have hdenY : 0 < 4 * (Y : ℝ) := by positivity
      exact one_div_le_one_div_of_le hdenY (by nlinarith)
  have hcard : P.card ≤ N := by
    have hsub : P ⊆ Finset.Icc 1 N := by
      intro p hpP
      have hp' := Nat.mem_primesBelow.mp hpP
      exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, Nat.le_of_lt_succ hp'.1⟩
    have hc := Finset.card_le_card hsub
    simpa using hc
  have hcalc :
    (∑ p ∈ P, if p < Y then 0 else (1 : ℝ) / (4 * (p : ℝ))) ≤ 1 := by
    calc
      (∑ p ∈ P, if p < Y then 0 else (1 : ℝ) / (4 * (p : ℝ))) ≤
        ∑ _p ∈ P, 1 / (4 * (Y : ℝ)) :=
        Finset.sum_le_sum hpoint
      _ = (P.card : ℝ) * (1 / (4 * (Y : ℝ))) := by simp
      _ ≤ (N : ℝ) * (1 / (4 * (Y : ℝ))) := by
        gcongr
      _ = 1 := by
        have hNY : N = 4 * Y := by simp [N, Y, pow_add, Nat.mul_comm]
        rw [hNY]
        push_cast
        field_simp [ne_of_gt hYcast]
  simpa [P, N, Y] using hcalc

/-- The sum of all mixed local exponents at the dyadic frontier. -/
theorem sum_mixedLocalExponent_le
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (hk : 1 ≤ k) :
    (∑ p ∈ (2 ^ (k + 2) + 1).primesBelow,
        mixedLocalExponent C k p) ≤
      (1 / 4 : ℝ) *
          Real.log (cleanMertensConstant *
            Real.log ((2 ^ (k + 2) : ℕ) : ℝ)) +
        2 + 8 * C * Real.log 2 := by
  classical
  let N : ℕ := 2 ^ (k + 2)
  let Y : ℕ := 2 ^ k
  let P : Finset ℕ := (N + 1).primesBelow
  have hN : 3 ≤ N := by
    dsimp [N]
    have : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hP : P = (Finset.Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [P, Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨hp.one_le, Nat.le_of_lt_succ hpN⟩, hp⟩
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨Nat.lt_succ_of_le hpN, hp⟩
  have hbase :
      (∑ p ∈ P, if p < Y then (1 : ℝ) / (4 * (p : ℝ))
        else 1 / (2 * (p : ℝ))) ≤
        (1 / 4 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ)) + 1 := by
    have hsplit :
        (∑ p ∈ P, if p < Y then (1 : ℝ) / (4 * (p : ℝ))
          else 1 / (2 * (p : ℝ))) =
          (1 / 4 : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) +
            ∑ p ∈ P, if p < Y then 0 else (1 : ℝ) / (4 * (p : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hpP
      by_cases hpY : p < Y <;> simp [hpY]
      <;> ring
    rw [hsplit]
    have hrec := TauInvTypeMean448.reciprocal_prime_sum_upper N hN
    have hhigh := high_quarter_prime_sum_le_one k
    have hrecP : (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ≤
        Real.log (cleanMertensConstant * Real.log (N : ℝ)) := by
      simpa [hP] using hrec
    have hrecMul := mul_le_mul_of_nonneg_left hrecP
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hhigh' :
        (∑ p ∈ P, if p < Y then 0 else (1 : ℝ) / (4 * (p : ℝ))) ≤ 1 := by
      simpa [P, N, Y] using hhigh
    linarith
  have hcorr :
      (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
    have hsub : P ⊆ Finset.Icc 2 N := by
      intro p hpP
      have hp' := Nat.mem_primesBelow.mp hpP
      exact Finset.mem_Icc.mpr ⟨hp'.2.two_le, Nat.le_of_lt_succ hp'.1⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ => by
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        exact div_nonneg zero_le_one
          (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (by linarith))))).trans
      (TauInvTypeMean448.sum_Icc_two_inv_mul_pred_le_one N)
  have herr :
      (∑ p ∈ P, 2 * C * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) ≤
        8 * C * Real.log 2 := by
    calc
      (∑ p ∈ P, 2 * C * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) =
          2 * C * ∑ p ∈ P,
            (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * C * (4 * Real.log 2) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hC)
        rw [hP]
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
      _ = 8 * C * Real.log 2 := by ring
  change (∑ p ∈ P, mixedLocalExponent C k p) ≤ _
  simp_rw [mixedLocalExponent, Finset.sum_add_distrib]
  change
    (∑ p ∈ P, if p < Y then (1 : ℝ) / (4 * (p : ℝ))
      else 1 / (2 * (p : ℝ))) +
        (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) +
        (∑ p ∈ P, 2 * C * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) ≤ _
  dsimp [N] at hbase ⊢
  linarith

/-- Mixed Euler-product estimate at `N=2^(k+2)`. -/
theorem weighted_eulerProduct_le
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    (k : ℕ) (hk : 1 ≤ k) :
    (∏ p ∈ (2 ^ (k + 2) + 1).primesBelow,
        ∑' j : ℕ,
          weightedFunction w k (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
      Real.exp ((1 / 4 : ℝ) *
          Real.log (cleanMertensConstant *
            Real.log ((2 ^ (k + 2) : ℕ) : ℝ)) +
        2 + 8 * C * Real.log 2) := by
  let P : Finset ℕ := (2 ^ (k + 2) + 1).primesBelow
  have hprod :
      (∏ p ∈ P, ∑' j : ℕ,
          weightedFunction w k (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
        ∏ p ∈ P, Real.exp (mixedLocalExponent C k p) := by
    apply Finset.prod_le_prod
    · intro p hpP
      exact tsum_nonneg fun j => div_nonneg (weightedFunction_nonneg hw k _) (by positivity)
    · intro p hpP
      exact weighted_localEuler_le_exp hw k (Nat.prime_of_mem_primesBelow hpP)
  calc
    (∏ p ∈ (2 ^ (k + 2) + 1).primesBelow,
        ∑' j : ℕ,
          weightedFunction w k (p ^ j) / (((p ^ j : ℕ) : ℝ))) =
        ∏ p ∈ P, ∑' j : ℕ,
          weightedFunction w k (p ^ j) / (((p ^ j : ℕ) : ℝ)) := rfl
    _ ≤ ∏ p ∈ P, Real.exp (mixedLocalExponent C k p) := hprod
    _ = Real.exp (∑ p ∈ P, mixedLocalExponent C k p) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp ((1 / 4 : ℝ) *
          Real.log (cleanMertensConstant *
            Real.log ((2 ^ (k + 2) : ℕ) : ℝ)) +
        2 + 8 * C * Real.log 2) := by
      rw [Real.exp_le_exp]
      exact sum_mixedLocalExponent_le hw.C_nonneg k hk

/-- Constant in the logarithmic-frontier mixed mean estimate. -/
noncomputable def weightedFrontierConstant (C : ℝ) : ℝ :=
  (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
    Real.exp (2 + 8 * C * Real.log 2) *
      cleanMertensConstant ^ (1 / 4 : ℝ)

lemma weightedFrontierConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ weightedFrontierConstant C := by
  have hm := HalberstamScratch.explicitMassConstant_nonneg
    (show 0 ≤ 1 + C by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  unfold weightedFrontierConstant
  exact mul_nonneg
    (mul_nonneg (by linarith) (Real.exp_pos _).le)
    (Real.rpow_nonneg cleanMertensConstant_pos.le _)

/-- The mixed Halberstam--Richert mean at the exact dyadic frontier, before
rewriting `log(2^(k+2))` in terms of `k`. -/
theorem weighted_mean_frontier_le
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Icc 1 (2 ^ (k + 2)), weightedFunction w k n) ≤
      weightedFrontierConstant C * ((2 ^ (k + 2) : ℕ) : ℝ) *
        (Real.log ((2 ^ (k + 2) : ℕ) : ℝ)) ^ (-(3 : ℝ) / 4) := by
  let N : ℕ := 2 ^ (k + 2)
  have hN : 2 ≤ N := by
    dsimp [N]
    have : 2 ^ 1 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hN3 : 3 ≤ N := by
    dsimp [N]
    have : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hC1 : 0 ≤ 1 + C := by linarith [hw.C_nonneg]
  have hhr := HalberstamComplete448.halberstam_richert_explicit
    (weightedFunction w k)
    (weightedFunction_zero hw k)
    (weightedFunction_one hw k)
    (weightedFunction_mul_of_coprime hw k)
    (weightedFunction_nonneg hw k)
    (1 + C) 1 hC1 (by norm_num) (by norm_num)
    (fun p hp j => by
      simpa using weightedFunction_prime_pow_le_one_add_C hw k hp (j := j))
    N hN
  have heuler := weighted_eulerProduct_le hw k hk
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hfac : 0 ≤
      (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    have hm := HalberstamScratch.explicitMassConstant_nonneg hC1
      (show (0 : ℝ) ≤ 1 by norm_num)
    positivity
  have hraw := hhr.trans (mul_le_mul_of_nonneg_left heuler hfac)
  have hthree : 0 < cleanMertensConstant * Real.log (N : ℝ) :=
    mul_pos cleanMertensConstant_pos hlogN
  have hexpQuarter :
      Real.exp ((1 / 4 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ))) =
        (cleanMertensConstant * Real.log (N : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos hthree]
    congr 1
    ring
  have hrpowMul :
      (cleanMertensConstant * Real.log (N : ℝ)) ^ (1 / 4 : ℝ) =
        cleanMertensConstant ^ (1 / 4 : ℝ) *
          (Real.log (N : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow cleanMertensConstant_pos.le hlogN.le]
  have hexpSplit :
      Real.exp ((1 / 4 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ)) +
          2 + 8 * C * Real.log 2) =
        Real.exp ((1 / 4 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ))) *
          Real.exp (2 + 8 * C * Real.log 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
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
          (Real.log (N : ℝ)) ^ (1 / 4 : ℝ)) := by
        rw [Real.rpow_neg_one]
      _ = (N : ℝ) * (Real.log (N : ℝ)) ^
          (-(1 : ℝ) + 1 / 4) := by
        rw [Real.rpow_add hlogN]
      _ = (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4) := by
        congr 2
        ring
  change (∑ n ∈ Finset.Icc 1 N, weightedFunction w k n) ≤ _
  calc
    (∑ n ∈ Finset.Icc 1 N, weightedFunction w k n) ≤
        (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            Real.exp ((1 / 4 : ℝ) *
              Real.log (cleanMertensConstant * Real.log (N : ℝ)) +
              2 + 8 * C * Real.log 2) := by
      simpa only [HalberstamScratch.partialSum] using hraw
    _ = weightedFrontierConstant C * (N : ℝ) *
          (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4) := by
      rw [hexpSplit, hexpQuarter, hrpowMul]
      unfold weightedFrontierConstant
      calc
        (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              (N : ℝ) / Real.log (N : ℝ) *
              (cleanMertensConstant ^ (1 / 4 : ℝ) *
                (Real.log (N : ℝ)) ^ (1 / 4 : ℝ) *
                Real.exp (2 + 8 * C * Real.log 2)) =
            (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (2 + 8 * C * Real.log 2) *
              cleanMertensConstant ^ (1 / 4 : ℝ) *
              ((N : ℝ) / Real.log (N : ℝ) *
                (Real.log (N : ℝ)) ^ (1 / 4 : ℝ)) := by ring
        _ = (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (2 + 8 * C * Real.log 2) *
              cleanMertensConstant ^ (1 / 4 : ℝ) *
              ((N : ℝ) *
                (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4)) := by rw [hcancel]
        _ = (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (2 + 8 * C * Real.log 2) *
              cleanMertensConstant ^ (1 / 4 : ℝ) * (N : ℝ) *
              (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4) := by ring
    _ = weightedFrontierConstant C * ((2 ^ (k + 2) : ℕ) : ℝ) *
          (Real.log ((2 ^ (k + 2) : ℕ) : ℝ)) ^ (-(3 : ℝ) / 4) := rfl

/-- Constant in the final `2^k k^(-3/4)` form. -/
noncomputable def weightedDyadicConstant (C : ℝ) : ℝ :=
  4 * weightedFrontierConstant C *
    (Real.log 2) ^ (-(3 : ℝ) / 4)

lemma weightedDyadicConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ weightedDyadicConstant C := by
  unfold weightedDyadicConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (weightedFrontierConstant_nonneg hC))
    (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _)

/-- The required truncated-weight mean, with the exponent `-3/4` exposed. -/
theorem weighted_mean_dyadic_le
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Icc 1 (2 ^ (k + 2)), omegaWeight k n * w n) ≤
      weightedDyadicConstant C * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(3 : ℝ) / 4) := by
  let N : ℕ := 2 ^ (k + 2)
  have hmain := weighted_mean_frontier_le hw k hk
  have hpoint :
      (∑ n ∈ Finset.Icc 1 N, omegaWeight k n * w n) =
        ∑ n ∈ Finset.Icc 1 N, weightedFunction w k n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    simp [weightedFunction, omegaWeightAF, hn0, mul_comm]
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogN : Real.log (N : ℝ) = ((k + 2 : ℕ) : ℝ) * Real.log 2 := by
    dsimp [N]
    rw [show (((2 ^ (k + 2) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 2) by norm_num,
      Real.log_pow]
  have hlogs : (k : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    rw [hlogN]
    gcongr
    norm_num
  have hsmallPos : 0 < (k : ℝ) * Real.log 2 := mul_pos hkR hlog2
  have hbigPos : 0 < Real.log (N : ℝ) := hsmallPos.trans_le hlogs
  have hrpowLe :
      (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4) ≤
        ((k : ℝ) * Real.log 2) ^ (-(3 : ℝ) / 4) := by
    have hanti := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show (-(3 : ℝ) / 4) ≤ 0 by norm_num)
    exact hanti hsmallPos hbigPos hlogs
  have hcoeff : 0 ≤ weightedFrontierConstant C * (N : ℝ) :=
    mul_nonneg (weightedFrontierConstant_nonneg hw.C_nonneg) (Nat.cast_nonneg N)
  rw [hpoint]
  calc
    (∑ n ∈ Finset.Icc 1 N, weightedFunction w k n) ≤
        weightedFrontierConstant C * (N : ℝ) *
          (Real.log (N : ℝ)) ^ (-(3 : ℝ) / 4) := by
      simpa [N] using hmain
    _ ≤ weightedFrontierConstant C * (N : ℝ) *
          (((k : ℝ) * Real.log 2) ^ (-(3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hrpowLe hcoeff
    _ = weightedDyadicConstant C * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4) := by
      have hNcast : (N : ℝ) = 4 * ((2 ^ k : ℕ) : ℝ) := by
        dsimp [N]
        norm_num [pow_add]
        ring
      rw [hNcast, Real.mul_rpow hkR.le hlog2.le]
      unfold weightedDyadicConstant
      ring

#print axioms weighted_mean_dyadic_le

end WeightedTauInv448
