/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Abel's binomial identity and Ford's Lemma 4.2

This file proves the finite identity and estimate used in Section 4 of
Kevin Ford's *Integers with a divisor in (y, 2y]*.  In particular, the
summation range, the positivity cut-off, and the constant `exp 4` in
`lemma_four_two` are exactly those in the printed lemma.
-/

namespace Erdos896.Ford

open scoped BigOperators
open Polynomial

/-! ## Abel polynomials -/

/-- The Abel polynomial `Aₙ(X) = X (X + n)^(n-1)`, with `A₀ = 1`. -/
noncomputable def abelPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * (X + C (n + 1 : ℝ)) ^ n

@[simp]
theorem abelPolynomial_zero : abelPolynomial 0 = 1 := rfl

@[simp]
theorem abelPolynomial_succ (n : ℕ) :
    abelPolynomial (n + 1) = X * (X + C (n + 1 : ℝ)) ^ n := rfl

@[simp]
theorem eval_abelPolynomial_zero (x : ℝ) :
    (abelPolynomial 0).eval x = 1 := by
  simp

@[simp]
theorem eval_abelPolynomial_succ (n : ℕ) (x : ℝ) :
    (abelPolynomial (n + 1)).eval x = x * (x + (n + 1 : ℝ)) ^ n := by
  simp [abelPolynomial]

@[simp]
theorem eval_zero_abelPolynomial (n : ℕ) :
    (abelPolynomial n).eval 0 = if n = 0 then 1 else 0 := by
  cases n <;> simp

/-- The differential recurrence `A'ₙ₊₁(X) = (n+1) Aₙ(X+1)`. -/
theorem derivative_abelPolynomial_succ (n : ℕ) :
    (abelPolynomial (n + 1)).derivative =
      C (n + 1 : ℝ) * (abelPolynomial n).comp (X + C 1) := by
  cases n with
  | zero => simp [abelPolynomial]
  | succ n =>
      simp [abelPolynomial, derivative_mul, derivative_pow]
      ring

private theorem polynomial_eq_of_derivative_eq_of_eval_zero_eq
    {P Q : ℝ[X]} (hderiv : P.derivative = Q.derivative)
    (heval : P.eval 0 = Q.eval 0) : P = Q := by
  have hzero : (P - Q).derivative = 0 := by
    rw [derivative_sub, hderiv, sub_self]
  have hconst := eq_C_of_derivative_eq_zero hzero
  have hcoeff : (P - Q).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_sub, heval, sub_self]
  rw [hcoeff, C_0] at hconst
  exact sub_eq_zero.mp hconst

/-- Abel polynomials are of binomial type. -/
theorem abelPolynomial_binomial (t : ℕ) (b : ℝ) :
    (∑ j ∈ Finset.range (t + 1),
        C (t.choose j : ℝ) * abelPolynomial j *
          C ((abelPolynomial (t - j)).eval b)) =
      (abelPolynomial t).comp (X + C b) := by
  induction t with
  | zero => simp
  | succ t ih =>
      apply polynomial_eq_of_derivative_eq_of_eval_zero_eq
      · rw [Finset.sum_range_succ']
        simp only [derivative_add, derivative_sum, derivative_mul,
          derivative_C, zero_mul, zero_add]
        simp_rw [derivative_abelPolynomial_succ]
        simp only [mul_zero, add_zero, abelPolynomial_zero, derivative_one,
          C_0, zero_mul]
        rw [derivative_comp, derivative_abelPolynomial_succ]
        simp only [derivative_add, derivative_X, derivative_C, add_zero,
          one_mul]
        simp only [Nat.add_sub_add_right]
        calc
          (∑ x ∈ Finset.range (t + 1),
              C ((t + 1).choose (x + 1) : ℝ) *
                  (C (x + 1 : ℝ) * (abelPolynomial x).comp (X + C 1)) *
                C ((abelPolynomial (t - x)).eval b)) =
              C (t + 1 : ℝ) *
                (∑ x ∈ Finset.range (t + 1),
                    C (t.choose x : ℝ) * abelPolynomial x *
                      C ((abelPolynomial (t - x)).eval b)).comp (X + C 1) := by
                rw [sum_comp, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x hx
                have hchoose :
                    ((t + 1).choose (x + 1) : ℝ) * (x + 1 : ℝ) =
                      (t + 1 : ℝ) * (t.choose x : ℝ) := by
                  exact_mod_cast (Nat.add_one_mul_choose_eq t x).symm
                have hchooseC :
                    C ((t + 1).choose (x + 1) : ℝ) * C (x + 1 : ℝ) =
                      C (t + 1 : ℝ) * C (t.choose x : ℝ) := by
                  rw [← C_mul, ← C_mul, hchoose]
                simp only [mul_comp, C_comp]
                rw [← mul_assoc, hchooseC]
                ring
          _ = C (t + 1 : ℝ) *
                ((abelPolynomial t).comp (X + C b)).comp (X + C 1) := by
              rw [ih]
          _ = C (t + 1 : ℝ) *
                ((abelPolynomial t).comp (X + C 1)).comp (X + C b) := by
              have hshift :
                  ((X : ℝ[X]) + C b).comp (X + C (1 : ℝ)) =
                    (X + C (1 : ℝ)).comp (X + C b) := by
                simp
                ring
              simp only [comp_assoc]
              rw [hshift]
          _ = (C (t + 1 : ℝ) *
                (abelPolynomial t).comp (X + C 1)).comp (X + C b) := by
              rw [mul_comp, C_comp]
      · simp only [eval_finsetSum, eval_mul, eval_C,
          eval_comp, eval_add, eval_X, zero_add]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro j hj hj0
          simp [eval_zero_abelPolynomial, hj0]
        · simp

/-- Pointwise form of the binomial-type identity for Abel polynomials. -/
theorem abelPolynomial_binomial_eval (t : ℕ) (a b : ℝ) :
    (∑ j ∈ Finset.range (t + 1),
        (t.choose j : ℝ) * (abelPolynomial j).eval a *
          (abelPolynomial (t - j)).eval b) =
      (abelPolynomial t).eval (a + b) := by
  have h := congrArg (Polynomial.eval a) (abelPolynomial_binomial t b)
  simpa [eval_finsetSum] using h

private theorem mul_zpow_sub_one_eq_eval_abelPolynomial
    (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    x * (x + (n : ℝ)) ^ ((n : ℤ) - 1) =
      (abelPolynomial n).eval x := by
  cases n with
  | zero => simp [hx]
  | succ n =>
      simp only [Int.natCast_succ, Int.add_sub_cancel, zpow_natCast,
        eval_abelPolynomial_succ]
      push_cast
      ring

/-- Abel's complete finite identity, equation (4.2) in Ford's paper. -/
theorem abel_zpow_identity {t : ℕ} (ht : 1 ≤ t) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑ j ∈ Finset.range (t + 1),
        (t.choose j : ℝ) *
          (a + (j : ℝ)) ^ ((j : ℤ) - 1) *
          (b + (t - j : ℕ)) ^ ((t - j : ℤ) - 1)) =
      (a⁻¹ + b⁻¹) *
        ((t : ℝ) + a + b) ^ ((t : ℤ) - 1) := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  apply mul_left_cancel₀ hab
  rw [Finset.mul_sum]
  have hpoly := abelPolynomial_binomial_eval t a b
  calc
    ∑ j ∈ Finset.range (t + 1),
        a * b * ((t.choose j : ℝ) *
          (a + (j : ℝ)) ^ ((j : ℤ) - 1) *
          (b + (t - j : ℕ)) ^ ((t - j : ℤ) - 1)) =
        ∑ j ∈ Finset.range (t + 1),
          (t.choose j : ℝ) * (abelPolynomial j).eval a *
            (abelPolynomial (t - j)).eval b := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjt : j ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [← mul_zpow_sub_one_eq_eval_abelPolynomial j a ha,
        ← mul_zpow_sub_one_eq_eval_abelPolynomial (t - j) b hb]
      rw [Int.natCast_sub hjt]
      ring
    _ = (abelPolynomial t).eval (a + b) := hpoly
    _ = a * b * ((a⁻¹ + b⁻¹) *
        ((t : ℝ) + a + b) ^ ((t : ℤ) - 1)) := by
      obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      simp only [eval_abelPolynomial_succ, Int.natCast_succ,
        Int.add_sub_cancel, zpow_natCast]
      field_simp
      push_cast
      ring

/-! ## Ford's Lemma 4.2 -/

private theorem normalized_pow_mono {m n : ℕ} {c : ℝ}
    (hm : 0 < m) (hmn : m ≤ n) (_hc : c ≤ 0) (hmc : 0 < (m : ℝ) + c) :
    (1 + c / (m : ℝ)) ^ m ≤ (1 + c / (n : ℝ)) ^ n := by
  have hn : 0 < n := hm.trans_le hmn
  let w : ℝ := (m : ℝ) / n
  let p : ℝ := 1 + c / m
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    exact (div_le_one (by positivity)).2 (by exact_mod_cast hmn)
  have hp : 0 ≤ p := by
    dsimp [p]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rw [show 1 + c / (m : ℝ) = ((m : ℝ) + c) / m by field_simp]
    positivity
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hw0 (sub_nonneg.mpr hw1)
    hp (by norm_num : (0 : ℝ) ≤ 1) (by ring : w + (1 - w) = 1)
  have hbase : p ^ w ≤ 1 + c / (n : ℝ) := by
    norm_num at hamgm
    dsimp [w, p] at hamgm ⊢
    convert hamgm using 1 <;> field_simp <;> ring
  have hright : 0 ≤ 1 + c / (n : ℝ) := by
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hcn : 0 ≤ (n : ℝ) + c := by linarith
    rw [show 1 + c / (n : ℝ) = ((n : ℝ) + c) / n by field_simp]
    positivity
  have hpw : 0 ≤ p ^ w := Real.rpow_nonneg hp _
  have hpow := pow_le_pow_left₀ hpw hbase n
  calc
    (1 + c / (m : ℝ)) ^ m = p ^ (m : ℝ) := by
      rw [Real.rpow_natCast]
    _ = p ^ (w * (n : ℝ)) := by
      congr 1
      dsimp [w]
      field_simp
    _ = (p ^ w) ^ (n : ℝ) := by rw [Real.rpow_mul hp]
    _ = (p ^ w) ^ n := by rw [Real.rpow_natCast]
    _ ≤ (1 + c / (n : ℝ)) ^ n := hpow

private theorem two_mul_add_three_pow_le_exp_four
    {n : ℕ} {s : ℝ} (hs : 0 < s) (hns : (n : ℝ) ≤ s) :
    2 * (s + 3) ^ n ≤ Real.exp 4 * s ^ n := by
  have hone : 1 + 3 / s ≤ Real.exp (3 / s) := by
    simpa [add_comm] using Real.add_one_le_exp (3 / s)
  have hadd : s + 3 ≤ s * Real.exp (3 / s) := by
    calc
      s + 3 = s * (1 + 3 / s) := by field_simp
      _ ≤ s * Real.exp (3 / s) := mul_le_mul_of_nonneg_left hone hs.le
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ s + 3) hadd n
  have hexp : Real.exp (3 / s * n) ≤ Real.exp 3 := by
    apply Real.exp_le_exp.mpr
    have hdiv : (n : ℝ) / s ≤ 1 := (div_le_one hs).2 hns
    calc
      3 / s * (n : ℝ) = 3 * ((n : ℝ) / s) := by ring
      _ ≤ 3 * 1 := by gcongr
      _ = 3 := by ring
  calc
    2 * (s + 3) ^ n ≤ 2 * (s * Real.exp (3 / s)) ^ n :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 2 * (Real.exp (3 / s * n) * s ^ n) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring
    _ ≤ 2 * (Real.exp 3 * s ^ n) := by gcongr
    _ ≤ Real.exp 4 * s ^ n := by
      rw [show (4 : ℝ) = 1 + 3 by norm_num, Real.exp_add]
      calc
        2 * (Real.exp 3 * s ^ n) ≤
            Real.exp 1 * (Real.exp 3 * s ^ n) :=
          mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le (by positivity)
        _ = Real.exp 1 * Real.exp 3 * s ^ n := by ring

/-- The finite sum denoted `Cₜ(a,b)` in Ford's proof of Lemma 4.2. -/
noncomputable def fordLemmaFourTwoSum (t : ℕ) (a b : ℝ) : ℝ :=
  ∑ j ∈ (Finset.Icc 1 (t - 1)).filter (fun j : ℕ ↦ 0 < a + (j : ℝ)),
    (t.choose j : ℝ) * (a + (j : ℝ)) ^ (j - 1) *
      (b + (t - j : ℕ)) ^ (t - j - 1)

private noncomputable def fordZTerm (t : ℕ) (a b : ℝ) (j : ℕ) : ℝ :=
  (t.choose j : ℝ) * (a + (j : ℝ)) ^ ((j : ℤ) - 1) *
    (b + (t - j : ℕ)) ^ ((t - j : ℤ) - 1)

private theorem fordLemmaFourTwoSum_le_complete {t : ℕ} (ht : 2 ≤ t) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    fordLemmaFourTwoSum t a b ≤
      (a⁻¹ + b⁻¹) * ((t : ℝ) + a + b) ^ (t - 1) := by
  have hrewrite : fordLemmaFourTwoSum t a b =
      ∑ j ∈ (Finset.Icc 1 (t - 1)).filter (fun j : ℕ ↦ 0 < a + (j : ℝ)),
        fordZTerm t a b j := by
    unfold fordLemmaFourTwoSum
    apply Finset.sum_congr rfl
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjpos⟩
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjIcc).1
    have hjtop : j ≤ t - 1 := (Finset.mem_Icc.mp hjIcc).2
    have hjt : j ≤ t := hjtop.trans (Nat.sub_le t 1)
    have htj1 : 1 ≤ t - j := by omega
    unfold fordZTerm
    rw [← zpow_natCast, ← zpow_natCast]
    rw [Int.natCast_sub hj1, Int.natCast_sub htj1]
    rw [Int.natCast_sub hjt]
    push_cast
    ring
  rw [hrewrite]
  calc
    (∑ j ∈ (Finset.Icc 1 (t - 1)).filter (fun j : ℕ ↦ 0 < a + (j : ℝ)),
        fordZTerm t a b j) ≤
        ∑ j ∈ Finset.range (t + 1), fordZTerm t a b j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjIcc, _⟩
        apply Finset.mem_range.mpr
        have hjtop := (Finset.mem_Icc.mp hjIcc).2
        omega
      · intro j hjRange hjNot
        unfold fordZTerm
        positivity
    _ = (a⁻¹ + b⁻¹) * ((t : ℝ) + a + b) ^ (t - 1) := by
      have hid := abel_zpow_identity (t := t) (by omega) ha.ne' hb.ne'
      rw [show ((t : ℤ) - 1) = (t - 1 : ℕ) by omega,
        zpow_natCast] at hid
      simpa [fordZTerm] using hid

private theorem fordLemmaFourTwoSum_mono {t : ℕ} {a b A B : ℝ}
    (haA : a ≤ A) (hb : 0 ≤ b) (hbB : b ≤ B) :
    fordLemmaFourTwoSum t a b ≤ fordLemmaFourTwoSum t A B := by
  unfold fordLemmaFourTwoSum
  calc
    (∑ j ∈ (Finset.Icc 1 (t - 1)).filter
        (fun j : ℕ ↦ 0 < a + (j : ℝ)),
        (t.choose j : ℝ) * (a + (j : ℝ)) ^ (j - 1) *
          (b + (t - j : ℕ)) ^ (t - j - 1)) ≤
      ∑ j ∈ (Finset.Icc 1 (t - 1)).filter
        (fun j : ℕ ↦ 0 < a + (j : ℝ)),
        (t.choose j : ℝ) * (A + (j : ℝ)) ^ (j - 1) *
          (B + (t - j : ℕ)) ^ (t - j - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjpos⟩
      have hleft : (a + (j : ℝ)) ^ (j - 1) ≤
          (A + (j : ℝ)) ^ (j - 1) := by gcongr
      have hright : (b + (t - j : ℕ)) ^ (t - j - 1) ≤
          (B + (t - j : ℕ)) ^ (t - j - 1) := by gcongr
      have hAnon : 0 ≤ A + (j : ℝ) := by linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left hleft (by positivity)) hright
        (by positivity) (mul_nonneg (by positivity) (pow_nonneg hAnon _))
    _ ≤ ∑ j ∈ (Finset.Icc 1 (t - 1)).filter
        (fun j : ℕ ↦ 0 < A + (j : ℝ)),
        (t.choose j : ℝ) * (A + (j : ℝ)) ^ (j - 1) *
          (B + (t - j : ℕ)) ^ (t - j - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjpos⟩
        exact Finset.mem_filter.mpr ⟨hjIcc, lt_of_lt_of_le hjpos (by linarith)⟩
      · intro j hjBig hjSmall
        rcases Finset.mem_filter.mp hjBig with ⟨hjIcc, hjApos⟩
        have hBnonneg : 0 ≤ B := by linarith
        exact mul_nonneg
          (mul_nonneg (by positivity) (pow_nonneg hjApos.le _))
          (pow_nonneg (by positivity) _)

private theorem fordLemmaFourTwoSum_le_exp_four_of_neg_one_le
    {t : ℕ} (ht : 2 ≤ t) {a b : ℝ} (ha : -1 ≤ a) (hb : 0 ≤ b) :
    fordLemmaFourTwoSum t a b ≤
      Real.exp 4 * ((t : ℝ) + a + b) ^ (t - 1) := by
  let A : ℝ := a + 2
  let B : ℝ := b + 1
  let s : ℝ := (t : ℝ) + a + b
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hs : 0 < s := by
    dsimp [s]
    have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hnle : ((t - 1 : ℕ) : ℝ) ≤ s := by
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    dsimp [s]
    push_cast
    linarith
  calc
    fordLemmaFourTwoSum t a b ≤ fordLemmaFourTwoSum t A B :=
      fordLemmaFourTwoSum_mono (by dsimp [A]; linarith) hb (by dsimp [B]; linarith)
    _ ≤ (A⁻¹ + B⁻¹) * ((t : ℝ) + A + B) ^ (t - 1) :=
      fordLemmaFourTwoSum_le_complete ht hA hB
    _ ≤ 2 * (s + 3) ^ (t - 1) := by
      have hAone : 1 ≤ A := by dsimp [A]; linarith
      have hBone : 1 ≤ B := by dsimp [B]; linarith
      have hinv : A⁻¹ + B⁻¹ ≤ 2 := by
        have hAi : A⁻¹ ≤ 1 := (inv_le_one₀ hA).2 hAone
        have hBi : B⁻¹ ≤ 1 := (inv_le_one₀ hB).2 hBone
        linarith
      have hpow : 0 ≤ (s + 3) ^ (t - 1) := by positivity
      rw [show (t : ℝ) + A + B = s + 3 by dsimp [A, B, s]; ring]
      exact mul_le_mul_of_nonneg_right hinv hpow
    _ ≤ Real.exp 4 * s ^ (t - 1) :=
      two_mul_add_three_pow_le_exp_four hs hnle
    _ = Real.exp 4 * ((t : ℝ) + a + b) ^ (t - 1) := rfl

private theorem fordLemmaFourTwoSum_le_factor_of_lt_neg_one
    {t : ℕ} (ht : 2 ≤ t) {a b : ℝ}
    (haLow : (1 : ℝ) - t < a) (ha : a < -1) (hb : 0 ≤ b) :
    fordLemmaFourTwoSum t a b ≤
      (((t : ℝ) + a) / (t - 1 : ℕ)) ^ (t - 1) *
        fordLemmaFourTwoSum t (-1) b := by
  let R : ℝ := (((t : ℝ) + a) / (t - 1 : ℕ)) ^ (t - 1)
  have ht1 : 0 < (t - 1 : ℕ) := by omega
  have hta : 0 < (t : ℝ) + a := by
    have htR : (t : ℝ) ≥ 2 := by exact_mod_cast ht
    linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  unfold fordLemmaFourTwoSum
  let small := (Finset.Icc 1 (t - 1)).filter
    (fun j : ℕ ↦ 0 < a + (j : ℝ))
  let big := (Finset.Icc 1 (t - 1)).filter
    (fun j : ℕ ↦ 0 < (-1 : ℝ) + (j : ℝ))
  calc
    (∑ j ∈ small,
        (t.choose j : ℝ) * (a + (j : ℝ)) ^ (j - 1) *
          (b + (t - j : ℕ)) ^ (t - j - 1)) ≤
      ∑ j ∈ small, R *
        ((t.choose j : ℝ) * ((-1 : ℝ) + (j : ℝ)) ^ (j - 1) *
          (b + (t - j : ℕ)) ^ (t - j - 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjpos⟩
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjIcc).1
      have hjtop : j ≤ t - 1 := (Finset.mem_Icc.mp hjIcc).2
      have hj2 : 2 ≤ j := by
        have hjR : (j : ℝ) > 1 := by linarith
        exact_mod_cast hjR
      have hmpos : 0 < j - 1 := by omega
      have hmn : j - 1 ≤ t - 1 := by omega
      have hmc : 0 < ((j - 1 : ℕ) : ℝ) + (a + 1) := by
        rw [Nat.cast_sub hj1]
        push_cast
        linarith
      have hnorm := normalized_pow_mono hmpos hmn (by linarith : a + 1 ≤ 0) hmc
      have hmR : (0 : ℝ) < (j - 1 : ℕ) := by exact_mod_cast hmpos
      have hnR : (0 : ℝ) < (t - 1 : ℕ) := by exact_mod_cast ht1
      have heqLeft : a + (j : ℝ) =
          (j - 1 : ℕ) * (1 + (a + 1) / (j - 1 : ℕ)) := by
        field_simp [ne_of_gt hmR]
        rw [Nat.cast_sub hj1]
        push_cast
        ring
      have heqRight : 1 + (a + 1) / (t - 1 : ℕ) =
          ((t : ℝ) + a) / (t - 1 : ℕ) := by
        field_simp [ne_of_gt hnR]
        rw [Nat.cast_sub (by omega : 1 ≤ t)]
        push_cast
        ring
      have hleft : (a + (j : ℝ)) ^ (j - 1) ≤
          R * ((-1 : ℝ) + (j : ℝ)) ^ (j - 1) := by
        calc
          (a + (j : ℝ)) ^ (j - 1) =
              ((j - 1 : ℕ) : ℝ) ^ (j - 1) *
                (1 + (a + 1) / (j - 1 : ℕ)) ^ (j - 1) := by
            rw [heqLeft, mul_pow]
          _ ≤ ((j - 1 : ℕ) : ℝ) ^ (j - 1) *
                (1 + (a + 1) / (t - 1 : ℕ)) ^ (t - 1) := by gcongr
          _ = R * ((-1 : ℝ) + (j : ℝ)) ^ (j - 1) := by
            rw [heqRight]
            dsimp [R]
            rw [Nat.cast_sub hj1]
            push_cast
            ring
      have hchoose : 0 ≤ (t.choose j : ℝ) := by positivity
      have hright : 0 ≤ (b + (t - j : ℕ)) ^ (t - j - 1) := by positivity
      calc
        (t.choose j : ℝ) * (a + (j : ℝ)) ^ (j - 1) *
            (b + (t - j : ℕ)) ^ (t - j - 1) ≤
          (t.choose j : ℝ) *
              (R * ((-1 : ℝ) + (j : ℝ)) ^ (j - 1)) *
            (b + (t - j : ℕ)) ^ (t - j - 1) := by gcongr
        _ = R * ((t.choose j : ℝ) *
              ((-1 : ℝ) + (j : ℝ)) ^ (j - 1) *
            (b + (t - j : ℕ)) ^ (t - j - 1)) := by ring
    _ = R * ∑ j ∈ small,
        (t.choose j : ℝ) * ((-1 : ℝ) + (j : ℝ)) ^ (j - 1) *
          (b + (t - j : ℕ)) ^ (t - j - 1) := by rw [Finset.mul_sum]
    _ ≤ R * ∑ j ∈ big,
        (t.choose j : ℝ) * ((-1 : ℝ) + (j : ℝ)) ^ (j - 1) *
          (b + (t - j : ℕ)) ^ (t - j - 1) := by
      apply mul_le_mul_of_nonneg_left _ hR
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjpos⟩
        exact Finset.mem_filter.mpr ⟨hjIcc, by linarith⟩
      · intro j hjBig hjSmall
        rcases Finset.mem_filter.mp hjBig with ⟨hjIcc, hjpos⟩
        positivity
    _ = (((t : ℝ) + a) / (t - 1 : ℕ)) ^ (t - 1) *
          (∑ j ∈ (Finset.Icc 1 (t - 1)).filter
            (fun j : ℕ ↦ 0 < (-1 : ℝ) + (j : ℝ)),
            (t.choose j : ℝ) * ((-1 : ℝ) + (j : ℝ)) ^ (j - 1) *
              (b + (t - j : ℕ)) ^ (t - j - 1)) := rfl

/-- Ford's Section 4, Lemma 4.2, with its exact hypotheses, summation
range, positivity cut-off, and constant `exp 4`. -/
theorem lemma_four_two {t : ℕ} {a b : ℝ}
    (ht : 2 ≤ t) (hb : 0 ≤ b) (hab : 0 < (t : ℝ) + a + b) :
    fordLemmaFourTwoSum t a b ≤
      Real.exp 4 * ((t : ℝ) + a + b) ^ (t - 1) := by
  by_cases haLow : (1 : ℝ) - t < a
  · by_cases ha : -1 ≤ a
    · exact fordLemmaFourTwoSum_le_exp_four_of_neg_one_le ht ha hb
    · have ha' : a < -1 := lt_of_not_ge ha
      have hfactor := fordLemmaFourTwoSum_le_factor_of_lt_neg_one ht haLow ha' hb
      have hminus := fordLemmaFourTwoSum_le_exp_four_of_neg_one_le ht
        (a := (-1 : ℝ)) (b := b) (by norm_num) hb
      let R : ℝ := (((t : ℝ) + a) / (t - 1 : ℕ)) ^ (t - 1)
      let s0 : ℝ := (t : ℝ) - 1 + b
      let s : ℝ := (t : ℝ) + a + b
      let q : ℝ := (((t : ℝ) + a) / (t - 1 : ℕ)) * s0
      have ht1 : 0 < (t - 1 : ℕ) := by omega
      have hd : (0 : ℝ) < (t - 1 : ℕ) := by exact_mod_cast ht1
      have hta : 0 < (t : ℝ) + a := by linarith
      have hs0 : 0 < s0 := by
        dsimp [s0]
        have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
        linarith
      have hR : 0 ≤ R := by dsimp [R]; positivity
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hqs : q ≤ s := by
        have hcorr : (a + 1) * b ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hb
        dsimp [q, s0, s]
        rw [div_mul_eq_mul_div]
        rw [div_le_iff₀ hd]
        rw [Nat.cast_sub (by omega : 1 ≤ t)]
        push_cast
        nlinarith
      calc
        fordLemmaFourTwoSum t a b ≤ R * fordLemmaFourTwoSum t (-1) b := hfactor
        _ ≤ R * (Real.exp 4 * s0 ^ (t - 1)) := by
          apply mul_le_mul_of_nonneg_left _ hR
          simpa [s0, sub_eq_add_neg, add_assoc] using hminus
        _ = Real.exp 4 * q ^ (t - 1) := by
          dsimp [R, q]
          rw [mul_pow]
          ring
        _ ≤ Real.exp 4 * s ^ (t - 1) := by gcongr
        _ = Real.exp 4 * ((t : ℝ) + a + b) ^ (t - 1) := rfl
  · have haBound : a ≤ (1 : ℝ) - t := le_of_not_gt haLow
    have hempty :
        (Finset.Icc 1 (t - 1)).filter
          (fun j : ℕ ↦ 0 < a + (j : ℝ)) = ∅ := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hjIcc, hjpos⟩
        have hjtop : j ≤ t - 1 := (Finset.mem_Icc.mp hjIcc).2
        have hjt : (j : ℝ) ≤ (t : ℝ) - 1 := by
          have hcast : (j : ℝ) ≤ ((t - 1 : ℕ) : ℝ) := by exact_mod_cast hjtop
          rw [Nat.cast_sub (by omega : 1 ≤ t)] at hcast
          norm_num at hcast
          exact hcast
        exfalso
        linarith
      · intro hj
        simpa using hj
    rw [fordLemmaFourTwoSum, hempty]
    simp only [Finset.sum_empty]
    positivity

end Erdos896.Ford
