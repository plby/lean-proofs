/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 519.
https://www.erdosproblems.com/forum/thread/519

Informal authors:
- F. V. Atkinson

Formal authors:
- Aristotle
- John Jennings

URLs:
- https://www.erdosproblems.com/forum/thread/519#post-5599
- https://gist.githubusercontent.com/JohnEdwardJennings/db1e0cb00b7d6866193c12f1c70a1813/raw/e629fcf1976d5b241d628c0b65e2b1e3701f51a6/Erdos519.lean
-/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Jennings, Aristotle (Harmonic)
-/
import Mathlib

namespace Erdos519


/-!
# Erdős Problem 519: Turán's Power Sum Problem

Given complex numbers z₁, ..., zₙ with z₁ = 1 and |zᵢ| ≤ 1 for all i,
the maximum of |∑ᵢ zᵢᵏ| over 1 ≤ k ≤ n is greater than 1/6.

This was a problem posed by Turán, solved by Atkinson (1961).

Reference: F. V. Atkinson, "On sums of powers of complex numbers",
Acta Math. Acad. Sci. Hungar. 12 (1961), 185-188.

## Proof structure

The proof combines two ingredients:
1. **Numerical check**: The function f(s) = s²·exp(2πs)·(1 + exp(4s)/(1-4s))
   satisfies f(1/6) < 1.
2. **Atkinson's key inequality**: For any valid configuration with max|sₖ| ≤ s < 1/4,
   we have f(s) > 1.

Together: if max|sₖ| ≤ 1/6 < 1/4, then f(1/6) ≥ f(max|sₖ|) > 1,
contradicting f(1/6) < 1.

The numerical check is proved using bounds on exp and π.
The key inequality follows from Atkinson's Fourier-analytic argument
involving Cauchy-Schwarz, Parseval's identity, and integral estimates.
-/

open Finset Complex MeasureTheory

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
-- The generated analytic proof blocks need a larger heartbeat budget throughout.
set_option maxHeartbeats 10000000
-- Several generated complex-integral estimates time out at the default heartbeat limit.

private lemma two_pi_smul_I :
    (Real.pi * 2) • (I : ℂ) = I * (↑Real.pi * 2) := by
  norm_num [smul_eq_mul]
  ring

private lemma two_pi_smul_one :
    (Real.pi * 2) • (1 : ℂ) = (↑Real.pi : ℂ) * 2 := by
  norm_num [smul_eq_mul]

/-- The k-th power sum of a sequence of complex numbers. -/
noncomputable def powerSum {n : ℕ} (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ m : Fin n, z m ^ k

/-- The Atkinson function f(s) = s² · exp(2πs) · (1 + exp(4s)/(1-4s)).
The key inequality from Atkinson's proof states that if all power sums
are bounded by s < 1/4, then f(s) > 1. -/
noncomputable def atkinson_f (s : ℝ) : ℝ :=
  s ^ 2 * Real.exp (2 * Real.pi * s) * (1 + Real.exp (4 * s) / (1 - 4 * s))

/-! ## Auxiliary lemmas for numerical bounds -/

/-- For x < 1, exp(x) ≤ 1/(1-x), from the inequality 1-x ≤ exp(-x). -/
lemma exp_le_inv_one_sub (x : ℝ) (hx1 : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have h2 : 0 < 1 - x := by linarith
  have h1 : (1 - x) * Real.exp x ≤ 1 := by
    have : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    calc (1 - x) * Real.exp x
        ≤ Real.exp (-x) * Real.exp x := by nlinarith [Real.exp_pos x]
      _ = Real.exp ((-x) + x) := by rw [← Real.exp_add]
      _ = 1 := by simp
  rwa [le_div_iff₀ h2, mul_comm]

/-- exp(2) < 8, used to bound exp(2/3) < 2. -/
lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h2]; nlinarith [sq_nonneg (2.83 - Real.exp 1), Real.exp_pos 1]

/-- exp(2/3) < 2. Follows from exp(2) < 8 and cube root monotonicity. -/
lemma exp_two_thirds_lt_two : Real.exp (2 / 3 : ℝ) < 2 := by
  have h_cube : Real.exp (2 / 3 : ℝ) ^ 3 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [exp_two_lt_eight, sq_nonneg (2 - Real.exp (2 / 3 : ℝ)),
             sq_nonneg (Real.exp (2 / 3 : ℝ)),
             Real.exp_pos (2 / 3 : ℝ),
             sq_nonneg (Real.exp (2 / 3 : ℝ) + 2)]

/-- exp(3) < 21. -/
lemma exp_three_lt : Real.exp 3 < 21 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 : Real.exp 3 = Real.exp 2 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h3, h2]; nlinarith [sq_nonneg (2.72 - Real.exp 1), Real.exp_pos 1]

/-- exp(π) < 27, needed for exp(π/3) < 3. -/
lemma exp_pi_lt_27 : Real.exp Real.pi < 27 := by
  have h_split : Real.exp (3.15 : ℝ) = Real.exp 3 * Real.exp 0.15 := by
    rw [← Real.exp_add]; norm_num
  have h_exp015 : Real.exp (0.15 : ℝ) ≤ 20 / 17 := by
    have := exp_le_inv_one_sub 0.15 (by norm_num); linarith
  calc Real.exp Real.pi < Real.exp 3.15 := Real.exp_strictMono (by linarith [Real.pi_lt_d4])
    _ = Real.exp 3 * Real.exp 0.15 := h_split
    _ < 21 * (20 / 17) := by nlinarith [exp_three_lt, Real.exp_pos 3, Real.exp_pos (0.15 : ℝ)]
    _ < 27 := by norm_num

/-- exp(π/3) < 3. Follows from exp(π) < 27 and cube root monotonicity. -/
lemma exp_pi_div3_lt_three : Real.exp (Real.pi / 3) < 3 := by
  have h_cube : Real.exp (Real.pi / 3) ^ 3 = Real.exp Real.pi := by
    rw [← Real.exp_nat_mul]; ring_nf
  nlinarith [exp_pi_lt_27, sq_nonneg (3 - Real.exp (Real.pi / 3)),
             sq_nonneg (Real.exp (Real.pi / 3)),
             Real.exp_pos (Real.pi / 3),
             sq_nonneg (Real.exp (Real.pi / 3) + 3)]

/-! ## Key numerical check -/

/-- The Atkinson function evaluated at 1/6 is less than 1.
This uses exp(2/3) < 2 and exp(π/3) < 3 to get f(1/6) < 7/12 < 1. -/
lemma atkinson_f_sixth_lt_one : atkinson_f (1 / 6) < 1 := by
  unfold atkinson_f
  have h1 : Real.exp (2 / 3 : ℝ) < 2 := exp_two_thirds_lt_two
  have h2 : Real.exp (Real.pi / 3) < 3 := exp_pi_div3_lt_three
  have h3 : (2 : ℝ) * Real.pi * (1 / 6) = Real.pi / 3 := by ring
  rw [h3]
  have hp : 0 < Real.exp (Real.pi / 3) := Real.exp_pos _
  have he : 0 < Real.exp (2 / 3 : ℝ) := Real.exp_pos _
  have : (4 : ℝ) * (1 / 6) = 2 / 3 := by norm_num
  simp only [this]
  have : (1 : ℝ) - 2 / 3 = 1 / 3 := by norm_num
  rw [this]
  have hd : Real.exp (2 / 3 : ℝ) / (1 / 3 : ℝ) = 3 * Real.exp (2 / 3 : ℝ) := by ring
  rw [hd]
  nlinarith [sq_nonneg (Real.exp (Real.pi / 3)), sq_nonneg (Real.exp (2 / 3 : ℝ))]

/-! ## Atkinson's analytic argument

### Key functions

- **g(θ)** = -∑_{k=1}^n s_k · exp(ikθ) / k, a trigonometric polynomial
- **g'(θ)** = -i · ∑_{k=1}^n s_k · exp(ikθ), the derivative
- **h(θ)** = ∑_{m=n+1}^∞ exp(-imθ) / m, the tail of the logarithmic series

### Proof outline

From the generating function identity exp(-∑ s_k y^k/k) = ∏(1-z_r y)
and P(1) = 0 (since z₁ = 1), we derive:

1. **Identity**: ∫ g'(θ) · exp(g(θ)-g(0)) · h(θ) dθ = 2πi
2. **Cauchy-Schwarz**: (2π)² ≤ (∫|g'|²) · (∫|exp(g-g(0))·h|²)
3. **Parseval**: ∫|g'|² ≤ 2πns²
4. **Integral estimate**: ∫|exp(g-g(0))·h|² < (2π/n)·exp(2πs)·(1+exp(4s)/(1-4s))
5. **Combining**: 1 < s²·exp(2πs)·(1+exp(4s)/(1-4s)) = f(s)
-/

/-- The function g(θ) = -∑_{k=1}^n s_k · exp(ikθ) / k from Atkinson's proof. -/
noncomputable def g_fun {n : ℕ} (z : Fin n → ℂ) (θ : ℝ) : ℂ :=
  -∑ k : Fin n, (powerSum z (k.val + 1) / (↑(k.val + 1 : ℕ) : ℂ)) *
    Complex.exp ((↑(k.val + 1 : ℕ) : ℂ) * ↑θ * I)

/-- The derivative g'(θ) = -i · ∑_{k=1}^n s_k · exp(ikθ). -/
noncomputable def g_deriv_fun {n : ℕ} (z : Fin n → ℂ) (θ : ℝ) : ℂ :=
  -I * ∑ k : Fin n, (powerSum z (k.val + 1)) *
    Complex.exp ((↑(k.val + 1 : ℕ) : ℂ) * ↑θ * I)

/-- The function h(θ) = ∑_{m=n+1}^∞ exp(-imθ) / m, defined using the closed-form
expression -log(1-exp(-iθ)) - ∑_{k=1}^n exp(-ikθ)/k.

The series ∑ exp(-imθ)/m is only conditionally convergent, so we use the
closed form via Complex.log instead of tsum. At θ = 0, this gives a finite
(but mathematically meaningless) value; this doesn't affect integrals. -/
noncomputable def h_fun (n : ℕ) (θ : ℝ) : ℂ :=
  -Complex.log (1 - Complex.exp (-(↑θ : ℂ) * I)) -
    ∑ k ∈ Finset.range n, Complex.exp (-(↑(k + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(k + 1 : ℕ) : ℂ)

/-! ### Sub-lemmas for the integral identity -/

/-- The product polynomial P(y) = ∏(1-z_r·y). -/
noncomputable def P_poly {n : ℕ} (z : Fin n → ℂ) (y : ℂ) : ℂ :=
  ∏ r : Fin n, (1 - z r * y)

/-
P(1) = 0 when z₁ = 1, since the first factor (1 - z₁·1) = 0.
-/
lemma P_poly_one_eq_zero {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1) : P_poly z 1 = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hn⟩) (by aesop)

/-- The generating function G(y) = exp(-∑ s_k·y^k/k). -/
noncomputable def G_gen {n : ℕ} (z : Fin n → ℂ) (y : ℂ) : ℂ :=
  Complex.exp (-∑ k : Fin n, (powerSum z (k.val + 1) / (↑(k.val + 1 : ℕ) : ℂ)) * y ^ (k.val + 1))

/-
G(exp(iθ)) = exp(g(θ)).
-/
lemma G_gen_eq_exp_g {n : ℕ} (z : Fin n → ℂ) (θ : ℝ) :
    G_gen z (Complex.exp (↑θ * I)) = Complex.exp (g_fun z θ) := by
  unfold G_gen g_fun
  norm_num [ ← Complex.exp_nat_mul, mul_assoc ]

/-
G(1) = exp(g(0)).
-/
lemma G_gen_one {n : ℕ} (z : Fin n → ℂ) :
    G_gen z 1 = Complex.exp (g_fun z 0) := by
  unfold G_gen g_fun; aesop

/-
For |y| < 1 and |z_r| ≤ 1, the generating function G equals P times a
correction factor that is 1 + O(y^{n+1}). This is the factored form of
Newton's identity: G(y) = P(y) · exp(∑_r ∑_{k>n} (z_r·y)^k/k).

Proof: log(P(y)) = ∑_r log(1-z_r y) = -∑_{k≥1} s_k y^k / k.
So P(y) = exp(-∑_{k≥1} s_k y^k/k) and G(y) = exp(-∑_{k=1}^n s_k y^k/k).
Thus G(y)/P(y) = exp(∑_{k>n} s_k y^k/k).
-/
lemma G_eq_P_mul_correction {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (y : ℂ) (hy : ‖y‖ < 1) :
    G_gen z y = P_poly z y *
      Complex.exp (∑ r : Fin n,
        ∑' k, (z r * y) ^ (k + n + 1) / (↑(k + n + 1) : ℂ)) := by
  -- For each $r$, the series $\sum_{k \geq 1} \frac{(z_r y)^k}{k}$ converges absolutely.
  have h_converge (r : Fin n) : Summable (fun k : ℕ => (z r * y) ^ k / (k : ℂ)) := by
    -- Since ‖z r‖ ≤ 1 and ‖y‖ < 1, we have ‖z r * y‖ ≤ 1 * ‖y‖ = ‖y‖ < 1.
    have h_abs : ‖z r * y‖ < 1 := by
      simpa using lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hz r)) hy
    exact Summable.of_norm <| by
      simpa using Summable.of_nonneg_of_le
        (fun k => by positivity)
        (fun k => by
          cases k
          · simp
          · simpa using div_le_self (by positivity) (mod_cast Nat.le_add_left _ _))
        (summable_geometric_of_lt_one (by positivity) h_abs)
  -- For each $r$, the series $\sum_{k \geq 1} \frac{(z_r y)^k}{k}$ converges absolutely, so we can split it into two parts.
  have h_split (r : Fin n) : ∑' k : ℕ, (z r * y) ^ k / (k : ℂ) =
      (∑ k ∈ Finset.range (n + 1), (z r * y) ^ k / (k : ℂ))
        + ∑' k : ℕ, (z r * y) ^ (k + n + 1) / (k + n + 1 : ℂ) := by
    rw [ ← Summable.sum_add_tsum_nat_add ]
    exacts [ by congr; ext; push_cast; ring, h_converge r ]
  -- By definition of $P_poly$, we have $P_poly z y = \prod_{r=1}^n (1 - z_r y)$.
  have hP_poly : P_poly z y = Complex.exp (∑ r : Fin n, -∑' k : ℕ, (z r * y) ^ k / (k : ℂ)) := by
    have hP_poly : ∀ r : Fin n, (1 - z r * y) = Complex.exp (-∑' k : ℕ, (z r * y) ^ k / (k : ℂ))
        := by
      intro r
      have h_exp : Complex.exp (-∑' k : ℕ, (z r * y) ^ k / (k : ℂ)) = 1 - z r * y := by
        have h_exp_split (r :
            Fin n) : ∑' k : ℕ, (z r * y) ^ k / (k : ℂ) = -Complex.log (1 - z r * y) := by
          have h_exp_split (r :
              Fin n) : ∀ {w : ℂ}, ‖w‖ < 1 → ∑' k : ℕ, w ^ k / (k : ℂ) = -Complex.log (1 - w) := by
            intro w hw; have := Complex.hasSum_taylorSeries_neg_log hw; have := this.tsum_eq; aesop
          exact h_exp_split r (by simpa [ abs_mul ] using lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hz r)) hy)
        rw [ h_exp_split r, neg_neg, Complex.exp_log ]
        exact sub_ne_zero_of_ne <| ne_of_apply_ne Norm.norm <| by
          norm_num
          nlinarith [hz r, norm_nonneg (z r), norm_nonneg y]
      exact h_exp.symm
    unfold P_poly; simp +decide [ hP_poly]
    rw [ ← Complex.exp_sum, Finset.sum_neg_distrib ]
  simp_all +decide [ ← Complex.exp_add, Finset.sum_add_distrib ]
  unfold G_gen; simp +decide [← Finset.sum_comm, ← Finset.sum_div]
  simp +decide [Finset.sum_range, Fin.sum_univ_succ, mul_pow, div_eq_mul_inv, Finset.mul_sum _ _ _,
                mul_assoc, mul_comm, mul_left_comm, powerSum]

/-! ### Helper lemmas for newton_taylor_sum -/

/-
G_gen z is a differentiable (entire) function: it's exp of a polynomial.
-/
lemma G_gen_differentiable {n : ℕ} (z : Fin n → ℂ) : Differentiable ℂ (G_gen z) := by
  refine Differentiable.cexp (Differentiable.neg ?_)
  fun_prop

/-- The Lean polynomial corresponding to P_poly. -/
noncomputable def P_as_poly {n : ℕ} (z : Fin n → ℂ) : Polynomial ℂ :=
  ∏ r : Fin n, (Polynomial.C 1 - Polynomial.C (z r) * Polynomial.X)

/-
P_poly z y is the evaluation of P_as_poly z at y.
-/
lemma P_poly_eq_eval {n : ℕ} (z : Fin n → ℂ) (y : ℂ) :
    P_poly z y = (P_as_poly z).eval y := by
  simp +decide [ P_poly, P_as_poly, Polynomial.eval_prod ]

/-
P_as_poly has degree at most n.
-/
lemma P_as_poly_natDegree_le {n : ℕ} (z : Fin n → ℂ) :
    (P_as_poly z).natDegree ≤ n := by
  unfold P_as_poly
  let f : Fin n → Polynomial ℂ := fun r =>
    Polynomial.C 1 - Polynomial.C (z r) * Polynomial.X
  have hprod :
      (∏ r ∈ (Finset.univ : Finset (Fin n)), f r).natDegree ≤
        ∑ r ∈ (Finset.univ : Finset (Fin n)), (f r).natDegree :=
    Polynomial.natDegree_prod_le (Finset.univ : Finset (Fin n)) f
  have hfactor : ∀ r : Fin n, (f r).natDegree ≤ 1 := by
    intro r
    dsimp [f]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    refine max_le ?_ ?_
    · simp
    · exact le_trans Polynomial.natDegree_mul_le (by simp [Polynomial.natDegree_X])
  have hsum :
      ∑ r ∈ (Finset.univ : Finset (Fin n)), (f r).natDegree ≤ n := by
    calc
      ∑ r ∈ (Finset.univ : Finset (Fin n)), (f r).natDegree
          ≤ ∑ r ∈ (Finset.univ : Finset (Fin n)), 1 :=
            Finset.sum_le_sum fun r _ => hfactor r
      _ = n := by simp
  exact le_trans (by simpa [f] using hprod) hsum

/-
Circle integral of y^(k-m-1): extracts the m-th coefficient.
    ∮ y^{k} * y^{-(m+1)} dy = 2πi if k = m, 0 otherwise.
-/
lemma circleIntegral_zpow_coeff (k m : ℕ) :
    ∮ y in C(0, 1), ((y : ℂ) ^ k * (y ^ (m + 1))⁻¹) =
    if k = m then 2 * ↑Real.pi * Complex.I else 0 := by
  by_cases hkm : k = m
  · subst k
    rw [if_pos rfl]
    have h :=
      circleIntegral.integral_sub_inv_of_mem_ball
        (c := (0 : ℂ)) (w := 0) (R := 1) (by simp)
    convert h using 1
    exact circleIntegral.integral_congr (by norm_num)
      (fun y hy => by
        have hy0 : y ≠ 0 := by
          intro h0
          subst y
          norm_num at hy
        rw [sub_zero, pow_succ]
        field_simp [hy0])
  · simp only [if_neg hkm]
    have hne : ((k : ℤ) - ((m + 1 : ℕ) : ℤ)) ≠ -1 := by
      omega
    have h :=
      circleIntegral.integral_sub_zpow_of_ne
        (n := (k : ℤ) - ((m + 1 : ℕ) : ℤ)) hne (0 : ℂ) 0 1
    convert h using 1
    exact circleIntegral.integral_congr (by norm_num)
      (fun y hy => by
        have hy0 : y ≠ 0 := by
          intro h0
          subst y
          norm_num at hy
        rw [sub_zero]
        rw [zpow_sub₀ hy0, zpow_natCast, zpow_natCast, pow_succ]
        field_simp [hy0])

/-
For a polynomial p of degree ≤ n, the sum of circle-integral-extracted
    coefficients through degree n equals p.eval 1.
-/
lemma poly_circle_integral_sum_eq_eval_one {n : ℕ} (p : Polynomial ℂ)
    (hp : p.natDegree ≤ n) :
    ∑ m ∈ Finset.range (n + 1),
      (2 * ↑Real.pi * I)⁻¹ • ∮ y in C(0, 1), (y ^ (m + 1))⁻¹ • p.eval y =
    p.eval 1 := by
  -- By linearity of the circle integral, we can interchange the sum and integral.
  have h_linearity : ∀ m ∈ Finset.range (n + 1), (∮ y in C(0, 1), (y ^ (m + 1))⁻¹ • p.eval y) = (∑ k ∈ Finset.range (n + 1), p.coeff k • (∮ y in C(0, 1), (y ^ (m + 1))⁻¹ * y ^ k)) := by
    intro m hm
    simp +decide [ Polynomial.eval_eq_sum_range, circleIntegral ]
    simp +decide [mul_assoc, mul_left_comm, Finset.mul_sum _ _ _]
    rw [ intervalIntegral.integral_finsetSum ]
    · rw [Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hp)) fun x hx₁ hx₂ => by
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
        · simp
        · exact Nat.lt_of_not_ge fun hx => hx₂ (Finset.mem_range.mpr (Nat.lt_succ_of_le hx))]
      refine Finset.sum_congr rfl fun x hx => ?_
      calc
        ∫ (x_1 : ℝ) in 0..2 * Real.pi,
            I * (circleMap 0 1 x_1 *
              ((circleMap 0 1 x_1 ^ (m + 1))⁻¹ *
                (p.coeff x * circleMap 0 1 x_1 ^ x))) =
          ∫ θ in 0..2 * Real.pi,
            p.coeff x *
              (I * (circleMap 0 1 θ *
                ((circleMap 0 1 θ ^ (m + 1))⁻¹ *
                  circleMap 0 1 θ ^ x))) := by
            refine intervalIntegral.integral_congr fun θ hθ => ?_
            ring
        _ = p.coeff x *
              ∫ θ in 0..2 * Real.pi,
                I * (circleMap 0 1 θ *
                  ((circleMap 0 1 θ ^ (m + 1))⁻¹ *
                    circleMap 0 1 θ ^ x)) :=
            intervalIntegral.integral_const_mul
              (a := (0 : ℝ)) (b := 2 * Real.pi) (r := p.coeff x)
              (f := fun θ : ℝ =>
                I * (circleMap 0 1 θ *
                  ((circleMap 0 1 θ ^ (m + 1))⁻¹ *
                    circleMap 0 1 θ ^ x)))
        _ = p.coeff x *
              (I * ∫ θ in 0..2 * Real.pi,
                circleMap 0 1 θ *
                  ((circleMap 0 1 θ ^ (m + 1))⁻¹ *
                    circleMap 0 1 θ ^ x)) := by
            congr 1
            exact intervalIntegral.integral_const_mul
              (a := (0 : ℝ)) (b := 2 * Real.pi) (r := I)
              (f := fun θ : ℝ =>
                circleMap 0 1 θ *
                  ((circleMap 0 1 θ ^ (m + 1))⁻¹ *
                    circleMap 0 1 θ ^ x))
        _ = I *
              (p.coeff x * ∫ θ in 0..2 * Real.pi,
                circleMap 0 1 θ *
                  ((circleMap 0 1 θ ^ (m + 1))⁻¹ *
                    circleMap 0 1 θ ^ x)) := by
            ring
    · exact fun _ _ => Continuous.intervalIntegrable (by exact Continuous.mul continuous_const <| by exact Continuous.mul (by continuity) <| by exact Continuous.mul (by exact Continuous.inv₀ (by continuity) fun x => by norm_num [ Complex.exp_ne_zero ]) <| by continuity) _ _
  rw [ Finset.sum_congr rfl fun m hm => by rw [ h_linearity m hm ] ]
  rw [ Finset.sum_congr rfl fun m hm => by rw [ Finset.smul_sum ] ]
  rw [ Finset.sum_comm ]
  rw [ Finset.sum_congr rfl fun i hi => Finset.sum_eq_single i _ _ ] <;> norm_num
  · rw [ Polynomial.eval_eq_sum_range' ]
    any_goals exact Nat.lt_succ_of_le hp
    rw [ ← Finset.sum_neg_distrib ]; refine Finset.sum_congr rfl fun i hi => ?_; rw [ show (∮ y in C(0, 1), (y ^ (i + 1)) ⁻¹ * y ^ i) = 2 * Real.pi * Complex.I by simpa [ mul_assoc, mul_comm, mul_left_comm ] using circleIntegral_zpow_coeff i i ]; ring_nf; norm_num [ Real.pi_ne_zero ]
  · intro i hi j hj hij; have := circleIntegral_zpow_coeff i j; simp_all +decide [ mul_comm ]
    tauto
  · intros; linarith

/-
For any f that is ContDiffAt, y^(n+1) * f(y) has iteratedDeriv k = 0 at 0 for k ≤ n.
-/
lemma iteratedDeriv_pow_mul_zero {n : ℕ} {f : ℂ → ℂ}
    (hf : ContDiffAt ℂ n f 0) (k : ℕ) (hk : k ≤ n) :
    iteratedDeriv k (fun y => y ^ (n + 1) * f y) 0 = 0 := by
  -- By the Leibniz rule, the k-th derivative of $y^{n+1} * f(y)$ at $0$ is the sum of the k-th derivatives of $y^{n+1}$ and $f(y)$.
  have h_leibniz : iteratedDeriv k (fun y : ℂ => y ^ (n + 1) * f y) 0 = ∑ j ∈ Finset.range (k + 1), Nat.choose k j * iteratedDeriv j (fun y : ℂ => y ^ (n + 1)) 0 * iteratedDeriv (k - j) f 0 := by
    exact iteratedDeriv_mul (contDiffAt_id.pow _) (hf.of_le <| mod_cast hk)
  simp_all +decide [ iteratedDeriv_eq_iterate ]
  exact Finset.sum_eq_zero fun x hx => by rw [ zero_pow (Nat.sub_ne_zero_of_lt (by linarith [ Finset.mem_range.mp hx ])) ]; ring

/-
The correction sum factors as y^(n+1) * g(y) for an analytic g.
-/
lemma correction_sum_eq_pow_mul {n : ℕ} (z : Fin n → ℂ) (_hz : ∀ i, ‖z i‖ ≤ 1) (y : ℂ) :
    (∑ r : Fin n, ∑' j, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ)) =
    y ^ (n + 1) * (∑ r : Fin n, ∑' j, z r ^ (j + n + 1) / (↑(j + n + 1) : ℂ) * y ^ j) := by
  simp +decide [mul_pow, mul_comm, div_eq_mul_inv, Finset.mul_sum _ _ _]
  exact Finset.sum_congr rfl fun _ _ => by rw [ ← tsum_mul_left ]; exact tsum_congr fun _ => by ring

/-
The function g(y) = ∑ r ∑' j z_r^(j+n+1)/(j+n+1) * y^j is analytic at 0.
-/
lemma correction_g_analyticAt {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    AnalyticAt ℂ (fun y => ∑ r : Fin n, ∑' j, z r ^ (j + n + 1) / (↑(j + n + 1) : ℂ) * y ^ j) 0 := by
  -- Show that each inner sum is analytic.
  have h_inner_analytic (r :
      Fin n) : AnalyticAt ℂ (fun y : ℂ => ∑' j, z r ^ (j + n + 1) / (j + n + 1) * y ^ j) 0 := by
    refine (show HasFPowerSeriesAt
      (fun y : ℂ => ∑' j, z r ^ (j + n + 1) / (j + n + 1) * y ^ j)
      (FormalMultilinearSeries.ofScalars ℂ fun j => (z r ^ (j + n + 1) / (j + n + 1)))
      0 from ?_).analyticAt
    rw [ hasFPowerSeriesAt_iff ]
    filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with x hx
    simp +decide [ mul_comm ]
    refine Summable.hasSum ?_
    refine .of_norm ?_
    norm_num at *
    exact Summable.of_nonneg_of_le (fun _ => by positivity) (fun _ => mul_le_of_le_one_right (by positivity) <| div_le_one_of_le₀ (by exact le_trans (pow_le_one₀ (by positivity) <| hz _) <| mod_cast by linarith) <| by positivity) <| summable_geometric_of_lt_one (by positivity) hx
  simp +zetaDelta at *
  exact Finset.analyticAt_fun_sum _ fun r _ => h_inner_analytic r

/-
exp(y^(n+1) * g(y)) - 1 = y^(n+1) * F(y) near 0, for ContDiffAt F.
-/
lemma exp_pow_mul_sub_one_factors {n : ℕ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    ∃ F : ℂ → ℂ, ContDiffAt ℂ n F 0 ∧
    (∀ᶠ y in nhds (0 : ℂ), Complex.exp (y ^ (n + 1) * g y) - 1 = y ^ (n + 1) * F y) := by
  -- Let $\psi(t) = \frac{\exp(t) - 1}{t}$ for $t \neq 0$ and $\psi(0) = 1$.
  set ψ : ℂ → ℂ := fun t => if t = 0 then 1 else (Complex.exp t - 1) / t
  refine ⟨fun y => ψ (y ^ (n + 1) * g y) * g y, ?_, ?_⟩
  · -- We need to show that $\psi$ is analytic at $0$.
    have h_psi_analytic : AnalyticAt ℂ ψ 0 := by
      -- We'll use the fact that ψ(t) is the sum of a power series converging everywhere.
      have h_psi_series : ∀ t : ℂ, ψ t = ∑' k : ℕ, t ^ k / Nat.factorial (k + 1) := by
        intro t; by_cases ht : t = 0 <;> simp +decide [ht, ψ, Complex.exp_eq_exp_ℂ,
                                                       NormedSpace.exp_eq_tsum_div]
        · rw [ tsum_eq_single 0 ] <;> aesop
        · rw [ Summable.tsum_eq_zero_add ]
          · simp +decide [ht, pow_succ', div_eq_mul_inv, mul_assoc, mul_comm, tsum_mul_left]
          · exact Summable.of_norm <| by
              simpa [Complex.normSq_eq_norm_sq] using
                Real.summable_pow_div_factorial ‖t‖
      refine (show HasFPowerSeriesAt ψ
        (FormalMultilinearSeries.ofScalars ℂ fun k => ((k + 1).factorial : ℂ) ⁻¹)
        0 from ?_).analyticAt
      rw [ hasFPowerSeriesAt_iff ]
      filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with t ht
      convert Summable.hasSum _ using 1
      · aesop
      · exact Summable.of_norm <| by
          refine Summable.of_nonneg_of_le (fun n => by positivity) ?_
            (summable_geometric_of_lt_one (by positivity) <|
              show ‖t‖ < 1 from by simpa using ht)
          intro n
          simpa [div_eq_mul_inv] using
            div_le_self (pow_nonneg (norm_nonneg t) n)
              (show (1 : ℝ) ≤ (n + 1).factorial by
                exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (n + 1)))
    refine ContDiffAt.mul ?_ ?_
    · have h_cont_diff : ContDiffAt ℂ (↑n) (fun y => ψ y) (0 ^ (n + 1) * g 0) := by
        simpa using h_psi_analytic.contDiffAt
      exact h_cont_diff.comp 0 (ContDiffAt.mul (contDiffAt_id.pow _) (hg.contDiffAt))
    · exact hg.contDiffAt
  · filter_upwards [ ] with y; by_cases hy : y ^ (n + 1) * g y = 0 <;> simp +decide [ hy, mul_assoc, mul_comm, mul_left_comm ]
    · aesop
    · grind

/-
exp(correction) has iteratedDeriv k at 0 equal to 0 for 1 ≤ k ≤ n,
    and iteratedDeriv 0 at 0 equal to 1.
-/
lemma exp_correction_iteratedDeriv {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (k : ℕ) (hk : k ≤ n) :
    iteratedDeriv k
      (fun y => Complex.exp (∑ r : Fin n, ∑' j, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ))) 0 =
    if k = 0 then 1 else 0 := by
  obtain ⟨F, hF_cont, hF_eq⟩ : ∃ F : ℂ → ℂ, ContDiffAt ℂ n F 0 ∧ (∀ᶠ y in nhds (0 : ℂ), Complex.exp (∑ r : Fin n, ∑' j, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ)) - 1 = y ^ (n + 1) * F y) := by
    convert exp_pow_mul_sub_one_factors (correction_g_analyticAt z hz) using 1
    convert rfl
    expose_names; exact Eq.symm (correction_sum_eq_pow_mul z hz _)
  -- By Filter.EventuallyEq.iteratedDeriv_eq, iteratedDeriv k (exp∘h) 0 = iteratedDeriv k (fun y => 1 + y^(n+1)*F(y)) 0.
  have h_iter_eq : iteratedDeriv k (fun y => Complex.exp (∑ r : Fin n, ∑' j, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ))) 0 = iteratedDeriv k (fun y => 1 + y ^ (n + 1) * F y) 0 := by
    rw [ Filter.EventuallyEq.iteratedDeriv_eq ]
    filter_upwards [ hF_eq ] with y hy using by linear_combination' hy
  rw [ h_iter_eq, iteratedDeriv_eq_iterate ]
  -- By iteratedDeriv_pow_mul_zero, the k-th derivative of y^(n+1) * F(y) at 0 is 0.
  have h_iter_zero : deriv^[k] (fun y => y ^ (n + 1) * F y) 0 = 0 := by
    have := @iteratedDeriv_pow_mul_zero
    simpa only [ iteratedDeriv_eq_iterate ] using this hF_cont k hk
  induction k with
  | zero => simp_all +decide []
  | succ k ih => simp_all +decide []

/-
G and P have the same iterated derivatives at 0 through degree n.
-/
lemma G_iteratedDeriv_eq_P {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (m : ℕ) (hm : m ≤ n) :
    iteratedDeriv m (G_gen z) 0 = iteratedDeriv m (fun y => P_poly z y) 0 := by
  -- By definition of $G_gen$, we know that $G_gen z y = P_poly z y * exp(correction(y))$ for $|y| < 1$.
  have h_eq : ∀ᶠ y in nhds 0, G_gen z y = P_poly z y * Complex.exp (∑ r : Fin n, ∑' j, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ)) := by
    filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with y hy using G_eq_P_mul_correction z hz y <| by simpa using hy
  have h_cont_diff : ContDiffAt ℂ n (fun y => P_poly z y) 0 ∧ ContDiffAt ℂ n (fun y => Complex.exp (∑ r : Fin n, ∑' j, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ))) 0 := by
    constructor
    · norm_num [ P_poly_eq_eval ]
      exact ContDiffAt.congr_of_eventuallyEq (show ContDiffAt ℂ n (fun y => ∑ i ∈ Finset.range (Polynomial.natDegree (P_as_poly z) + 1), Polynomial.coeff (P_as_poly z) i * y ^ i) 0 from ContDiffAt.sum fun i hi => ContDiffAt.mul (contDiffAt_const) (contDiffAt_id.pow i)) (Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds _ zero_lt_one) fun x hx => by simp +decide [ Polynomial.eval_eq_sum_range ])
    · refine ContDiffAt.cexp ?_
      -- The sum of analytic functions is analytic.
      have h_analytic : ∀ r : Fin n, AnalyticAt ℂ (fun y => ∑' j : ℕ, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ)) 0 := by
        intro r
        have h_exp_analytic : HasFPowerSeriesAt (fun y => ∑' j : ℕ, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ)) (FormalMultilinearSeries.ofScalars ℂ (fun j => if j < n + 1 then 0 else (z r) ^ j / (↑j : ℂ))) 0 := by
          rw [ hasFPowerSeriesAt_iff ]
          filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with y hy
          convert Summable.hasSum _ using 1
          · rw [ eq_comm, ← Summable.sum_add_tsum_nat_add n.succ ]
            · rw [ Finset.sum_eq_zero ] <;> norm_num
              · exact tsum_congr fun i => by rw [ if_neg (by linarith) ]; ring
              · bv_omega
            · rw [ ← summable_nat_add_iff (n + 1) ]
              simp +decide []
              refine Summable.of_norm ?_
              refine Summable.of_nonneg_of_le (fun a => by positivity) (fun a => ?_) (summable_nat_add_iff (n + 1) |>.2 <| summable_geometric_of_lt_one (by positivity) <| show ‖y‖ < 1 from by simpa using hy)
              split_ifs <;> norm_num
              exact mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ (le_trans (pow_le_one₀ (by positivity) (hz r)) (by norm_cast; linarith)) (by positivity))
          · rw [ ← summable_nat_add_iff (n + 1) ]
            simp +decide []
            refine Summable.of_norm ?_
            refine Summable.of_nonneg_of_le (fun a => by positivity) (fun a => ?_) (summable_nat_add_iff (n + 1) |>.2 <| summable_geometric_of_lt_one (by positivity) <| show ‖y‖ < 1 from by simpa using hy)
            split_ifs <;> norm_num
            exact mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ (le_trans (pow_le_one₀ (by positivity) (hz r)) (by norm_cast; linarith)) (by positivity))
        exact h_exp_analytic.analyticAt
      exact ContDiffAt.sum fun r _ => (h_analytic r |> AnalyticAt.contDiffAt)
  have h_iterated_deriv : iteratedDeriv m (fun y => P_poly z y * Complex.exp (∑ r : Fin n, ∑' j, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ))) 0 = ∑ j ∈ Finset.range (m + 1), Nat.choose m j * iteratedDeriv j (fun y => P_poly z y) 0 * iteratedDeriv (m - j) (fun y => Complex.exp (∑ r : Fin n, ∑' j, (z r * y) ^ (j + n + 1) / (↑(j + n + 1) : ℂ))) 0 := by
    have := @iteratedDeriv_mul
    exact this (h_cont_diff.1.of_le (mod_cast hm)) (h_cont_diff.2.of_le (mod_cast hm))
  convert h_iterated_deriv using 1
  · rw [ Filter.EventuallyEq.iteratedDeriv_eq ]
    exact h_eq
  · rw [ Finset.sum_eq_single m ] <;> norm_num
    intro k hk₁ hk₂; right; exact (by
    convert exp_correction_iteratedDeriv z hz (m - k) (Nat.sub_le_of_le_add <| by linarith) using 1
    focus
      norm_cast
    rw [ if_neg (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hk₁ hk₂)) ])

/-
For m ≤ n, the circle integrals of G_gen and P_poly agree.
    This follows from G_eq_P_mul_correction: G and P agree through degree n.
    Uses cauchyPowerSeries and the connection to iteratedDeriv.
-/
lemma circle_integral_G_eq_P {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (m : ℕ) (hm : m ≤ n) :
    (2 * ↑Real.pi * I)⁻¹ • ∮ y in C(0, 1), (y ^ (m + 1))⁻¹ • G_gen z y =
    (2 * ↑Real.pi * I)⁻¹ • ∮ y in C(0, 1), (y ^ (m + 1))⁻¹ • P_poly z y := by
  -- By the uniqueness of the power series coefficients, we can equate them.
  have h_coeff : (cauchyPowerSeries (G_gen z) 0 1).coeff m = (cauchyPowerSeries (fun y => P_poly z y) 0 1).coeff m := by
    have h_unique : ∀ f : ℂ → ℂ, Differentiable ℂ f → ∀ m, (cauchyPowerSeries f 0 1).coeff m = iteratedDeriv m f 0 / (Nat.factorial m) := by
      intro f hf m; rw [ iteratedDeriv_eq_iterate ]
      have := @Differentiable.hasFPowerSeriesOnBall ℂ
      specialize this hf 0 zero_lt_one
      have := this.hasFPowerSeriesAt
      rw [ eq_div_iff (Nat.cast_ne_zero.mpr <| Nat.factorial_ne_zero m) ]
      have := this.analyticAt
      have := this.hasFPowerSeriesAt
      have := this.eq_formalMultilinearSeries ‹HasFPowerSeriesAt f (cauchyPowerSeries f 0 1) 0›
      replace this := congr_arg (fun p => p.coeff m) this; simp_all +decide []
      rw [← this, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr <| Nat.factorial_ne_zero m),
          iteratedDeriv_eq_iterate]
    rw [ h_unique _ (G_gen_differentiable _), h_unique _ (show Differentiable ℂ (fun y => P_poly z y) from by
                                                              exact fun y => DifferentiableAt.congr_of_eventuallyEq (show DifferentiableAt ℂ (fun y => (P_as_poly z |> Polynomial.eval y)) y from by exact (P_as_poly z |> Polynomial.differentiable) |> Differentiable.differentiableAt) (Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds _ zero_lt_one) fun x hx => by simp +decide [ P_poly_eq_eval ])), G_iteratedDeriv_eq_P _ hz _ hm ]
  simpa [cauchyPowerSeries_apply, FormalMultilinearSeries.coeff, cauchyPowerSeries,
    circleIntegral, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_succ] using h_coeff

/-- Newton's identity: the first n+1 Taylor coefficients of G sum to P(1).
Equivalently, ∑_{m=0}^n G^(m)(0)/m! = P(1).
This follows from the fact that G and P agree as formal power series through
degree n, which in turn follows from log(∏(1-z_r y)) = -∑ s_k y^k/k. -/
lemma newton_taylor_sum {n : ℕ} (_hn : 0 < n) (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∑ m ∈ Finset.range (n + 1),
      (2 * ↑Real.pi * I)⁻¹ • ∮ y in C(0, 1), (y ^ (m + 1))⁻¹ • G_gen z y =
    P_poly z 1 := by
  -- Step 1: Replace each G_gen integral with P_poly integral
  have h_eq : ∀ m ∈ Finset.range (n + 1),
      (2 * ↑Real.pi * I)⁻¹ • ∮ y in C(0, 1), (y ^ (m + 1))⁻¹ • G_gen z y =
      (2 * ↑Real.pi * I)⁻¹ • ∮ y in C(0, 1), (y ^ (m + 1))⁻¹ • P_poly z y := by
    intro m hm
    exact circle_integral_G_eq_P z hz m (by simp [Finset.mem_range] at hm; omega)
  rw [Finset.sum_congr rfl h_eq]
  -- Step 2: Rewrite P_poly as polynomial eval
  have h_eval : ∀ y, P_poly z y = (P_as_poly z).eval y := P_poly_eq_eval z
  simp_rw [h_eval]
  -- Step 3: Apply the polynomial circle integral sum lemma
  exact poly_circle_integral_sum_eq_eval_one (P_as_poly z) (P_as_poly_natDegree_le z)

/-! ### Regularized version of h and the Abel regularization proof

The core identity ∫ g'·exp(g)·h = 2πi·exp(g(0)) is proved by Abel regularization:
1. Define h_r(θ) with parameter r < 1, which equals h(θ) when r = 1.
2. Prove the identity for h_r using integration by parts + Cauchy's integral formula.
3. Take r → 1⁻ using dominated convergence.
-/

/-- The regularized h function: h_r(θ) = -log(1 - r·exp(-iθ)) - ∑_{k=1}^n r^(k+1)·exp(-ikθ)/k.
For r < 1, this equals ∑_{k>n} r^k·exp(-ikθ)/k (absolutely convergent).
For r = 1, this reduces to h_fun n θ. -/
noncomputable def h_fun_reg (n : ℕ) (r : ℝ) (θ : ℝ) : ℂ :=
  -Complex.log (1 - (r : ℂ) * Complex.exp (-(↑θ : ℂ) * I)) -
    ∑ k ∈ Finset.range n, (r : ℂ) ^ (k + 1) *
      Complex.exp (-(↑(k + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(k + 1 : ℕ) : ℂ)
/-! ### Helper lemmas for the regularized integral identity -/

/-
The series ∑_{k≥1} (r exp(-iθ))^k / k converges and sums to -log(1 - r exp(-iθ))
for r < 1. This is `Complex.hasSum_taylorSeries_neg_log` applied to w = r exp(-iθ).
-/
lemma neg_log_hasSum (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    HasSum (fun k : ℕ => ((↑r : ℂ) * Complex.exp (-(↑θ : ℂ) * I)) ^ (k + 1) / (↑(k + 1) : ℂ))
      (-Complex.log (1 - (↑r : ℂ) * Complex.exp (-(↑θ : ℂ) * I))) := by
  have norm_lt_1 : ‖(r : ℂ) * Complex.exp (-(θ : ℂ) * I)‖ < 1 := by
    simpa [ Complex.norm_exp, abs_of_pos hr ] using hr1
  let w : ℂ := (r : ℂ) * Complex.exp (-(θ : ℂ) * I)
  have hzero : (∑ i ∈ Finset.range 1, w ^ i / (i : ℂ)) = 0 := by simp [w]
  simpa [w, hzero, Nat.cast_add, Nat.cast_one] using
    ((hasSum_nat_add_iff' 1).2
      (Complex.hasSum_taylorSeries_neg_log (z := w) (by simpa [w] using norm_lt_1)))

/-
h_fun_reg equals the tail of the series -log(1-w) for w = r exp(-iθ).
    h_fun_reg n r θ = ∑' k, r^{k+n+1} exp(-i(k+n+1)θ) / (k+n+1)
-/
lemma h_fun_reg_eq_tsum (n : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    h_fun_reg n r θ = ∑' k : ℕ, ((↑r : ℂ) * Complex.exp (-(↑θ : ℂ) * I)) ^ (k + n + 1) /
      (↑(k + n + 1) : ℂ) := by
  let w : ℂ := (r : ℂ) * Complex.exp (-(θ : ℂ) * I)
  have htail := (hasSum_nat_add_iff' n).2 (neg_log_hasSum r hr hr1 θ)
  rw [htail.tsum_eq]
  unfold h_fun_reg
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp [mul_pow, ← Complex.exp_nat_mul]
  ring_nf

/-
g_fun is 2π-periodic.
-/
lemma g_fun_periodic {n : ℕ} (z : Fin n → ℂ) :
    Function.Periodic (g_fun z) (2 * Real.pi) := by
  unfold g_fun
  norm_num [ Complex.exp_add, mul_add, add_mul ]
  norm_num [show ∀ k : ℕ,
            cexp (k * (2 * Real.pi) * I) = 1 by intro k; rw [ Complex.exp_eq_one_iff ]; use k; push_cast; ring]

/-
exp(g_fun z θ) has the derivative g_deriv_fun z θ * exp(g_fun z θ).
-/
lemma exp_g_fun_hasDerivAt {n : ℕ} (z : Fin n → ℂ) (θ : ℝ) :
    HasDerivAt (fun t => Complex.exp (g_fun z t))
      (g_deriv_fun z θ * Complex.exp (g_fun z θ)) θ := by
  have hg : HasDerivAt (g_fun z) (g_deriv_fun z θ) θ := by
    unfold g_fun g_deriv_fun
    let F : ℝ → ℂ := fun t =>
      ∑ k : Fin n, (powerSum z (k.val + 1) / (↑(k.val + 1 : ℕ) : ℂ)) *
        Complex.exp ((↑(k.val + 1 : ℕ) : ℂ) * ↑t * I)
    let D : ℂ :=
      ∑ k : Fin n,
        (powerSum z (k.val + 1) / (↑(k.val + 1 : ℕ) : ℂ)) *
          (((↑(k.val + 1 : ℕ) : ℂ) * I) *
            Complex.exp ((↑(k.val + 1 : ℕ) : ℂ) * ↑θ * I))
    have hsum : HasDerivAt F D θ := by
      dsimp [F, D]
      refine HasDerivAt.fun_sum fun k _ => ?_
      set c : ℂ := (↑(k.val + 1 : ℕ) : ℂ)
      set a : ℂ := powerSum z (k.val + 1) / c
      have hlin : HasDerivAt (fun t : ℝ => c * ↑t * I) (c * I) θ := by
        simpa [mul_assoc] using
          ((((hasDerivAt_id θ).ofReal_comp).const_mul c).mul_const I)
      simpa [a, c, mul_assoc, mul_comm, mul_left_comm] using
        ((Complex.hasDerivAt_exp _).comp θ hlin |>.const_mul a)
    have hD :
        -D =
          -I * ∑ k : Fin n, (powerSum z (k.val + 1)) *
            Complex.exp ((↑(k.val + 1 : ℕ) : ℂ) * ↑θ * I) := by
      dsimp [D]
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk0 : ((↑(k.val + 1 : ℕ) : ℂ) ≠ 0) := by
        exact_mod_cast Nat.succ_ne_zero k.val
      field_simp [hk0]
    change HasDerivAt (-F)
      (-I * ∑ k : Fin n, (powerSum z (k.val + 1)) *
        Complex.exp ((↑(k.val + 1 : ℕ) : ℂ) * ↑θ * I)) θ
    rw [← hD]
    exact hsum.neg
  simpa [mul_comm] using hg.cexp

/-
Integration by parts for a single Fourier mode:
    ∫_{-π}^{π} g'exp(g) exp(-imθ) dθ = im ∫_{-π}^{π} exp(g) exp(-imθ) dθ.
    The boundary term vanishes because exp(g) is 2π-periodic and
    sin(mπ) = 0 for integer m.
-/
lemma ibp_fourier_mode {n : ℕ} (z : Fin n → ℂ) (m : ℕ) (_hm : 0 < m) :
    ∫ θ in (-Real.pi)..Real.pi,
      g_deriv_fun z θ * Complex.exp (g_fun z θ) *
        Complex.exp (-(↑m : ℂ) * ↑θ * I) =
    I * (↑m : ℂ) * ∫ θ in (-Real.pi)..Real.pi,
      Complex.exp (g_fun z θ) * Complex.exp (-(↑m : ℂ) * ↑θ * I) := by
  -- Set u(θ) = exp(g_fun z θ), u'(θ) = g_deriv_fun z θ * exp(g_fun z θ) (from exp_g_fun_hasDerivAt),
  set u := fun θ : ℝ => Complex.exp (g_fun z θ)
  set u' := fun θ : ℝ => g_deriv_fun z θ * Complex.exp (g_fun z θ)
  set v := fun θ : ℝ => Complex.exp (-(m : ℂ) * θ * I)
  set v' := fun θ : ℝ => -m * Complex.I * Complex.exp (-(m : ℂ) * θ * I)
  -- Apply the integration by parts formula.
  have h_parts :
      ∀ a b : ℝ, ∫ θ in a..b, u' θ * v θ = (u b * v b - u a * v a) - ∫ θ in a..b, u θ * v' θ := by
    intros a b; rw [ eq_sub_iff_add_eq ]; rw [ ← intervalIntegral.integral_add ]
    focus
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ]
      · intro x hx
        have hu : HasDerivAt u (u' x) x := by
          dsimp [u, u']
          exact exp_g_fun_hasDerivAt z x
        have hv : HasDerivAt v (v' x) x := by
          dsimp [v, v']
          have hlin :
              HasDerivAt (fun y : ℝ => (-(m : ℂ)) * ↑y * I) (-(m : ℂ) * I) x := by
            simpa [mul_assoc] using
              ((((hasDerivAt_id x).ofReal_comp).const_mul (-(m : ℂ))).mul_const I)
          simpa [mul_assoc, mul_comm, mul_left_comm] using hlin.cexp
        exact hu.mul hv
    · apply_rules [ Continuous.intervalIntegrable ]
      apply_rules [ Continuous.add, Continuous.mul, continuous_const, Complex.continuous_exp.comp ]
      · fun_prop
      · exact Continuous.neg <| continuous_finsetSum _ fun _ _ => Continuous.mul (continuous_const) <| Complex.continuous_exp.comp <| by continuity
      · exact Complex.continuous_ofReal
      · exact Continuous.neg <| continuous_finsetSum _ fun _ _ => Continuous.mul (continuous_const) <| Complex.continuous_exp.comp <| by continuity
      · exact Complex.continuous_ofReal
    · apply_rules [ Continuous.intervalIntegrable ]
      apply_rules [Continuous.mul, Continuous.neg, Continuous.add, continuous_const,
                   Complex.continuous_exp]
      · fun_prop
      · exact Complex.continuous_exp.comp <| by unfold g_fun; continuity
      · continuity
    · apply_rules [ Continuous.intervalIntegrable ]
      refine Continuous.mul ?_ ?_
      · refine Complex.continuous_exp.comp ?_
        exact continuous_neg.comp <| continuous_finsetSum _ fun _ _ => Continuous.mul (continuous_const) <| Complex.continuous_exp.comp <| by continuity
      · fun_prop
  -- Since $u$ is $2\pi$-periodic, we have $u(\pi) = u(-\pi)$.
  have h_periodic : u Real.pi = u (-Real.pi) := by
    have h_periodic : ∀ θ : ℝ, u (θ + 2 * Real.pi) = u θ := by
      exact fun θ => congr_arg Complex.exp (g_fun_periodic z θ)
    convert h_periodic (-Real.pi) using 1; ring_nf
  simp +zetaDelta at *
  have h_exp_boundary :
      Complex.exp (-(I * (↑Real.pi * ↑m))) =
        Complex.exp (I * (↑Real.pi * ↑m)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-m, ?_⟩
    push_cast
    ring
  rw [h_parts]
  simp [h_periodic, h_exp_boundary, mul_assoc, mul_comm, mul_left_comm]
  calc
    ∫ (x : ℝ) in -Real.pi..Real.pi,
        Complex.exp (g_fun z x) *
          ((↑m : ℂ) * Complex.exp (-(I * (↑x * ↑m)))) =
      ∫ (x : ℝ) in -Real.pi..Real.pi,
        (↑m : ℂ) *
          (Complex.exp (g_fun z x) * Complex.exp (-(I * (↑x * ↑m)))) := by
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        ring
    _ = (↑m : ℂ) *
        ∫ (θ : ℝ) in -Real.pi..Real.pi,
          Complex.exp (g_fun z θ) * Complex.exp (-(I * (↑θ * ↑m))) :=
        intervalIntegral.integral_const_mul
          (a := -Real.pi) (b := Real.pi) (r := (↑m : ℂ))
          (f := fun θ : ℝ =>
            Complex.exp (g_fun z θ) * Complex.exp (-(I * (↑θ * ↑m))))

/-
Connection between the θ-integral and the circle integral:
    ∫_{-π}^{π} exp(g(θ)) exp(-imθ) dθ = -I · ∮_{C(0,1)} G(w)/w^{m+1} dw.
    This uses the substitution w = exp(iθ) and periodicity to shift [0,2π] to [-π,π].
-/
lemma interval_integral_eq_circle {n : ℕ} (z : Fin n → ℂ) (m : ℕ) :
    ∫ θ in (-Real.pi)..Real.pi,
      Complex.exp (g_fun z θ) * Complex.exp (-(↑m : ℂ) * ↑θ * I) =
    -I * ∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w := by
  -- By definition of $circleIntegral$, we have:
  have h_circle : (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w) = ∫ θ in (0 : ℝ)..2 * Real.pi, (Complex.exp (θ * I) ^ (m + 1))⁻¹ • G_gen z (Complex.exp (θ * I)) * Complex.I * Complex.exp (θ * I) := by
    rw [ circleIntegral ]
    norm_num [ mul_assoc, mul_comm, mul_left_comm, circleMap ]
  -- Using the periodicity of the integrand, we can shift the interval of integration.
  have h_periodic : ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (g_fun z θ) * Complex.exp (-(m : ℂ) * θ * I) = ∫ θ in (-Real.pi)..Real.pi, Complex.exp (g_fun z θ) * Complex.exp (-(m : ℂ) * θ * I) := by
    have h_periodic : ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (g_fun z θ) * Complex.exp (-(m : ℂ) * θ * I) = (∫ θ in (0 : ℝ)..Real.pi, Complex.exp (g_fun z θ) * Complex.exp (-(m : ℂ) * θ * I)) + (∫ θ in (Real.pi)..2 * Real.pi, Complex.exp (g_fun z θ) * Complex.exp (-(m : ℂ) * θ * I)) := by
      rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Continuous.intervalIntegrable ]
      · refine Continuous.mul ?_ ?_
        · refine Complex.continuous_exp.comp ?_
          exact continuous_neg.comp <| continuous_finsetSum _ fun _ _ => Continuous.mul (continuous_const) <| Complex.continuous_exp.comp <| by continuity
        · continuity
      · refine Continuous.mul ?_ ?_
        · refine Complex.continuous_exp.comp ?_
          exact continuous_neg.comp <| continuous_finsetSum _ fun _ _ => Continuous.mul (continuous_const) <| Complex.continuous_exp.comp <| by continuity
        · continuity
    -- Using the periodicity of the integrand, we can shift the interval of integration from $[\pi, 2\pi]$ to $[-\pi, 0]$.
    have h_shift : ∫ θ in (Real.pi)..2 * Real.pi, Complex.exp (g_fun z θ) * Complex.exp (-(m : ℂ) * θ * I) = ∫ θ in (-Real.pi)..0, Complex.exp (g_fun z (θ + 2 * Real.pi)) * Complex.exp (-(m : ℂ) * (θ + 2 * Real.pi) * I) := by
      convert intervalIntegral.integral_comp_sub_right _ (2 * Real.pi) using 2 <;> norm_num; ring
    -- Using the periodicity of the integrand, we can simplify the expression.
    have h_simplify : ∫ θ in (-Real.pi)..0, Complex.exp (g_fun z (θ + 2 * Real.pi)) * Complex.exp (-(m : ℂ) * (θ + 2 * Real.pi) * I) = ∫ θ in (-Real.pi)..0, Complex.exp (g_fun z θ) * Complex.exp (-(m : ℂ) * θ * I) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [ show g_fun z (x + 2 * Real.pi) = g_fun z x from _ ]
      · exact congrArg _ (Complex.exp_eq_exp_iff_exists_int.mpr ⟨-m, by push_cast; ring⟩)
      · exact g_fun_periodic z x
    rw [ h_periodic, h_shift, h_simplify ]
    rw [add_comm,
        intervalIntegral.integral_add_adjacent_intervals] <;> apply_rules [ Continuous.intervalIntegrable ]
    · refine Continuous.mul ?_ ?_
      · refine Complex.continuous_exp.comp ?_
        refine continuous_neg.comp ?_
        fun_prop
      · fun_prop
    · refine Continuous.mul ?_ ?_
      · refine Complex.continuous_exp.comp ?_
        refine continuous_neg.comp ?_
        fun_prop
      · fun_prop
  rw [ ← h_periodic, h_circle ]
  calc
    ∫ θ in (0 : ℝ)..2 * Real.pi,
        Complex.exp (g_fun z θ) * Complex.exp (-(m : ℂ) * θ * I) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        (-I) * ((Complex.exp (θ * I) ^ (m + 1))⁻¹ •
          G_gen z (Complex.exp (θ * I)) * I * Complex.exp (θ * I)) := by
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        norm_num [smul_eq_mul, ← Complex.exp_nat_mul, ← Complex.exp_neg, G_gen_eq_exp_g]
        ring_nf
        norm_num [mul_assoc, ← Complex.exp_add]
        ring_nf
    _ = -I * ∫ θ in (0 : ℝ)..2 * Real.pi,
        (Complex.exp (θ * I) ^ (m + 1))⁻¹ •
          G_gen z (Complex.exp (θ * I)) * I * Complex.exp (θ * I) :=
        intervalIntegral.integral_const_mul
          (a := (0 : ℝ)) (b := 2 * Real.pi) (r := -I)
          (f := fun θ : ℝ =>
            (Complex.exp (θ * I) ^ (m + 1))⁻¹ •
              G_gen z (Complex.exp (θ * I)) * I * Complex.exp (θ * I))

/-
For each m > n and 0 < r < 1:
    (r·exp(-iθ))^m / m integrated against g'·exp(g) gives
    2πi · r^m · d_m, where d_m = (2πi)⁻¹ ∮ G/w^{m+1}.
    Equivalently:
    ∫_{-π}^{π} g'exp(g) · (r exp(-iθ))^m / m dθ
    = r^m · ∮_{C(0,1)} G(w)/w^{m+1} dw
-/
lemma fourier_mode_integral_eq_circle {n : ℕ} (z : Fin n → ℂ)
    (m : ℕ) (hm : 0 < m) :
    ∫ θ in (-Real.pi)..Real.pi,
      g_deriv_fun z θ * Complex.exp (g_fun z θ) *
        ((↑m : ℂ)⁻¹ * Complex.exp (-(↑m : ℂ) * ↑θ * I)) =
    ∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w := by
  convert congr_arg (fun x : ℂ => (m : ℂ) ⁻¹ * x) (ibp_fourier_mode z m hm) using 1
  · calc
      ∫ θ in (-Real.pi)..Real.pi,
          g_deriv_fun z θ * Complex.exp (g_fun z θ) *
            ((↑m : ℂ)⁻¹ * Complex.exp (-(↑m : ℂ) * ↑θ * I)) =
        ∫ θ in (-Real.pi)..Real.pi,
          (↑m : ℂ)⁻¹ *
            (g_deriv_fun z θ * Complex.exp (g_fun z θ) *
              Complex.exp (-(↑m : ℂ) * ↑θ * I)) := by
          refine intervalIntegral.integral_congr fun θ hθ => ?_
          ring
      _ = (↑m : ℂ)⁻¹ *
          ∫ θ in (-Real.pi)..Real.pi,
            g_deriv_fun z θ * Complex.exp (g_fun z θ) *
              Complex.exp (-(↑m : ℂ) * ↑θ * I) :=
          intervalIntegral.integral_const_mul
            (a := -Real.pi) (b := Real.pi) (r := (↑m : ℂ)⁻¹)
            (f := fun θ : ℝ =>
              g_deriv_fun z θ * Complex.exp (g_fun z θ) *
                Complex.exp (-(↑m : ℂ) * ↑θ * I))
  · rw [ interval_integral_eq_circle ]
    ring_nf; norm_num [ hm.ne' ]

/-
Cauchy integral formula applied to G: for |r| < 1,
    (2πi)⁻¹ ∮ G(w)/(w-r) dw = G(r).
-/
lemma cauchy_G_gen {n : ℕ} (z : Fin n → ℂ) (y : ℂ) (hy : ‖y‖ < 1) :
    (2 * ↑Real.pi * I)⁻¹ • ∮ w in C(0, 1), (w - y)⁻¹ • G_gen z w = G_gen z y := by
  have := @Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
  convert this (Set.countable_singleton y) (show y ∈ Metric.ball 0 1 from by simpa using hy) (G_gen_differentiable z |> Differentiable.continuous |> Continuous.continuousOn) (fun x hx => G_gen_differentiable z |> Differentiable.differentiableAt) using 1

/-
G^{(m)}(0) = P^{(m)}(0) for m ≤ n.
    This follows from G(w) - P(w) = w^{n+1} * Q(w) for some analytic Q.
-/
lemma G_P_iteratedDeriv_eq {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (m : ℕ) (hm : m ≤ n) :
    iteratedDeriv m (G_gen z) 0 = iteratedDeriv m (P_poly z) 0 := by
  convert G_iteratedDeriv_eq_P z hz m hm using 1

/-
Circle integral of (G-P)/w^{m+1} vanishes for m ≤ n.
    Proof: (∮ f/w^{m+1})/(2πi) = f^{(m)}(0)/m!, so the integral of
    (G-P)/w^{m+1} is 2πi(G^{(m)}(0) - P^{(m)}(0))/m! = 0 by G_P_iteratedDeriv_eq.
-/
lemma circleIntegral_G_minus_P_eq_zero {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (m : ℕ) (hm : m ≤ n) :
    ∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • (G_gen z w - P_poly z w) = 0 := by
  -- By Cauchy's integral formula, we have:
  have h_cauchy : ∀ y : ℂ, ‖y‖ < 1 → (2 * Real.pi * I)⁻¹ • (∮ w in C(0, 1), (w - y)⁻¹ • (G_gen z w - P_poly z w)) = (G_gen z y - P_poly z y) := by
    intro y hy
    have h_cauchy : (∮ w in C(0, 1), (w - y)⁻¹ • (G_gen z w - P_poly z w)) = 2 * Real.pi * I * (G_gen z y - P_poly z y) := by
      have h_cauchy : ∀ f : ℂ → ℂ, Differentiable ℂ f → ∀ y : ℂ, ‖y‖ < 1 → (∮ w in C(0, 1), (w - y)⁻¹ • f w) = 2 * Real.pi * I * f y := by
        intro f hf y hy; have := @Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        simpa using @this ℂ _ _ _ 1 0 y f ∅ (by norm_num) (by simpa using hy) (hf.continuous.continuousOn) (by simpa using fun x hx => hf.differentiableAt)
      apply h_cauchy
      · refine Differentiable.sub ?_ ?_
        · grind +suggestions
        · unfold P_poly
          fun_prop
      · exact hy
    rw [h_cauchy, smul_eq_mul, inv_mul_eq_div,
        mul_div_cancel_left₀ _ (by norm_num [ Complex.ext_iff, Real.pi_ne_zero ])]
  -- By the properties of the power series expansion, we know that the coefficient of $y^m$ in $G(y) - P(y)$ is zero for $m \leq n$.
  have h_coeff : ∀ m ≤ n, (iteratedDeriv m (fun y => G_gen z y - P_poly z y) 0) = 0 := by
    intro m hm
    have h_coeff : iteratedDeriv m (fun y => G_gen z y - P_poly z y) 0 = iteratedDeriv m (G_gen z) 0 - iteratedDeriv m (P_poly z) 0 := by
      apply_rules [ iteratedDeriv_sub ]
      · exact Differentiable.contDiff (G_gen_differentiable z) |> ContDiff.contDiffAt
      · refine ContDiffAt.congr_of_eventuallyEq
          (f := fun y => ∏ r : Fin n, (1 - z r * y)) ?_ ?_
        · fun_prop (disch := norm_num)
        · exact Filter.Eventually.of_forall fun y => rfl
    rw [ h_coeff, G_P_iteratedDeriv_eq z hz m hm, sub_self ]
  contrapose! h_coeff
  refine ⟨m, hm, ?_⟩
  have h_integral_eq : ∀ y : ℂ, ‖y‖ < 1 → (G_gen z y - P_poly z y) = ∑' k : ℕ, (∮ w in C(0, 1), (w ^ (k + 1))⁻¹ • (G_gen z w - P_poly z w)) / (2 * Real.pi * I) * y ^ k := by
    intro y hy
    have h_integral_eq : (∮ w in C(0, 1), (w - y)⁻¹ • (G_gen z w - P_poly z w)) = ∑' k : ℕ, (∮ w in C(0, 1), (w ^ (k + 1))⁻¹ • (G_gen z w - P_poly z w)) * y ^ k := by
      have h_integral_eq : ∀ w : ℂ, ‖w‖ = 1 → (w - y)⁻¹ = ∑' k : ℕ, (w ^ (k + 1))⁻¹ * y ^ k := by
        intro w hw
        have h_series : (w - y)⁻¹ = w⁻¹ * (∑' k : ℕ, (y / w) ^ k) := by
          rw [ tsum_geometric_of_norm_lt_one ]
          · rw [ ← mul_inv, mul_sub, mul_one, mul_div_cancel₀ _ (by rintro rfl; norm_num at hw) ]
          · simpa [ hw ] using hy
        rw [ h_series, ← tsum_mul_left ]; congr; ext k; ring
      have h_integral_eq : ∀ N : ℕ, (∮ w in C(0, 1), (∑ k ∈ Finset.range N, (w ^ (k + 1))⁻¹ * y ^ k) • (G_gen z w - P_poly z w)) = ∑ k ∈ Finset.range N, (∮ w in C(0, 1), (w ^ (k + 1))⁻¹ • (G_gen z w - P_poly z w)) * y ^ k := by
        intro N; simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _,
                               circleIntegral]
        rw [ intervalIntegral.integral_finsetSum ]
        · refine Finset.sum_congr rfl fun i hi => ?_
          calc
            ∫ (x : ℝ) in 0..Real.pi * 2,
                I *
                  (y ^ i *
                    (circleMap 0 1 x *
                      ((G_gen z (circleMap 0 1 x) -
                          P_poly z (circleMap 0 1 x)) *
                        (circleMap 0 1 x ^ (i + 1))⁻¹))) =
              ∫ θ in 0..Real.pi * 2,
                y ^ i *
                  (I *
                    (circleMap 0 1 θ *
                      ((G_gen z (circleMap 0 1 θ) -
                          P_poly z (circleMap 0 1 θ)) *
                        (circleMap 0 1 θ ^ (i + 1))⁻¹))) := by
                refine intervalIntegral.integral_congr fun θ hθ => ?_
                ring
            _ = y ^ i *
                ∫ θ in 0..Real.pi * 2,
                  I *
                    (circleMap 0 1 θ *
                      ((G_gen z (circleMap 0 1 θ) -
                          P_poly z (circleMap 0 1 θ)) *
                        (circleMap 0 1 θ ^ (i + 1))⁻¹)) :=
                intervalIntegral.integral_const_mul
                  (a := (0 : ℝ)) (b := Real.pi * 2) (r := y ^ i)
                  (f := fun θ : ℝ =>
                    I *
                      (circleMap 0 1 θ *
                        ((G_gen z (circleMap 0 1 θ) -
                            P_poly z (circleMap 0 1 θ)) *
                          (circleMap 0 1 θ ^ (i + 1))⁻¹)))
            _ = y ^ i *
                (I * ∫ θ in 0..Real.pi * 2,
                  circleMap 0 1 θ *
                    ((G_gen z (circleMap 0 1 θ) -
                        P_poly z (circleMap 0 1 θ)) *
                      (circleMap 0 1 θ ^ (i + 1))⁻¹)) := by
                congr 1
                exact intervalIntegral.integral_const_mul
                  (a := (0 : ℝ)) (b := Real.pi * 2) (r := I)
                  (f := fun θ : ℝ =>
                    circleMap 0 1 θ *
                      ((G_gen z (circleMap 0 1 θ) -
                          P_poly z (circleMap 0 1 θ)) *
                        (circleMap 0 1 θ ^ (i + 1))⁻¹))
            _ = I * (y ^ i *
                ∫ θ in 0..Real.pi * 2,
                  circleMap 0 1 θ *
                    ((G_gen z (circleMap 0 1 θ) -
                        P_poly z (circleMap 0 1 θ)) *
                      (circleMap 0 1 θ ^ (i + 1))⁻¹)) := by
                ring
        · intro i hi; apply_rules [ ContinuousOn.intervalIntegrable ]; norm_num [ circleMap ]
          refine ContinuousOn.mul continuousOn_const ?_
          refine ContinuousOn.mul continuousOn_const ?_
          refine ContinuousOn.mul ?_ ?_
          · exact Continuous.continuousOn (by continuity)
          · refine ContinuousOn.mul ?_ ?_
            · refine ContinuousOn.sub ?_ ?_
              · exact Continuous.continuousOn (by exact Complex.continuous_exp.comp <| by continuity)
              · exact Continuous.continuousOn (by exact continuous_finsetProd _ fun _ _ => continuous_const.sub (continuous_const.mul (Complex.continuous_exp.comp (by continuity))))
            · exact ContinuousOn.inv₀ (Continuous.continuousOn (by continuity)) fun x hx => pow_ne_zero _ (Complex.exp_ne_zero _)
      have h_integral_eq : Filter.Tendsto (fun N : ℕ => (∮ w in C(0, 1), (∑ k ∈ Finset.range N, (w ^ (k + 1))⁻¹ * y ^ k) • (G_gen z w - P_poly z w))) Filter.atTop (nhds (∮ w in C(0, 1), (w - y)⁻¹ • (G_gen z w - P_poly z w))) := by
        refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence ?_ ?_ ?_ ?_ ?_
        focus
          use fun x => ‖deriv (circleMap 0 1) x‖ * (∑' k : ℕ, ‖y‖ ^ k) * ‖G_gen z (circleMap 0 1 x) - P_poly z (circleMap 0 1 x)‖
        · refine Filter.Eventually.of_forall fun N => Continuous.aestronglyMeasurable ?_
          refine Continuous.smul (M := ℂ) (X := ℂ) ?_ ?_
          · unfold deriv; norm_num [ fderiv_apply_one_eq_deriv ]; continuity
          · refine Continuous.smul (M := ℂ) (X := ℂ) ?_ ?_
            · exact continuous_finsetSum _ fun _ _ => Continuous.mul (Continuous.inv₀ (by continuity) fun x => by norm_num [ Complex.exp_ne_zero ]) (continuous_const.pow _)
            · refine Continuous.sub ?_ ?_
              · exact Complex.continuous_exp.comp <| Continuous.neg <| continuous_finsetSum _ fun _ _ => Continuous.mul (continuous_const) <| Continuous.pow (continuous_circleMap _ _) _
              · exact continuous_finsetProd _ fun _ _ => continuous_const.sub (continuous_const.mul (by continuity))
        · simp +zetaDelta at *
          refine ⟨0, fun N hN => Filter.Eventually.of_forall fun x hx => mul_le_mul_of_nonneg_right ?_ (by positivity)⟩
          refine le_trans
            (norm_sum_le (Finset.range N)
              (fun k => (circleMap 0 1 x ^ (k + 1))⁻¹ * y ^ k)) ?_
          norm_num [ circleMap ]
          exact Summable.sum_le_tsum (Finset.range N) (fun _ _ => by positivity) (summable_geometric_of_lt_one (by positivity) hy)
        · apply_rules [ ContinuousOn.intervalIntegrable ]
          refine ContinuousOn.mul ?_ ?_
          · norm_num [ circleMap ]
            exact continuousOn_const
          · refine ContinuousOn.norm ?_
            refine ContinuousOn.sub ?_ ?_
            · exact Continuous.continuousOn (by exact Complex.continuous_exp.comp <| by continuity)
            · exact Continuous.continuousOn (by exact continuous_finsetProd _ fun _ _ => continuous_const.sub (continuous_const.mul (by continuity)))
        · refine Filter.Eventually.of_forall fun x hx => ?_
          refine Filter.Tendsto.smul tendsto_const_nhds ?_
          refine Filter.Tendsto.smul ?_ tendsto_const_nhds
          convert Summable.hasSum _ |> HasSum.tendsto_sum_nat using 1
          focus
            rw [‹∀ w : ℂ, ‖w‖ = 1 → (w - y) ⁻¹ = ∑' k : ℕ,
                (w ^ (k + 1)) ⁻¹ * y ^ k› (circleMap 0 1 x) (by norm_num [ Complex.norm_exp ])]
          exact Summable.of_norm <| by simpa [ Complex.norm_exp ] using summable_geometric_of_lt_one (by positivity) hy
      refine tendsto_nhds_unique h_integral_eq ?_
      rw [ Filter.tendsto_congr ‹_› ]
      refine (Summable.hasSum ?_) |> HasSum.tendsto_sum_nat
      have h_integral_eq :
          ∃ C : ℝ, ∀ k : ℕ, ‖(∮ w in C(0, 1), (w ^ (k + 1))⁻¹ • (G_gen z w - P_poly z w))‖ ≤ C := by
        use (2 * Real.pi) * (SupSet.sSup (Set.image (fun w : ℂ => ‖G_gen z w - P_poly z w‖) (Metric.sphere 0 1)))
        intro k
        refine le_trans
          (circleIntegral.norm_integral_le_of_norm_le_const
            (C := sSup (Set.image (fun w => ‖G_gen z w - P_poly z w‖)
              (Metric.sphere 0 1))) (by norm_num) ?_) ?_
        · simp +zetaDelta at *
          exact fun w hw => by rw [hw, one_pow, inv_one,
                                   one_mul]; exact le_csSup (by exact (IsCompact.bddAbove (isCompact_sphere 0 1 |> IsCompact.image <| continuous_norm.comp <| by exact Continuous.sub (show Continuous fun w => G_gen z w from by exact Complex.continuous_exp.comp <| by continuity) <| show Continuous fun w => P_poly z w from by exact continuous_finsetProd _ fun _ _ => continuous_const.sub <| continuous_const.mul continuous_id'))) <| Set.mem_image_of_mem _ <| by simp [ hw ]
        · norm_num
      obtain ⟨C, hC⟩ := h_integral_eq
      -- Since ‖y‖ < 1, the series ∑' k : ℕ, C * ‖y‖^k is a geometric series with ratio ‖y‖, which converges.
      have h_geo_series : Summable (fun k : ℕ => C * ‖y‖^k) := by
        exact Summable.mul_left _ <| summable_geometric_of_lt_one (norm_nonneg _) hy
      -- Apply the comparison test with the summable series ∑' k : ℕ, C * ‖y‖^k.
      have h_comparison : ∀ k : ℕ, ‖(∮ w in C(0, 1), (w ^ (k + 1))⁻¹ • (G_gen z w - P_poly z w)) * y ^ k‖ ≤ C * ‖y‖^k := by
        exact fun k => by simpa using mul_le_mul_of_nonneg_right (hC k) (by positivity)
      -- Apply the comparison test with the summable series ∑' k : ℕ, C * ‖y‖^k to conclude that the original series is summable.
      have h_comparison_test : Summable (fun k : ℕ => ‖(∮ w in C(0, 1), (w ^ (k + 1))⁻¹ • (G_gen z w - P_poly z w)) * y ^ k‖) := by
        exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) h_comparison h_geo_series
      exact h_comparison_test.of_norm
    simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm ]
    rw [← h_cauchy y hy,
        h_integral_eq]; norm_num [ mul_assoc, mul_comm, mul_left_comm, tsum_neg, tsum_mul_left ]
    simp +decide only [← tsum_mul_left, mul_left_comm]
  have h_integral_eq : HasFPowerSeriesAt (fun y => G_gen z y - P_poly z y) (FormalMultilinearSeries.ofScalars ℂ (fun k => (∮ w in C(0, 1), (w ^ (k + 1))⁻¹ • (G_gen z w - P_poly z w)) / (2 * Real.pi * I))) 0 := by
    rw [ hasFPowerSeriesAt_iff ]
    filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with y hy
    simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm ]
    refine Summable.hasSum ?_
    refine Summable.of_norm ?_
    have h_integral_bound :
        ∃ C : ℝ, ∀ k : ℕ, ‖∮ w in C(0, 1), (G_gen z w - P_poly z w) * (w ^ (k + 1))⁻¹‖ ≤ C := by
      use (2 * Real.pi) * (SupSet.sSup (Set.image (fun w : ℂ => ‖G_gen z w - P_poly z w‖) (Metric.sphere 0 1)))
      intro k
      refine le_trans
        (circleIntegral.norm_integral_le_of_norm_le_const
          (C := sSup (Set.image (fun w => ‖G_gen z w - P_poly z w‖)
            (Metric.sphere 0 1))) (by norm_num) ?_) ?_
      · simp +zetaDelta at *
        exact fun w hw => by rw [hw, one_pow, inv_one,
                                 mul_one]; exact le_csSup (by exact (IsCompact.bddAbove (isCompact_sphere 0 1 |> IsCompact.image <| continuous_norm.comp <| by exact Continuous.sub (show Continuous fun w => G_gen z w from by exact Complex.continuous_exp.comp <| by continuity) <| show Continuous fun w => P_poly z w from by exact continuous_finsetProd _ fun _ _ => continuous_const.sub <| continuous_const.mul continuous_id'))) <| Set.mem_image_of_mem _ <| by simp [ hw ]
      · norm_num
    norm_num +zetaDelta at *
    exact Summable.of_nonneg_of_le (fun k => by positivity) (fun k => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h_integral_bound.choose_spec k) (by positivity)) (by positivity)) (by positivity)) (Summable.mul_right _ <| summable_geometric_of_lt_one (by positivity) hy)
  have := h_integral_eq.analyticAt
  have := this.hasFPowerSeriesAt
  have := this.eq_formalMultilinearSeries h_integral_eq
  replace this := congr_arg (fun f => f.coeff m) this; simp_all +decide []
  intro H; simp_all +decide [ div_eq_mul_inv ]
/-
For a polynomial P of degree ≤ n, the Cauchy integral formula gives back P:
    ∑_{m=0}^n y^m · (2πi)⁻¹ ∮ P(w)/w^{m+1} dw = P(y).
-/
lemma cauchy_poly_recovery {n : ℕ} (z : Fin n → ℂ) (y : ℂ) :
    ∑ m ∈ Finset.range (n + 1),
      y ^ m * ((2 * ↑Real.pi * I)⁻¹ • ∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • P_poly z w) =
    P_poly z y := by
  have h_poly : ∀ p : Polynomial ℂ, p.degree ≤ n → (∑ m ∈ Finset.range (n + 1), y ^ m * (2 * Real.pi * I)⁻¹ • (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • (p.eval w))) = p.eval y := by
    intro p hp
    have h_poly_eval : ∀ m ∈ Finset.range (n + 1), (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • (p.eval w)) = 2 * Real.pi * I * (p.coeff m) := by
      intro m hm
      have h_cauchy_integral : (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • (p.eval w)) = ∑ k ∈ Finset.range (n + 1), p.coeff k * (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • (w ^ k)) := by
        simp +decide [Polynomial.eval_eq_sum_range, Finset.mul_sum _ _ _, mul_left_comm,
                      ← circleIntegral.integral_const_mul]
        simp +decide [ circleIntegral ]
        rw [ intervalIntegral.integral_congr fun x hx => by rw [ Finset.mul_sum _ _ _ ] ]
        rw [ intervalIntegral.integral_finsetSum ]
        · refine Finset.sum_subset ?_ ?_ <;> intro i hi <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ]
          exact le_trans hi (Polynomial.natDegree_le_of_degree_le hp)
        · intro i hi; apply_rules [ ContinuousOn.intervalIntegrable ]; norm_num [ circleMap ]
          have h_exp : Continuous fun x : ℝ => Complex.exp ((x : ℂ) * I) := by
            fun_prop
          have h_inv : Continuous fun x : ℝ =>
              (Complex.exp ((x : ℂ) * I) ^ (m + 1))⁻¹ := by
            exact Continuous.inv₀ (h_exp.pow _) fun x =>
              pow_ne_zero _ (Complex.exp_ne_zero _)
          exact (h_exp.mul continuous_const |>.mul
            (h_inv.mul (continuous_const.mul (h_exp.pow i)))).continuousOn
      -- Evaluate the integral $\oint_{|w|=1} w^{k-m-1} \, dw$.
      have h_integral : ∀ k : ℕ, (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • (w ^ k)) = if k = m then 2 * Real.pi * I else 0 := by
        intro k
        simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
          circleIntegral_zpow_coeff k m
      simp_all +decide [ mul_comm ]
    rw [ Polynomial.eval_eq_sum_range' ]
    focus
      refine Finset.sum_congr rfl fun m hm => ?_
    · rw [ h_poly_eval m hm ]; norm_num [ mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero ]
      ring_nf; norm_num
    · exact Nat.lt_succ_of_le (Polynomial.natDegree_le_of_degree_le hp)
  have hdeg : (P_as_poly z).degree ≤ n := by
    exact le_trans Polynomial.degree_le_natDegree (by exact_mod_cast P_as_poly_natDegree_le z)
  simpa [P_poly_eq_eval] using h_poly (P_as_poly z) hdeg

/-
The Taylor sum of G through degree n equals P (Newton's identity):
    ∑_{m=0}^n r^m · (2πi)⁻¹ ∮ G/w^{m+1} dw = P(r) for any r.
    Proof: since G-P = O(w^{n+1}), the circle integrals of G/w^{m+1}
    and P/w^{m+1} agree for m ≤ n, and the sum for P gives back P(y).
-/
lemma G_taylor_partial_eq_P {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (_hz1 : z ⟨0, hn⟩ = 1) (hz : ∀ i, ‖z i‖ ≤ 1) (y : ℂ) :
    ∑ m ∈ Finset.range (n + 1),
      y ^ m * ((2 * ↑Real.pi * I)⁻¹ • ∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w) =
    P_poly z y := by
  convert cauchy_poly_recovery z y using 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have h_split : (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • (G_gen z w - P_poly z w)) = 0 := by
    convert circleIntegral_G_minus_P_eq_zero z hz m (Finset.mem_range_succ_iff.mp hm) using 1
  simp_all +decide [ circleIntegral, mul_sub ]
  rw [ intervalIntegral.integral_sub ] at h_split
  · exact Or.inl <| eq_of_sub_eq_zero h_split
  · apply_rules [ ContinuousOn.intervalIntegrable ]
    refine ContinuousOn.mul ?_ ?_
    · exact Continuous.continuousOn (by continuity)
    · refine ContinuousOn.mul ?_ ?_
      · exact ContinuousOn.inv₀ (Continuous.continuousOn (by continuity)) fun x hx => pow_ne_zero _ (ne_of_apply_ne Complex.normSq <| by norm_num [ Complex.normSq_eq_norm_sq, circleMap ])
      · exact Continuous.continuousOn (by exact Complex.continuous_exp.comp <| by continuity)
  · apply_rules [ ContinuousOn.intervalIntegrable ]
    refine ContinuousOn.mul (Continuous.continuousOn (by continuity)) (ContinuousOn.mul (ContinuousOn.inv₀ (Continuous.continuousOn (by continuity)) fun x hx => ?_) (Continuous.continuousOn (by continuity)))
    norm_num [ circleMap ]

/-
Master helper: the tail of the Taylor series of G equals G(r) - P(r).
    ∑_{m≥n+1} r^m · ∮ G/w^{m+1} dw = 2πi(G(r) - P(r)) for |r| < 1.
-/
lemma G_taylor_tail_eq {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∑' k : ℕ, (↑r : ℂ) ^ (k + n + 1) *
      (∮ w in C(0, 1), (w ^ (k + n + 1 + 1))⁻¹ • G_gen z w) =
    2 * ↑Real.pi * I * (G_gen z (↑r) - P_poly z (↑r)) := by
  -- The series $\sum_{m=n+1}^\infty r^m \sum_{|z| \leq 1} z^m$ converges for $|r| < 1$.
  have h_series_conv :
      Summable (fun m : ℕ => (r : ℂ) ^ m * (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w)) := by
    -- The circle integral of an entire function over the unit circle is bounded by the maximum modulus on the circle.
    have h_circle_integral_bound : ∀ m : ℕ, ‖∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w‖ ≤ 2 * Real.pi * (SupSet.sSup (Set.image (fun w : ℂ => ‖G_gen z w‖) (Metric.sphere 0 1))) := by
      intro m
      have h_circle_integral_bound : ∀ w ∈ Metric.sphere 0 1, ‖(w ^ (m + 1))⁻¹ • G_gen z w‖ ≤ sSup (Set.image (fun w => ‖G_gen z w‖) (Metric.sphere 0 1)) := by
        intro w hw; rw [ norm_smul ]; norm_num [ hw ]
        exact le_trans (by aesop) (le_csSup (by exact (IsCompact.bddAbove (isCompact_sphere 0 1 |> IsCompact.image <| continuous_norm.comp <| show Continuous fun w => G_gen z w from by exact Complex.continuous_exp.comp <| by continuity))) <| Set.mem_image_of_mem _ hw)
      refine le_trans
        (circleIntegral.norm_integral_le_of_norm_le_const
          (C := sSup ((fun w => ‖G_gen z w‖) '' Metric.sphere 0 1))
          (by norm_num) h_circle_integral_bound) ?_
      norm_num
    refine .of_norm ?_
    norm_num +zetaDelta at *
    exact Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg (abs_nonneg r) m) (norm_nonneg _)) (fun m => mul_le_mul_of_nonneg_left (h_circle_integral_bound m) (pow_nonneg (abs_nonneg r) m)) (Summable.mul_right _ <| summable_geometric_of_lt_one (abs_nonneg r) <| by rwa [ abs_of_pos hr ])
  have h_series_conv : ∑' m : ℕ, (r : ℂ) ^ m * (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w) = 2 * Real.pi * I * G_gen z r := by
    have h_series_conv : ∑' m : ℕ, (r : ℂ) ^ m * (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w) = ∮ w in C(0, 1), (∑' m : ℕ, (r : ℂ) ^ m * (w ^ (m + 1))⁻¹) • G_gen z w := by
      have h_series_conv : ∀ N : ℕ, ∑ m ∈ Finset.range N, (r : ℂ) ^ m * (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w) = ∮ w in C(0, 1), (∑ m ∈ Finset.range N, (r : ℂ) ^ m * (w ^ (m + 1))⁻¹) • G_gen z w := by
        intro N; simp +decide [mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, circleIntegral,
                               mul_comm]
        rw [ intervalIntegral.integral_finsetSum ]
        · refine Finset.sum_congr rfl fun i hi => ?_
          calc
            I * ((r : ℂ) ^ i *
                ∫ (x : ℝ) in 0..Real.pi * 2,
                  circleMap 0 1 x *
                    (G_gen z (circleMap 0 1 x) *
                      (circleMap 0 1 x ^ (i + 1))⁻¹)) =
              I * ∫ (x : ℝ) in 0..Real.pi * 2,
                (r : ℂ) ^ i *
                  (circleMap 0 1 x *
                    (G_gen z (circleMap 0 1 x) *
                      (circleMap 0 1 x ^ (i + 1))⁻¹)) := by
                congr 1
                exact (intervalIntegral.integral_const_mul
                  (a := (0 : ℝ)) (b := Real.pi * 2) (r := (r : ℂ) ^ i)
                  (f := fun x : ℝ =>
                    circleMap 0 1 x *
                      (G_gen z (circleMap 0 1 x) *
                        (circleMap 0 1 x ^ (i + 1))⁻¹))).symm
            _ = ∫ (x : ℝ) in 0..Real.pi * 2,
                I * ((r : ℂ) ^ i *
                  (circleMap 0 1 x *
                    (G_gen z (circleMap 0 1 x) *
                      (circleMap 0 1 x ^ (i + 1))⁻¹))) :=
                (intervalIntegral.integral_const_mul
                  (a := (0 : ℝ)) (b := Real.pi * 2) (r := I)
                  (f := fun x : ℝ =>
                    (r : ℂ) ^ i *
                      (circleMap 0 1 x *
                        (G_gen z (circleMap 0 1 x) *
                          (circleMap 0 1 x ^ (i + 1))⁻¹)))).symm
        · intro i hi; apply_rules [ ContinuousOn.intervalIntegrable ]
          refine ContinuousOn.mul continuousOn_const ?_
          refine ContinuousOn.mul continuousOn_const ?_
          refine ContinuousOn.mul (Continuous.continuousOn (by continuity)) (ContinuousOn.mul (Continuous.continuousOn (by exact G_gen_differentiable z |> Differentiable.continuous |> Continuous.comp <| by continuity)) (ContinuousOn.inv₀ (Continuous.continuousOn (by continuity)) fun x hx => by norm_num [ Complex.exp_ne_zero ]))
      have h_series_conv : Filter.Tendsto (fun N : ℕ => ∮ w in C(0, 1), (∑ m ∈ Finset.range N, (r : ℂ) ^ m * (w ^ (m + 1))⁻¹) • G_gen z w) Filter.atTop (nhds (∮ w in C(0, 1), (∑' m : ℕ, (r : ℂ) ^ m * (w ^ (m + 1))⁻¹) • G_gen z w)) := by
        refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence ?_ ?_ ?_ ?_ ?_
        focus
          use fun x => ‖deriv (circleMap 0 1) x‖ * (∑' m : ℕ, r ^ m) * ‖G_gen z (circleMap 0 1 x)‖
        · refine Filter.Eventually.of_forall fun N => Continuous.aestronglyMeasurable ?_
          refine Continuous.smul (M := ℂ) (X := ℂ) ?_ ?_
          · exact by rw [ show deriv (circleMap 0 1) = fun x => I * circleMap 0 1 x from funext fun x => by simp +decide [ circleMap, mul_comm ] ]; continuity
          · refine Continuous.smul (M := ℂ) (X := ℂ) ?_ ?_
            · exact continuous_finsetSum _ fun _ _ => Continuous.mul (continuous_const) (Continuous.inv₀ (by continuity) fun x => by norm_num [ Complex.exp_ne_zero ])
            · exact Complex.continuous_exp.comp <| Continuous.neg <| continuous_finsetSum _ fun _ _ => Continuous.mul (continuous_const) <| Continuous.pow (by continuity) _
        · simp +decide [ mul_assoc ]
          refine ⟨0, fun N hN => Filter.Eventually.of_forall fun x hx => mul_le_mul_of_nonneg_right ?_ (by positivity)⟩
          refine le_trans
            (norm_sum_le (Finset.range N)
              (fun m => (r : ℂ) ^ m * (circleMap 0 1 x ^ (m + 1))⁻¹)) ?_
          norm_num [ circleMap ]
          exact le_trans (Finset.sum_le_sum fun _ _ => by rw [ abs_of_pos hr ]) (Summable.sum_le_tsum (Finset.range N) (fun _ _ => by positivity) (summable_geometric_of_lt_one hr.le hr1))
        · apply_rules [ ContinuousOn.intervalIntegrable ]
          refine ContinuousOn.mul ?_ ?_
          · exact Continuous.continuousOn (by continuity)
          · exact Continuous.continuousOn (by exact Continuous.norm <| by exact G_gen_differentiable z |> Differentiable.continuous |> Continuous.comp <| by continuity)
        · refine Filter.Eventually.of_forall fun x hx => ?_
          refine Filter.Tendsto.smul tendsto_const_nhds ?_
          refine Filter.Tendsto.smul ?_ tendsto_const_nhds
          refine (Summable.hasSum ?_) |> HasSum.tendsto_sum_nat
          exact Summable.of_norm <| by simpa [ abs_of_pos hr ] using summable_geometric_of_lt_one (by positivity) hr1
      exact tendsto_nhds_unique (Summable.hasSum (by assumption) |> HasSum.tendsto_sum_nat) (h_series_conv.congr (by aesop))
    -- The series $\sum_{m=0}^\infty r^m w^{-m-1}$ is a geometric series with sum $\frac{1}{w-r}$.
    have h_geo_series :
        ∀ w : ℂ, w ∈ Metric.sphere 0 1 → ∑' m : ℕ, (r : ℂ) ^ m * (w ^ (m + 1))⁻¹ = (w - r)⁻¹ := by
      intro w hw
      have h_geo_series : ∑' m : ℕ, (r : ℂ) ^ m * (w ^ (m + 1))⁻¹ = (w⁻¹) * ∑' m : ℕ, (r / w) ^ m
          := by
        rw [ ← tsum_mul_left ]; congr; ext m; ring
      rw [ h_geo_series, tsum_geometric_of_norm_lt_one ]
      · rw [ ← mul_inv, mul_sub, mul_div_cancel₀ _ (by aesop) ]; ring
      · simp_all +decide [ div_eq_mul_inv ]
        rwa [ abs_of_pos hr ]
    rw [ h_series_conv, circleIntegral.integral_congr ]
    rotate_right
    focus
      use fun w => (w - r) ⁻¹ • G_gen z w
    · have := @cauchy_G_gen
      convert congr_arg (fun x : ℂ => (2 * Real.pi * I) * x) (this z r (by simpa [ abs_of_pos hr ] using hr1)) using 1; norm_num [mul_assoc,
                                                                                                                                  mul_comm,
                                                                                                                                  mul_left_comm]
      norm_num [ ← mul_assoc ]
    · norm_num
    · exact fun w hw => by rw [ h_geo_series w hw ]
  have h_split : ∑' m : ℕ, (r : ℂ) ^ m * (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w) = (∑ m ∈ Finset.range (n + 1), (r : ℂ) ^ m * (∮ w in C(0, 1), (w ^ (m + 1))⁻¹ • G_gen z w)) + (∑' m : ℕ, (r : ℂ) ^ (m + n + 1) * (∮ w in C(0, 1), (w ^ (m + n + 1 + 1))⁻¹ • G_gen z w)) := by
    rw [ ← Summable.sum_add_tsum_nat_add ]
    focus
      aesop
    assumption
  have := G_taylor_partial_eq_P hn z hz1 hz r; simp_all +decide [ mul_sub ]
  simp +decide [ ← this, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]
  norm_num [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ]

/-
**Regularized integral identity**: For 0 < r < 1,
∫ g'(θ) exp(g(θ)) h_r(θ) dθ = 2πi · (G(r) - P(r)).

This follows from:
1. Integration by parts: ∫ (exp(g))' · h_r = -∫ exp(g) · h_r'
   (boundary term vanishes by 2π-periodicity of exp(g(θ)) and h_r(θ)).
2. Computing h_r'(θ) = -i·r·exp(-iθ)/(1-r·exp(-iθ)) + i·∑ r^k·exp(-ikθ)
3. Cauchy's integral formula: ∮ G(y)/(y-r) dy = 2πi·G(r) gives
   ∫ G(exp(iθ))·r·exp(-iθ)/(1-r·exp(-iθ)) dθ = 2π(G(r) - G(0))
4. Fourier coefficient via Cauchy: ∫ G(exp(iθ)) exp(-ikθ) = 2π·d_k
5. Newton's identity: ∑_{k=0}^n d_k·r^k = P(r)
-/
set_option maxHeartbeats 30000000 in
-- The regularized integral proof exceeds the file-level heartbeat budget.
lemma regularized_integral_eq {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∫ θ in (-Real.pi)..Real.pi,
      g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun_reg n r θ =
    2 * ↑Real.pi * I * (G_gen z (r : ℂ) - P_poly z (r : ℂ)) := by
  classical
  let F : ℕ → ℝ → ℂ := fun k θ =>
    g_deriv_fun z θ * Complex.exp (g_fun z θ) *
      (((r : ℂ) * Complex.exp (-(θ : ℂ) * I)) ^ (k + n + 1) /
        (↑(k + n + 1) : ℂ))
  let B : ℝ → ℝ := fun θ => ‖g_deriv_fun z θ‖ * ‖Complex.exp (g_fun z θ)‖
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hF_int : ∀ k : ℕ, Integrable (F k) (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
    intro k
    refine Continuous.integrableOn_Ioc ?_
    dsimp [F]
    unfold g_deriv_fun g_fun
    fun_prop
  have hB_int : Integrable B (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
    refine Continuous.integrableOn_Ioc ?_
    dsimp [B]
    unfold g_deriv_fun g_fun
    fun_prop
  have hgeo : Summable (fun k : ℕ => r ^ (k + n + 1) / (k + n + 1 : ℝ)) := by
    have hgeom_shift : Summable (fun k : ℕ => r ^ (k + n + 1)) := by
      exact (summable_geometric_of_lt_one hr.le hr1).comp_injective (by
        intro a b h
        exact Nat.add_right_cancel (Nat.succ.inj h))
    refine Summable.of_nonneg_of_le
      (fun k => div_nonneg (pow_nonneg hr.le _) (by positivity)) ?_
      hgeom_shift
    · intro k
      exact div_le_self (pow_nonneg hr.le _) (by
        norm_num
        positivity)
  have hF_norm :
      Summable (fun k : ℕ => ∫ θ, ‖F k θ‖ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
    refine Summable.of_nonneg_of_le
      (fun k => MeasureTheory.integral_nonneg fun θ => norm_nonneg (F k θ)) ?_
      (hgeo.mul_left (∫ θ, B θ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi)))
    intro k
    have hnorm :
        (fun θ : ℝ => ‖F k θ‖) =
          fun θ : ℝ => (r ^ (k + n + 1) / (k + n + 1 : ℝ)) * B θ := by
      funext θ
      dsimp [F, B]
      simp [norm_pow, Complex.norm_exp, abs_of_pos hr,
        div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      left
      have hden : ‖((↑k + ↑n + 1 : ℂ))‖⁻¹ = ((↑k + ↑n + 1 : ℝ))⁻¹ := by
        have hcast : ((↑k + ↑n + 1 : ℂ)) = ((↑k + ↑n + 1 : ℝ) : ℂ) := by
          norm_num
        calc
          ‖((↑k + ↑n + 1 : ℂ))‖⁻¹ =
            ‖(((↑k + ↑n + 1 : ℝ) : ℂ))‖⁻¹ := by
              exact congrArg (fun u : ℂ => ‖u‖⁻¹) hcast
          _ = |(↑k + ↑n + 1 : ℝ)|⁻¹ := by
              exact congrArg Inv.inv (RCLike.norm_ofReal (K := ℂ) (↑k + ↑n + 1 : ℝ))
          _ = ((↑k + ↑n + 1 : ℝ))⁻¹ := by
              rw [abs_of_nonneg (show 0 ≤ (↑k + ↑n + 1 : ℝ) by positivity)]
      calc
        ‖((↑k + ↑n + 1 : ℂ))‖⁻¹ *
            (r ^ (k + n + 1) * Real.exp (g_fun z θ).re) =
          ((↑k + ↑n + 1 : ℝ))⁻¹ *
            (r ^ (k + n + 1) * Real.exp (g_fun z θ).re) := by
            exact congrArg
              (fun u : ℝ => u * (r ^ (k + n + 1) * Real.exp (g_fun z θ).re)) hden
        _ = r ^ (k + n + 1) *
            (((↑k + ↑n + 1 : ℝ))⁻¹ * Real.exp (g_fun z θ).re) := by
            ring_nf
    rw [hnorm]
    calc
      ∫ θ, (r ^ (k + n + 1) / (k + n + 1 : ℝ)) * B θ
          ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi)
          =
        (r ^ (k + n + 1) / (k + n + 1 : ℝ)) *
          ∫ θ, B θ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi) := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_const_mul
              (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi))
              (r := r ^ (k + n + 1) / (k + n + 1 : ℝ)) (f := B))
      _ =
        (∫ θ, B θ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi)) *
          (r ^ (k + n + 1) / (k + n + 1 : ℝ)) := by ring
      _ ≤
        (∫ θ, B θ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi)) *
          (r ^ (k + n + 1) / (k + n + 1 : ℝ)) := le_rfl
  have hterm : ∀ k : ℕ,
      ∫ θ in (-Real.pi)..Real.pi, F k θ =
        (r : ℂ) ^ (k + n + 1) *
          (∮ w in C(0, 1), (w ^ (k + n + 1 + 1))⁻¹ • G_gen z w) := by
    intro k
    have hk : 0 < k + n + 1 := by omega
    have hfourier := fourier_mode_integral_eq_circle z (k + n + 1) hk
    calc
      ∫ θ in (-Real.pi)..Real.pi, F k θ =
        ∫ θ in (-Real.pi)..Real.pi,
          (r : ℂ) ^ (k + n + 1) *
            (g_deriv_fun z θ * Complex.exp (g_fun z θ) *
              ((↑(k + n + 1) : ℂ)⁻¹ *
                Complex.exp (-(↑(k + n + 1) : ℂ) * ↑θ * I))) := by
          refine intervalIntegral.integral_congr fun θ hθ => ?_
          dsimp [F]
          norm_num [mul_pow, ← Complex.exp_nat_mul, div_eq_mul_inv]
          ring_nf
      _ =
        (r : ℂ) ^ (k + n + 1) *
          ∫ θ in (-Real.pi)..Real.pi,
            g_deriv_fun z θ * Complex.exp (g_fun z θ) *
              ((↑(k + n + 1) : ℂ)⁻¹ *
                Complex.exp (-(↑(k + n + 1) : ℂ) * ↑θ * I)) := by
          exact
            intervalIntegral.integral_const_mul ((r : ℂ) ^ (k + n + 1))
              (fun θ : ℝ =>
                g_deriv_fun z θ * Complex.exp (g_fun z θ) *
                  ((↑(k + n + 1) : ℂ)⁻¹ *
                    Complex.exp (-(↑(k + n + 1) : ℂ) * ↑θ * I)))
      _ =
        (r : ℂ) ^ (k + n + 1) *
          (∮ w in C(0, 1), (w ^ (k + n + 1 + 1))⁻¹ • G_gen z w) := by
          rw [hfourier]
  calc
    ∫ θ in (-Real.pi)..Real.pi,
        g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun_reg n r θ
        =
      ∫ θ in (-Real.pi)..Real.pi, ∑' k : ℕ, F k θ := by
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        rw [h_fun_reg_eq_tsum n r hr hr1 θ, ← tsum_mul_left]
    _ =
      ∑' k : ℕ, ∫ θ, F k θ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi) := by
        rw [intervalIntegral.integral_of_le hle]
        exact (MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_norm).symm
    _ =
      ∑' k : ℕ, ∫ θ in (-Real.pi)..Real.pi, F k θ := by
        refine tsum_congr fun k => ?_
        rw [intervalIntegral.integral_of_le hle]
    _ =
      ∑' k : ℕ, (r : ℂ) ^ (k + n + 1) *
        (∮ w in C(0, 1), (w ^ (k + n + 1 + 1))⁻¹ • G_gen z w) := by
        exact tsum_congr hterm
    _ =
      2 * ↑Real.pi * I * (G_gen z (r : ℂ) - P_poly z (r : ℂ)) :=
        G_taylor_tail_eq hn z hz1 hz r hr hr1

/-
The regularized integral converges to the actual integral as r → 1⁻.
This is dominated convergence: h_r → h pointwise a.e., and
|g'·exp(g)·h_r| is dominated by an integrable function uniformly in r near 1.
-/
lemma regularized_limit {n : ℕ} (_hn : 0 < n) (z : Fin n → ℂ)
    (_hz : ∀ i, ‖z i‖ ≤ 1) :
    Filter.Tendsto (fun r : ℝ =>
      ∫ θ in (-Real.pi)..Real.pi,
        g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun_reg n r θ)
    (nhdsWithin 1 (Set.Iio 1))
    (nhds (∫ θ in (-Real.pi)..Real.pi,
        g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun n θ)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence ?_ ?_ ?_ ?_ ?_
  focus
    refine fun θ => ‖g_deriv_fun z θ * Complex.exp (g_fun z θ)‖ * (|Real.log (|Real.sin (θ / 2)|)| + 2 * Real.pi + ∑ k ∈ Finset.range n, (1 / (k + 1) : ℝ))
  · refine Filter.Eventually.of_forall fun r => Measurable.aestronglyMeasurable ?_
    refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · refine Measurable.mul ?_ ?_
        · exact measurable_const
        · fun_prop
      · refine Complex.continuous_exp.measurable.comp ?_
        refine Measurable.neg ?_
        fun_prop
    · refine Measurable.sub ?_ ?_
      · fun_prop
      · fun_prop
  · -- The term h_fun_reg n r θ is bounded by |log(|sin(θ/2)|)| + 2π + ∑ k ∈ Finset.range n, (1/(k+1)) for r in [1/2, 1).
    have h_h_fun_reg_bound : ∀ r ∈ Set.Icc (1 / 2) 1, ∀ θ ∈ Set.Ioc (-Real.pi) Real.pi, θ ≠ 0 → ‖h_fun_reg n r θ‖ ≤ |Real.log (|Real.sin (θ / 2)|)| + 2 * Real.pi + ∑ k ∈ Finset.range n, (1 / (k + 1) : ℝ) := by
      intros r hr θ hθ hθ_ne_zero
      have h_log_bound : ‖Complex.log (1 - r * Complex.exp (-(θ : ℂ) * I))‖ ≤ |Real.log (|Real.sin (θ / 2)|)| + 2 * Real.pi := by
        have h_log_bound : ‖Complex.log (1 - r * Complex.exp (-(θ : ℂ) * I))‖ ≤ |Real.log (‖1 - r * Complex.exp (-(θ : ℂ) * I)‖)| + Real.pi := by
          rw [ Complex.norm_def ]
          rw [ Real.sqrt_le_left ] <;> norm_num [ Complex.normSq, Complex.log_re, Complex.log_im ]
          · cases abs_cases (Real.log ‖1 - r * Complex.exp (- (θ * I))‖) <;> nlinarith [Real.pi_pos,
                                                                                        Complex.neg_pi_lt_arg (1 - r * Complex.exp (- (θ * I))),
                                                                                        Complex.arg_le_pi (1 - r * Complex.exp (- (θ * I)))]
          · positivity
        have h_norm_bound : ‖1 - r * Complex.exp (-(θ : ℂ) * I)‖ ≥ |Real.sin (θ / 2)| := by
          norm_num [ Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im ]
          refine Real.abs_le_sqrt <| ?_
          rw [ Real.sin_sq, Real.cos_sq ]; ring_nf
          rw [ Real.sin_sq ]; nlinarith [ hr.1, hr.2, mul_le_mul_of_nonneg_left hr.1 (sub_nonneg_of_le hr.2), Real.cos_le_one θ, Real.neg_one_le_cos θ ]
        have h_log_bound : |Real.log (‖1 - r * Complex.exp (-(θ : ℂ) * I)‖)| ≤ |Real.log (|Real.sin (θ / 2)|)| + |Real.log 2| := by
          have h_log_bound : Real.log (‖1 - r * Complex.exp (-(θ : ℂ) * I)‖) ≤ Real.log 2 := by
            gcongr
            · exact lt_of_lt_of_le (abs_pos.mpr (show Real.sin (θ / 2) ≠ 0 from by exact fun h => hθ_ne_zero <| by rw [ Real.sin_eq_zero_iff_of_lt_of_lt ] at h <;> linarith [ hθ.1, hθ.2 ])) h_norm_bound
            · norm_num [ Complex.norm_def, Complex.normSq ]
              norm_num [ Complex.exp_re, Complex.exp_im ]
              rw [ Real.sqrt_le_left ] <;> ring_nf <;> norm_num
              rw [ Real.sin_sq ]; nlinarith [ hr.1, hr.2, Real.neg_one_le_cos θ, Real.cos_le_one θ ]
          have h_log_bound :
              Real.log (‖1 - r * Complex.exp (-(θ : ℂ) * I)‖) ≥ Real.log (|Real.sin (θ / 2)|) := by
            exact Real.log_le_log (abs_pos.mpr (show Real.sin (θ / 2) ≠ 0 from by exact fun h => hθ_ne_zero <| by rw [ Real.sin_eq_zero_iff_of_lt_of_lt ] at h <;> linarith [ hθ.1, hθ.2 ])) h_norm_bound
          cases abs_cases (Real.log ‖1 - r * Complex.exp (-θ * I)‖) <;> cases abs_cases (Real.log |Real.sin (θ / 2)|) <;> cases abs_cases (Real.log 2) <;> linarith
        linarith [Real.pi_gt_three,
                  show |Real.log 2| ≤ Real.pi by rw [ abs_of_nonneg (Real.log_nonneg one_le_two) ]; linarith [ Real.pi_gt_three, Real.log_le_sub_one_of_pos zero_lt_two ]]
      have h_sum_bound : ‖∑ k ∈ Finset.range n, (r : ℂ) ^ (k + 1) * Complex.exp (-(↑(k + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(k + 1 : ℕ) : ℂ)‖ ≤ ∑ k ∈ Finset.range n, (1 / (k + 1) : ℝ) := by
        refine le_trans
          (norm_sum_le (Finset.range n)
            (fun k => (r : ℂ) ^ (k + 1) *
              Complex.exp (-(↑(k + 1 : ℕ) : ℂ) * ↑θ * I) /
                (↑(k + 1 : ℕ) : ℂ))) ?_
        norm_num [ Complex.norm_exp ]
        exact Finset.sum_le_sum fun i hi => by rw [ abs_of_nonneg (by linarith [ hr.1 ]) ]; exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by linarith [ hr.1 ]) (by linarith [ hr.2 ])) |> le_trans <| by norm_cast
      unfold h_fun_reg
      refine le_trans
        (norm_sub_le
          (-Complex.log (1 - r * Complex.exp (-(θ : ℂ) * I)))
          (∑ k ∈ Finset.range n, (r : ℂ) ^ (k + 1) *
            Complex.exp (-(↑(k + 1 : ℕ) : ℂ) * ↑θ * I) /
              (↑(k + 1 : ℕ) : ℂ))) ?_
      simpa [norm_neg] using add_le_add h_log_bound h_sum_bound
    refine Filter.eventually_of_mem (Ioo_mem_nhdsLT <| show 1 / 2 < 1 by norm_num) fun r hr => Filter.eventually_of_mem (MeasureTheory.measure_eq_zero_iff_ae_notMem.mp <| MeasureTheory.measure_singleton 0) fun x hx => ?_
    simp +zetaDelta at *
    exact fun hx' => mul_le_mul_of_nonneg_left (h_h_fun_reg_bound r (by norm_num at *; linarith) (by norm_num at *; linarith) x (by cases Set.mem_uIoc.mp hx' <;> linarith [ Real.pi_pos ]) (by cases Set.mem_uIoc.mp hx' <;> linarith [ Real.pi_pos ]) hx) (by positivity)
  · -- The function inside the integral is bounded and continuous, hence integrable.
    have h_integrable : MeasureTheory.IntegrableOn (fun θ => |Real.log (|Real.sin (θ / 2)|)| + 2 * Real.pi + ∑ k ∈ Finset.range n, (1 / (k + 1) : ℝ)) (Set.Icc (-Real.pi) Real.pi) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun θ => |Real.log (|Real.sin (θ / 2)|)|) (Set.Icc (-Real.pi) Real.pi) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun θ => |Real.log (|Real.sin θ|)|) (Set.Icc (-Real.pi / 2) (Real.pi / 2)) := by
          have h_integrable : MeasureTheory.IntegrableOn (fun θ => |Real.log (Real.sin θ)|) (Set.Ioc 0 (Real.pi / 2)) := by
            have h_integrable :
                MeasureTheory.IntegrableOn (fun θ => |Real.log θ|) (Set.Ioc 0 (Real.pi / 2)) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun θ => |Real.log θ|) (Set.Ioc 0 1)
                  := by
                have h_integrable : ∫ θ in Set.Ioc 0 1, |Real.log θ| = 1 := by
                  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => abs_of_nonpos (Real.log_nonpos hx.1.le hx.2),
                      ← intervalIntegral.integral_of_le] <;> norm_num
                exact (by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ]; norm_num)
              have h_integrable :
                  MeasureTheory.IntegrableOn (fun θ => |Real.log θ|) (Set.Ioc 1 (Real.pi / 2)) := by
                exact ContinuousOn.integrableOn_Icc (by exact ContinuousOn.abs (Real.continuousOn_log.mono <| by norm_num)) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self
              convert MeasureTheory.IntegrableOn.union ‹IntegrableOn (fun θ => |Real.log θ|) (Set.Ioc 0 1) volume› ‹IntegrableOn (fun θ => |Real.log θ|) (Set.Ioc 1 (Real.pi / 2)) volume› using 1; rw [ Set.Ioc_union_Ioc_eq_Ioc ] <;> linarith [ Real.pi_gt_three ]
            have h_integrable : ∀ θ ∈ Set.Ioc 0 (Real.pi / 2), |Real.log (Real.sin θ)| ≤ |Real.log θ| + |Real.log 2| := by
              intros θ hθ
              have h_sin_le : Real.sin θ ≥ θ / 2 := by
                have := Real.mul_le_sin hθ.1.le hθ.2
                rw [div_mul_eq_mul_div,
                    div_le_iff₀] at this <;> nlinarith [ Real.pi_gt_three, Real.pi_le_four, hθ.1, hθ.2 ]
              rw [ abs_le ]
              constructor
              · cases abs_cases (Real.log θ) <;> cases abs_cases (Real.log 2) <;> linarith [Real.log_le_log (by linarith [ hθ.1 ]) h_sin_le,
                                                                                            Real.log_div (show θ ≠ 0 from hθ.1.ne') (show (2 : ℝ) ≠ 0 from by norm_num)]
              · cases abs_cases (Real.log θ) <;> cases abs_cases (Real.log 2) <;> linarith [Real.log_le_log (by linarith [ hθ.1 ]) h_sin_le,
                                                                                            Real.log_le_log (by linarith [ hθ.1 ]) (show Real.sin θ ≤ θ from le_of_lt (Real.sin_lt <| by linarith [ hθ.1 ]))]
            refine MeasureTheory.Integrable.mono'
              (g := fun θ => |Real.log θ| + |Real.log 2|) ?_ ?_ ?_
            exacts [by exact MeasureTheory.Integrable.add ‹_› (MeasureTheory.integrable_const _),
                    by exact Measurable.aestronglyMeasurable (by exact Measurable.norm (Measurable.log (Real.continuous_sin.measurable))),
                    Filter.eventually_of_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioc) fun x hx => by simpa using h_integrable x hx]
          have h_integrable : MeasureTheory.IntegrableOn (fun θ => |Real.log (Real.sin θ)|) (Set.Ioc (-Real.pi / 2) (Real.pi / 2)) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun θ => |Real.log (Real.sin θ)|) (Set.Ioc (-Real.pi / 2) 0) := by
              rw [ ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [ Real.pi_pos ]) ] at *
              rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [ Real.pi_pos ]) ] at *
              simpa [Set.neg_Ioo, Real.sin_neg, Real.log_neg_eq_log, neg_div] using
                h_integrable.comp_neg
            convert h_integrable.union ‹IntegrableOn (fun θ => |Real.log (Real.sin θ)|) (Set.Ioc 0 (Real.pi / 2)) volume› using 1; rw [ Set.Ioc_union_Ioc_eq_Ioc ] <;> linarith [ Real.pi_pos ]
          simpa [MeasureTheory.IntegrableOn,
                 MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc] using h_integrable
        rw [ ← MeasureTheory.integrable_indicator_iff (measurableSet_Icc) ] at *
        refine (h_integrable.comp_smul (show (2⁻¹ : ℝ) ≠ 0 by norm_num)).congr ?_
        filter_upwards with x
        have hscale : (2⁻¹ : ℝ) • x = x / 2 := by
          rw [smul_eq_mul]
          ring
        by_cases hx : x ∈ Set.Icc (-Real.pi) Real.pi
        · have hx' : (2⁻¹ : ℝ) • x ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2) := by
            rw [hscale]
            rcases hx with ⟨hxlo, hxhi⟩
            constructor <;> linarith
          have hx'_mul : -Real.pi / 2 ≤ 2⁻¹ * x ∧ 2⁻¹ * x ≤ Real.pi / 2 := by
            simpa [smul_eq_mul] using hx'
          simp [Set.indicator, Set.mem_Icc, hx, hx'_mul, Real.log_abs]
          rw [show 2⁻¹ * x = x / 2 by ring]
        · have hx' : (2⁻¹ : ℝ) • x ∉ Set.Icc (-Real.pi / 2) (Real.pi / 2) := by
            intro hx'
            apply hx
            rw [hscale] at hx'
            rcases hx' with ⟨hxlo, hxhi⟩
            constructor <;> linarith
          have hx'_mul : ¬(-Real.pi / 2 ≤ 2⁻¹ * x ∧ 2⁻¹ * x ≤ Real.pi / 2) := by
            simpa [smul_eq_mul] using hx'
          simp [Set.indicator, Set.mem_Icc, hx, hx'_mul]
      exact MeasureTheory.Integrable.add (MeasureTheory.Integrable.add h_integrable (MeasureTheory.integrable_const _)) (MeasureTheory.integrable_const _)
    rw [ intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [ Real.pi_pos ]) ]
    refine h_integrable.const_mul ?_ |> fun h => h.mono' ?_ ?_
    focus
      exact (SupSet.sSup (Set.image (fun θ => ‖g_deriv_fun z θ * Complex.exp (g_fun z θ)‖) (Set.Icc (-Real.pi) Real.pi)))
    · refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_
        refine Continuous.norm ?_
        refine Continuous.mul ?_ ?_
        · refine continuous_const.mul ?_
          fun_prop
        · refine Complex.continuous_exp.comp ?_
          refine Continuous.neg ?_
          fun_prop
      · exact h_integrable.aestronglyMeasurable
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx
      rw [ Real.norm_of_nonneg (by positivity) ]
      gcongr
      refine le_csSup ?_ ?_
      · refine IsCompact.bddAbove (isCompact_Icc.image ?_)
        unfold g_deriv_fun g_fun; norm_num [Complex.exp_ne_zero, Finset.sum_range_succ']; continuity
      · grind
  · refine MeasureTheory.measure_mono_null
      (t := { 0 } ∪ { x : ℝ | Real.sin (x / 2) = 0 }) ?_ ?_
    · intro x hx; contrapose! hx; simp_all +decide []
      refine fun hx => Filter.Tendsto.mul tendsto_const_nhds ?_
      refine Filter.Tendsto.sub ?_ ?_
      · refine Filter.Tendsto.neg (Filter.Tendsto.comp (Complex.differentiableAt_log ?_ |> DifferentiableAt.continuousAt) ?_)
        · norm_num [ Complex.slitPlane, Complex.exp_re, Complex.exp_im ]
          exact Or.inl (by rw [ show x = 2 * (x / 2) by ring, Real.cos_two_mul ]; nlinarith [ Real.sin_sq_add_cos_sq (x / 2), mul_self_pos.mpr ‹_› ])
        · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ <| by norm_num)
      · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ <| by norm_num)
    · norm_num [ Real.sin_eq_zero_iff ]
      norm_num [ eq_div_iff ]
      erw [ Set.countable_range _ |> fun h => h.measure_zero _ ]

set_option maxHeartbeats 1600000 in
-- This identity depends on the preceding Abel regularization argument.
lemma atkinson_core_identity {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∫ θ in (-Real.pi)..Real.pi,
      g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun n θ =
    2 * ↑Real.pi * I * Complex.exp (g_fun z 0) := by
  -- The proof uses Abel regularization.
  -- Define the auxiliary function f(r) = 2πi·(G(r) - P(r))
  -- and show f(r) converges to both the integral and to 2πi·exp(g(0)) as r → 1⁻.
  have hnebot : (nhdsWithin (1:ℝ) (Set.Iio 1)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, by norm_num⟩
  -- Step 1: f(r) = regularized integral for 0 < r < 1
  -- Step 2: regularized integral → actual integral as r → 1⁻
  -- Therefore f(r) → actual integral
  have hLim := regularized_limit hn z hz
  have hConverge : Filter.Tendsto
      (fun r : ℝ => 2 * (↑Real.pi : ℂ) * I * (G_gen z (↑r) - P_poly z (↑r)))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (∫ θ in (-Real.pi)..Real.pi,
        g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun n θ)) := by
    apply hLim.congr'
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [eventually_gt_nhds (show (0:ℝ) < 1 by norm_num)] with r hr hr_mem
    exact (regularized_integral_eq hn z hz1 hz r hr hr_mem)
  -- Step 3: f(r) → 2πi·exp(g(0)) by continuity + G(1)=exp(g(0)), P(1)=0
  have hG_cont : Continuous (fun r : ℝ => G_gen z (↑r : ℂ)) := by
    unfold G_gen; fun_prop
  have hP_cont : Continuous (fun r : ℝ => P_poly z (↑r : ℂ)) := by
    unfold P_poly; fun_prop
  have hTarget : Filter.Tendsto
      (fun r : ℝ => 2 * (↑Real.pi : ℂ) * I * (G_gen z (↑r) - P_poly z (↑r)))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (2 * (↑Real.pi : ℂ) * I * Complex.exp (g_fun z 0))) := by
    apply Filter.Tendsto.const_mul
    have h1 : Complex.exp (g_fun z 0) = G_gen z (1:ℂ) - P_poly z (1:ℂ) := by
      rw [G_gen_one, P_poly_one_eq_zero hn z hz1, sub_zero]
    rw [h1]
    exact ((hG_cont.tendsto 1).sub (hP_cont.tendsto 1)).mono_left nhdsWithin_le_nhds
  -- By uniqueness of limits
  exact tendsto_nhds_unique hConverge hTarget

/-- **The key integral identity** from Atkinson's proof:
∫ g'(θ) · exp(g(θ)-g(0)) · h(θ) dθ = 2πi.

This follows from:
1. exp(-∑ s_k y^k/k) = ∏(1-z_r y) (generating function identity)
2. P(1) = 0 since z₁ = 1
3. Integration by parts for Fourier coefficients
4. Summing over modes > n -/
lemma atkinson_integral_identity {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∫ θ in (-Real.pi)..Real.pi,
      g_deriv_fun z θ * Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ =
    2 * ↑Real.pi * I := by
  -- Rewrite exp(g(θ) - g(0)) = exp(g(θ)) · exp(-g(0))
  have h_eq : ∀ θ : ℝ,
      g_deriv_fun z θ * Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ =
      Complex.exp (-g_fun z 0) * (g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun n θ) := by
    intro θ; rw [sub_eq_add_neg, Complex.exp_add]; ring
  simp_rw [h_eq]
  have : cexp (-g_fun z 0) * cexp (g_fun z 0) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc
    ∫ θ in (-Real.pi)..Real.pi,
        Complex.exp (-g_fun z 0) *
          (g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun n θ) =
      Complex.exp (-g_fun z 0) *
        ∫ θ in (-Real.pi)..Real.pi,
          g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun n θ :=
        intervalIntegral.integral_const_mul
          (a := -Real.pi) (b := Real.pi) (r := Complex.exp (-g_fun z 0))
          (f := fun θ : ℝ =>
            g_deriv_fun z θ * Complex.exp (g_fun z θ) * h_fun n θ)
    _ = Complex.exp (-g_fun z 0) *
        (2 * ↑Real.pi * I * Complex.exp (g_fun z 0)) := by
        rw [atkinson_core_identity hn z hz1 hz]
    _ = 2 * ↑Real.pi * I := by
        linear_combination (2 * ↑Real.pi * I) * this

/-
**Cauchy-Schwarz for interval integrals**: |∫ fg|² ≤ (∫|f|²)(∫|g|²).
-/
lemma cauchy_schwarz_intervalIntegral (f g : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hf2 : IntervalIntegrable (fun x => (‖f x‖ ^ 2 : ℝ)) volume a b)
    (hg2 : IntervalIntegrable (fun x => (‖g x‖ ^ 2 : ℝ)) volume a b) :
    ‖∫ x in a..b, f x * g x‖ ^ 2 ≤
      (∫ x in a..b, (‖f x‖ ^ 2 : ℝ)) * (∫ x in a..b, (‖g x‖ ^ 2 : ℝ)) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hab] at *
  -- By the properties of the inner product and the Cauchy-Schwarz inequality, we have:
  have h_inner : ‖∫ x in Set.Ioc a b, f x * g x‖ ^ 2 ≤ (∫ x in Set.Ioc a b, ‖f x‖ * ‖g x‖) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [ ← norm_mul ] using MeasureTheory.norm_integral_le_integral_norm (fun x => f x * g x)) _
  have h_cauchy_schwarz : ∀ {u v : ℝ → ℝ}, MeasureTheory.IntegrableOn (fun x => u x * v x) (Set.Ioc a b) → MeasureTheory.IntegrableOn (fun x => u x ^ 2) (Set.Ioc a b) → MeasureTheory.IntegrableOn (fun x => v x ^ 2) (Set.Ioc a b) → (∫ x in Set.Ioc a b, u x * v x) ^ 2 ≤ (∫ x in Set.Ioc a b, u x ^ 2) * (∫ x in Set.Ioc a b, v x ^ 2) := by
    intros u v huv hu hv
    have h_cauchy_schwarz : (∫ x in Set.Ioc a b, (u x - (∫ x in Set.Ioc a b, u x * v x) / (∫ x in Set.Ioc a b, v x ^ 2) * v x) ^ 2) ≥ 0 := by
      exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
    by_cases h : ∫ x in Set.Ioc a b, v x ^ 2 = 0 <;> simp_all +decide [sub_sq, mul_assoc, mul_comm, mul_left_comm]
    · rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) ] at h
      · exact MeasureTheory.integral_eq_zero_of_ae (h.mono fun x hx => by aesop)
      · exact hv
    · rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] at h_cauchy_schwarz
      · simp_all +decide [mul_pow, ← mul_assoc,
                          MeasureTheory.integral_mul_const]
        nlinarith [mul_div_cancel₀ (∫ x in Set.Ioc a b, u x * v x) h, show 0 ≤ ∫ x in Set.Ioc a b,
                   u x ^ 2 from MeasureTheory.integral_nonneg fun _ => sq_nonneg _,
                   show 0 ≤ ∫ x in Set.Ioc a b,
                   v x ^ 2 from MeasureTheory.integral_nonneg fun _ => sq_nonneg _]
      · exact hu
      · simpa [mul_assoc, mul_comm, mul_left_comm] using
          huv.mul_const (2 * ((∫ x in Set.Ioc a b, u x * v x) /
            ∫ x in Set.Ioc a b, v x ^ 2))
      · refine MeasureTheory.Integrable.sub hu ?_
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          huv.mul_const (2 * ((∫ x in Set.Ioc a b, u x * v x) /
            ∫ x in Set.Ioc a b, v x ^ 2))
      · simpa only [ mul_pow ] using hv.mul_const _
  refine le_trans h_inner (h_cauchy_schwarz ?_ ?_ ?_) <;> simp_all +decide [ intervalIntegrable_iff ]
  refine MeasureTheory.Integrable.mono' (hf2.add hg2) ?_ ?_
  · exact hf.norm.aestronglyMeasurable.mul hg.norm.aestronglyMeasurable
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by simpa using by nlinarith only [ norm_nonneg (f x), norm_nonneg (g x) ]

/-
‖g'‖² is interval integrable on [-π, π].
-/
lemma g_deriv_sq_intervalIntegrable {n : ℕ} (z : Fin n → ℂ) :
    IntervalIntegrable (fun θ => (‖g_deriv_fun z θ‖ ^ 2 : ℝ))
      volume (-Real.pi) Real.pi := by
  apply_rules [ Continuous.intervalIntegrable ]
  exact Continuous.pow (continuous_norm.comp <| by unfold g_deriv_fun; continuity) _

/-
‖exp(g-g(0))*h‖² is interval integrable on [-π, π].
-/
lemma exp_g_h_sq_intervalIntegrable {n : ℕ} (_hn : 0 < n) (z : Fin n → ℂ)
    (_hz : ∀ i, ‖z i‖ ≤ 1) :
    IntervalIntegrable (fun θ => (‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 : ℝ))
      volume (-Real.pi) Real.pi := by
  rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [ Real.pi_pos ]) ]
  refine MeasureTheory.Integrable.mono'
    (g := fun θ =>
      (SupSet.sSup (Set.image
        (fun θ => ‖Complex.exp (g_fun z θ - g_fun z 0)‖ ^ 2)
        (Set.Icc (-Real.pi) Real.pi))) * ‖h_fun n θ‖ ^ 2) ?_ ?_ ?_
  · refine MeasureTheory.Integrable.const_mul ?_
      (SupSet.sSup (Set.image
        (fun θ => ‖Complex.exp (g_fun z θ - g_fun z 0)‖ ^ 2)
        (Set.Icc (-Real.pi) Real.pi)) : ℝ)
    refine MeasureTheory.Integrable.mono'
      (g := fun θ =>
        (Real.pi ^ 2 + (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1)) ^ 2) * 2 +
          2 * Real.log (1 / |Real.sin (θ / 2)|) ^ 2) ?_ ?_ ?_
    · -- The integral of $(\log |\sin(\theta/2)|)^2$ over $(-\pi, \pi)$ is finite.
      have h_log_sin_sq_integrable : MeasureTheory.IntegrableOn (fun θ => (Real.log |Real.sin (θ / 2)|) ^ 2) (Set.Ioo (-Real.pi) Real.pi) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun θ => (Real.log (Real.sin θ)) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
          have h_integrable :
              MeasureTheory.IntegrableOn (fun θ => (Real.log θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun θ => (Real.log θ) ^ 2) (Set.Ioc 0 (Real.pi / 2)) := by
              have h_integrable :
                  MeasureTheory.IntegrableOn (fun θ => (Real.log θ) ^ 2) (Set.Ioc 0 1) := by
                have h_integrable :
                    MeasureTheory.IntegrableOn (fun θ => θ ^ (-1 / 2 : ℝ)) (Set.Ioc (0 : ℝ) 1) := by
                  exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).1
                -- Since $|\log \theta|^2 \leq C \theta^{-1/2}$ for some bound $C$ and $\theta \in (0, 1]$, and $\theta^{-1/2}$ is integrable on $(0, 1]$, it follows that $|\log \theta|^2$ is also integrable on $(0, 1]$.
                have h_log_sq_le :
                    ∃ C : ℝ, ∀ θ ∈ Set.Ioc (0 : ℝ) 1, |Real.log θ|^2 ≤ C * θ^(-1 / 2 : ℝ) := by
                  use 16
                  intros θ hθ
                  have h_log_sq_le : |Real.log θ| ≤ 4 * θ^(-1 / 4 : ℝ) := by
                    rw [ abs_of_nonpos (Real.log_nonpos hθ.1.le hθ.2) ]
                    rw [ Real.rpow_def_of_pos hθ.1 ]
                    nlinarith [Real.add_one_le_exp (Real.log θ * (-1 / 4)),
                               Real.log_le_sub_one_of_pos hθ.1]
                  exact le_trans (pow_le_pow_left₀ (abs_nonneg _) h_log_sq_le 2) (by rw [ mul_pow ]; norm_num [ sq, ← Real.rpow_add hθ.1 ])
                refine MeasureTheory.Integrable.mono'
                  (g := fun θ => h_log_sq_le.choose * θ ^ (-1 / 2 : ℝ)) ?_ ?_ ?_
                exacts [by exact h_integrable.const_mul _,
                        by exact Measurable.aestronglyMeasurable (by exact Measurable.pow_const (Real.measurable_log) _),
                        Filter.eventually_of_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioc) fun x hx => by simpa [abs_mul,
                                                                                                                         abs_of_nonneg (Real.rpow_nonneg hx.1.le _)] using h_log_sq_le.choose_spec x hx]
              have h_integrable : MeasureTheory.IntegrableOn (fun θ => (Real.log θ) ^ 2) (Set.Ioc 1 (Real.pi / 2)) := by
                exact ContinuousOn.integrableOn_Icc (by exact ContinuousOn.pow (Real.continuousOn_log.mono <| by norm_num) _) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self
              convert MeasureTheory.IntegrableOn.union ‹IntegrableOn (fun θ => Real.log θ ^ 2) (Set.Ioc 0 1) volume› ‹IntegrableOn (fun θ => Real.log θ ^ 2) (Set.Ioc 1 (Real.pi / 2)) volume› using 1; rw [ Set.Ioc_union_Ioc_eq_Ioc ] <;> linarith [ Real.pi_gt_three ]
            exact h_integrable.mono_set <| Set.Ioo_subset_Ioc_self
          have h_integrable : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (Real.log (Real.sin θ)) ^ 2 ≤ 4 * (Real.log θ) ^ 2 + 4 * (Real.log 2) ^ 2 := by
            intros θ hθ
            have h_sin_le : Real.sin θ ≥ θ / 2 := by
              have := Real.mul_le_sin hθ.1.le hθ.2.le
              rw [div_mul_eq_mul_div,
                  div_le_iff₀] at this <;> nlinarith [ Real.pi_gt_three, Real.pi_le_four, hθ.1, hθ.2 ]
            have h_log_sin_le : Real.log (Real.sin θ) ≥ Real.log (θ / 2) := by
              exact Real.log_le_log (div_pos hθ.1 zero_lt_two) h_sin_le
            rw [ Real.log_div hθ.1.ne' two_ne_zero ] at h_log_sin_le
            nlinarith [sq_nonneg (Real.log θ + Real.log 2),
                       Real.log_nonpos (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [ Real.pi_pos, hθ.2 ])) (Real.sin_le_one θ)]
          refine MeasureTheory.Integrable.mono'
            (g := fun θ => 4 * Real.log θ ^ 2 + 4 * Real.log 2 ^ 2) ?_ ?_ ?_
          · exact MeasureTheory.Integrable.add (MeasureTheory.Integrable.const_mul ‹_› _) (MeasureTheory.integrable_const _)
          · exact Measurable.aestronglyMeasurable (by exact Measurable.pow_const (Measurable.log (Real.continuous_sin.measurable)) _)
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using by rw [ Real.norm_of_nonneg (sq_nonneg _) ]; exact h_integrable x hx
        have h_integrable : MeasureTheory.IntegrableOn (fun θ => (Real.log (Real.sin (θ / 2))) ^ 2) (Set.Ioo 0 Real.pi) := by
          rw [ ← MeasureTheory.integrable_indicator_iff (measurableSet_Ioo) ] at *
          refine (h_integrable.comp_smul (show (2⁻¹ : ℝ) ≠ 0 by norm_num)).congr ?_
          filter_upwards with x
          have hscale : (2⁻¹ : ℝ) • x = x / 2 := by
            rw [smul_eq_mul]
            ring
          by_cases hx : x ∈ Set.Ioo 0 Real.pi
          · have hx' : (2⁻¹ : ℝ) • x ∈ Set.Ioo 0 (Real.pi / 2) := by
              rw [hscale]
              rcases hx with ⟨hxlo, hxhi⟩
              constructor <;> linarith
            have hx'_mul : 0 < 2⁻¹ * x ∧ 2⁻¹ * x < Real.pi / 2 := by
              simpa [smul_eq_mul] using hx'
            simp [Set.indicator, Set.mem_Ioo, hx, hx'_mul]
            rw [show 2⁻¹ * x = x / 2 by ring]
          · have hx' : (2⁻¹ : ℝ) • x ∉ Set.Ioo 0 (Real.pi / 2) := by
              intro hx'
              apply hx
              rw [hscale] at hx'
              rcases hx' with ⟨hxlo, hxhi⟩
              constructor <;> linarith
            have hx'_mul : ¬(0 < 2⁻¹ * x ∧ 2⁻¹ * x < Real.pi / 2) := by
              simpa [smul_eq_mul] using hx'
            have hx'_mul' : ¬(0 < x ∧ 2⁻¹ * x < Real.pi / 2) := by
              intro hxcond
              apply hx
              constructor <;> linarith
            simp [Set.indicator, Set.mem_Ioo, hx, hx'_mul']
        have h_integrable : MeasureTheory.IntegrableOn (fun θ => (Real.log (Real.sin (θ / 2))) ^ 2) (Set.Ioo (-Real.pi) 0) := by
          rw [ ← MeasureTheory.integrable_indicator_iff (measurableSet_Ioo) ] at *
          refine h_integrable.comp_neg.congr ?_
          filter_upwards with x
          by_cases hx : x ∈ Set.Ioo (-Real.pi) 0
          · have hx' : -x ∈ Set.Ioo 0 Real.pi := by
              rcases hx with ⟨hxlo, hxhi⟩
              constructor <;> linarith
            simp [Set.indicator, hx, hx', Real.sin_neg, Real.log_neg_eq_log,
              neg_div]
          · have hx' : -x ∉ Set.Ioo 0 Real.pi := by
              intro hx'
              apply hx
              rcases hx' with ⟨hxlo, hxhi⟩
              constructor <;> linarith
            simp [Set.indicator, hx, hx']
        have h_integrable : MeasureTheory.IntegrableOn (fun θ => (Real.log (Real.sin (θ / 2))) ^ 2) (Set.Ioo (-Real.pi) Real.pi) := by
          have h_union : Set.Ioo (-Real.pi) Real.pi = Set.Ioo (-Real.pi) 0 ∪ Set.Ioo 0 Real.pi ∪ {0}
              := by
            ext x
            simp
            exact ⟨fun hx => by cases lt_trichotomy x 0 <;> tauto, fun hx => by rcases hx with (rfl | ⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩) <;> constructor <;> linarith [ Real.pi_pos ]⟩
          rw [ h_union ]
          exact MeasureTheory.IntegrableOn.union (MeasureTheory.IntegrableOn.union h_integrable ‹_›) (by norm_num)
        aesop
      exact MeasureTheory.Integrable.add (MeasureTheory.integrable_const _)
        (MeasureTheory.Integrable.const_mul
          (by simpa [MeasureTheory.IntegrableOn] using h_log_sin_sq_integrable) _)
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.pow_const ?_ 2
      refine Measurable.norm ?_
      refine Measurable.sub ?_ ?_
      · fun_prop
      · fun_prop
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with θ hθ
      -- The norm of the logarithm term is bounded by π^2 + (sum of reciprocals)^2.
      have h_log_bound : ‖-Complex.log (1 - Complex.exp (-(θ : ℂ) * I))‖ ^ 2 ≤ Real.pi ^ 2 + (Real.log (1 / |Real.sin (θ / 2)|)) ^ 2 := by
        norm_num [ Complex.normSq, Complex.sq_norm, Complex.log_re, Complex.log_im ]
        -- The norm of $1 - e^{-i\theta}$ is $2|\sin(\theta/2)|$.
        have h_norm : ‖1 - Complex.exp (-(θ : ℂ) * I)‖ = 2 * |Real.sin (θ / 2)| := by
          norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ]
          rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring_nf
          nlinarith [ Real.cos_sq' θ ]
        by_cases h : Real.sin (θ / 2) = 0 <;> simp_all +decide [ Complex.arg ]
        · positivity
        · split_ifs <;> norm_num [ Complex.exp_re, Complex.exp_im ] at *
          · rw [ Real.log_mul (by positivity) (by positivity), Real.log_abs ]; ring_nf; norm_num
            have h_arcsin_bound : Real.arcsin (Real.sin θ * |Real.sin (θ * (1 / 2))|⁻¹ * (1 / 2)) ^ 2 ≤ (Real.pi / 2) ^ 2 := by
              nlinarith [Real.arcsin_le_pi_div_two (Real.sin θ * |Real.sin (θ * (1 / 2))|⁻¹ * (1 / 2)),
                         Real.neg_pi_div_two_le_arcsin (Real.sin θ * |Real.sin (θ * (1 / 2))|⁻¹ * (1 / 2))]
            have h_log_bound : Real.log (Real.sin (θ * (1 / 2))) ≤ 0 := by
              exact Real.log_nonpos (abs_nonneg _) (abs_le.mpr ⟨by linarith [ Real.neg_one_le_sin (θ * (1 / 2)) ], by linarith [ Real.sin_le_one (θ * (1 / 2)) ]⟩) |> le_trans (by rw [ Real.log_abs ])
            nlinarith [Real.pi_gt_three, Real.log_le_sub_one_of_pos zero_lt_two,
                       Real.log_pos one_lt_two]
          · linarith [ Real.cos_le_one θ ]
          · nlinarith [ Real.cos_sq' θ ]
      -- The norm of the sum term is bounded by the square of the sum of reciprocals.
      have h_sum_bound : ‖∑ k ∈ Finset.range n, Complex.exp (-(k + 1 : ℕ) * θ * I) / (k + 1 : ℕ)‖ ^ 2 ≤ (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1)) ^ 2 := by
        have hnorm :
            ‖∑ k ∈ Finset.range n,
                Complex.exp (-(k + 1 : ℕ) * θ * I) / (k + 1 : ℕ)‖ ≤
              ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) := by
          calc
            ‖∑ k ∈ Finset.range n,
                Complex.exp (-(k + 1 : ℕ) * θ * I) / (k + 1 : ℕ)‖
                ≤ ∑ k ∈ Finset.range n,
                    ‖Complex.exp (-(k + 1 : ℕ) * θ * I) / (k + 1 : ℕ)‖ :=
              norm_sum_le _ _
            _ = ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              have hkpos : (0 : ℝ) < k + 1 := by positivity
              rw [norm_div]
              have hexp : ‖Complex.exp (-(k + 1 : ℕ) * θ * I)‖ = 1 := by
                rw [Complex.norm_exp]
                norm_num
              rw [hexp]
              rw [RCLike.norm_natCast]
              norm_num
        exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      norm_num [ h_fun ] at *
      have := norm_add_le (-log (1 - Complex.exp (- (θ * I)))) (-∑ x ∈ Finset.range n, Complex.exp ((-1 + -x) * θ * I) / (x + 1)); norm_num at *
      calc
        ‖-log (1 - cexp (-(θ * I))) +
            -∑ x ∈ Finset.range n, cexp ((-1 + -x) * θ * I) / (x + 1)‖ ^ 2
            ≤ (‖log (1 - cexp (-(θ * I)))‖ +
              ‖∑ x ∈ Finset.range n, cexp ((-1 + -x) * θ * I) / (x + 1)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
        _ ≤ 2 * ‖log (1 - cexp (-(θ * I)))‖ ^ 2 +
            2 * ‖∑ x ∈ Finset.range n, cexp ((-1 + -x) * θ * I) / (x + 1)‖ ^ 2 := by
          simpa [mul_add, two_mul, add_assoc, add_comm, add_left_comm] using
            add_sq_le (a := ‖log (1 - cexp (-(θ * I)))‖)
              (b := ‖∑ x ∈ Finset.range n,
                cexp ((-1 + -x) * θ * I) / (x + 1)‖)
        _ ≤ (Real.pi ^ 2 + (∑ x ∈ Finset.range n, (↑x + 1)⁻¹) ^ 2) * 2 +
            2 * Real.log (Real.sin (θ / 2)) ^ 2 := by
          nlinarith [h_log_bound, h_sum_bound]
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.pow_const ?_ 2
    refine Measurable.norm (Measurable.mul ?_ ?_)
    · refine Continuous.measurable ?_
      refine Complex.continuous_exp.comp ?_
      refine Continuous.sub ?_ continuous_const
      refine continuous_neg.comp ?_
      fun_prop
    · refine Measurable.sub ?_ ?_
      · fun_prop
      · fun_prop
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with θ hθ
    norm_num [ mul_pow ]
    gcongr
    refine le_csSup ?_ ?_
    · refine IsCompact.bddAbove (isCompact_Icc.image ?_)
      unfold g_fun; continuity
    · exact ⟨θ, ⟨hθ.1.le, hθ.2.le⟩, rfl⟩

/-
**Combined identity + Cauchy-Schwarz bound**
-/
lemma atkinson_cs_bound {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (2 * Real.pi) ^ 2 ≤
      (∫ θ in (-Real.pi)..Real.pi, (‖g_deriv_fun z θ‖ ^ 2 : ℝ)) *
      (∫ θ in (-Real.pi)..Real.pi,
        (‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 : ℝ)) := by
  convert atkinson_integral_identity hn z hz1 hz |> fun h => cauchy_schwarz_intervalIntegral _ _ (-Real.pi) Real.pi (by linarith [ Real.pi_pos ]) _ _ _ _ using 1
  · have := atkinson_integral_identity hn z hz1 hz; simp_all +decide [ mul_assoc ]
    rw [ abs_of_nonneg Real.pi_pos.le ]
  · exact Continuous.intervalIntegrable (by unfold g_deriv_fun; fun_prop) _ _
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    have hii := exp_g_h_sq_intervalIntegrable hn z hz
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])] at hii
    refine Integrable.mono' (hii.add (integrable_const (1 : ℝ)))
      (by unfold g_fun h_fun; measurability) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ _
    simp only [Pi.add_apply]
    nlinarith [norm_nonneg (Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ),
               sq_nonneg (‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ - 1)]
  · convert g_deriv_sq_intervalIntegrable z using 1
  · exact exp_g_h_sq_intervalIntegrable hn z hz

/-
**Parseval bound**: ∫|g'(θ)|² dθ ≤ 2π·n·s².

Since g'(θ) = -i·∑ s_k exp(ikθ), orthogonality of complex exponentials gives
∫_{-π}^{π} |g'|² = 2π·∑|s_k|², and |s_k| ≤ s yields the bound.
-/
lemma parseval_g_deriv_bound {n : ℕ} (z : Fin n → ℂ)
    {s : ℝ} (hs_max : ∀ k : Fin n, ‖powerSum z (k.val + 1)‖ ≤ s) :
    ∫ θ in (-Real.pi)..Real.pi, (‖g_deriv_fun z θ‖ ^ 2 : ℝ) ≤
      2 * Real.pi * (↑n : ℝ) * s ^ 2 := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [g_deriv_fun]
  let p : Polynomial ℂ := ∑ k : Fin n, Polynomial.monomial k.val (powerSum z (k.val + 1))
  let F : ℝ → ℝ := fun θ => ‖p.eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2
  have h_eval : ∀ θ : ℝ, ‖g_deriv_fun z θ‖ ^ 2 = F θ := by
    intro θ
    dsimp [F, p, g_deriv_fun]
    have hsum :
        (∑ k : Fin n, powerSum z (k.val + 1) *
            Complex.exp ((↑(k.val + 1 : ℕ) : ℂ) * ↑θ * I)) =
          Complex.exp ((θ : ℂ) * I) *
            (∑ k : Fin n,
              (Polynomial.monomial k.val (powerSum z (k.val + 1))).eval
                (Complex.exp ((θ : ℂ) * I))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [Polynomial.eval_monomial]
      calc
        powerSum z (↑k + 1) * Complex.exp ((↑↑k + 1) * ↑θ * I)
            = powerSum z (↑k + 1) *
                (Complex.exp ((θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) ^ k.val) := by
              congr 1
              rw [← Complex.exp_nat_mul, ← Complex.exp_add]
              congr 1
              ring_nf
        _ = Complex.exp ((θ : ℂ) * I) *
              (powerSum z (↑k + 1) * Complex.exp ((θ : ℂ) * I) ^ k.val) := by
              ring
    rw [hsum]
    rw [← Polynomial.eval_finsetSum]
    simp [Complex.norm_exp_ofReal_mul_I, Complex.norm_I]
  have h_periodic : Function.Periodic F (2 * Real.pi) := by
    intro θ
    dsimp [F]
    have hexp :
        Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * I) =
          Complex.exp ((θ : ℂ) * I) :=
      by simpa [map_add, map_mul] using (Complex.exp_mul_I_periodic (θ : ℂ))
    rw [hexp]
  have h_shift :
      ∫ θ in (-Real.pi)..Real.pi, F θ =
        ∫ θ in (0 : ℝ)..2 * Real.pi, F θ := by
    simpa [two_mul, add_assoc, add_comm, add_left_comm, sub_eq_add_neg] using
      h_periodic.intervalIntegral_add_eq (-Real.pi) 0
  have h_circle :
      Real.circleAverage (fun w : ℂ => ‖p.eval w‖ ^ 2) 0 1 =
        (2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..2 * Real.pi, F θ := by
    simp [Real.circleAverage_def, F, circleMap, smul_eq_mul]
  have h_parseval :
      ∫ θ in (0 : ℝ)..2 * Real.pi, F θ =
        2 * Real.pi * ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 := by
    have h := (Polynomial.sum_sq_norm_coeff_eq_circleAverage p).symm
    rw [h_circle] at h
    have htwo : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    calc
      ∫ θ in (0 : ℝ)..2 * Real.pi, F θ =
          2 * Real.pi * ((2 * Real.pi)⁻¹ *
            ∫ θ in (0 : ℝ)..2 * Real.pi, F θ) := by
            field_simp [htwo]
      _ = 2 * Real.pi * ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 := by
            rw [h]
  have h_coeff_zero_of_le : ∀ i : ℕ, n ≤ i → p.coeff i = 0 := by
    intro i hi
    dsimp [p]
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero ?_
    intro k hk
    rw [Polynomial.coeff_monomial]
    simp [show ¬ k.val = i by exact fun hki => by omega]
  have h_support_lt : ∀ i ∈ p.support, i < n := by
    intro i hi
    by_contra hni
    exact (Polynomial.mem_support_iff.mp hi) (h_coeff_zero_of_le i (not_lt.mp hni))
  have h_coeff_bound : ∀ i ∈ p.support, ‖p.coeff i‖ ^ 2 ≤ s ^ 2 := by
    intro i hi
    have hi_lt := h_support_lt i hi
    have hcoeff : p.coeff i = powerSum z (i + 1) := by
      dsimp [p]
      rw [Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single (⟨i, hi_lt⟩ : Fin n)]
      · simp
      · intro k hk hki
        rw [Polynomial.coeff_monomial]
        simp [show ¬ k.val = i by
          intro h
          exact hki (Fin.ext h)]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    have hs_nonneg : 0 ≤ s := (norm_nonneg _).trans (by simpa [hcoeff] using hs_max (⟨i, hi_lt⟩ : Fin n))
    rw [hcoeff]
    exact pow_le_pow_left₀ (norm_nonneg _) (hs_max (⟨i, hi_lt⟩ : Fin n)) 2
  have h_sum_bound :
      ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 ≤ (n : ℝ) * s ^ 2 := by
    calc
      ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2
          ≤ ∑ i ∈ p.support, s ^ 2 := by
            exact Finset.sum_le_sum fun i hi => h_coeff_bound i hi
      _ = (p.support.card : ℝ) * s ^ 2 := by simp [mul_comm]
      _ ≤ (n : ℝ) * s ^ 2 := by
        have hcard : p.support.card ≤ n := by
          have hcard' : p.support.card ≤ (Finset.range n).card := by
            refine Finset.card_le_card ?_
            intro i hi
            simpa [Finset.mem_range] using h_support_lt i hi
          simpa using hcard'
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg s)
  rw [intervalIntegral.integral_congr (fun θ hθ => h_eval θ), h_shift, h_parseval]
  have htwo_nonneg : 0 ≤ (2 * Real.pi : ℝ) :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left h_sum_bound htwo_nonneg

/-
**Integral estimate**: ∫|exp(g-g(0))·h|² < (2π/n)·exp(2πs)·(1+exp(4s)/(1-4s)).

The proof splits [-π,π] into the near region |θ| ≤ π/n (where |g(θ)-g(0)| ≤ πs
by the triangle inequality) and the far region |θ| > π/n (where |h(θ)| ≤ π/(n|θ|)
by Abel summation), then estimates each piece:
- Near: ≤ exp(2πs) · ∫|h|² ≤ exp(2πs) · 2π/n (using Parseval for h)
- Far: ≤ exp(2s(π+2)) · ∫ (n|θ|/π)^{4s-2} dθ < exp(2πs+4s) · π/(n(1-4s))
-/
/-! ### Helper lemmas for the integral estimate -/

/-! ### Sub-lemmas for the integral estimate -/

/-
For |θ| ≤ π/n, the deviation |g(θ)-g(0)| ≤ πs.
This follows from |e^{ikθ}-1| ≤ k|θ| and the triangle inequality.
-/
private lemma g_deviation_near {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    {s : ℝ} (hs_pos : 0 ≤ s) (hs_max : ∀ k : Fin n, ‖powerSum z (k.val + 1)‖ ≤ s)
    {θ : ℝ} (hθ : |θ| ≤ Real.pi / n) :
    ‖g_fun z θ - g_fun z 0‖ ≤ Real.pi * s := by
  -- Apply the triangle inequality to the sum defining g_fun z θ - g_fun z 0.
  have h_triangle : ‖g_fun z θ - g_fun z 0‖ ≤ ∑ k : Fin n, ‖(powerSum z (k.val + 1) / (k.val + 1 : ℂ)) * (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1)‖ := by
    unfold g_fun
    norm_num [ mul_sub ]
    rw [ neg_add_eq_sub, ← Finset.sum_sub_distrib ]
    convert norm_sum_le _ _ using 2; norm_num [ norm_sub_rev ]
  -- Each term in the sum is bounded by $s \cdot |\theta|$.
  have h_term_bound : ∀ k : Fin n, ‖(powerSum z (k.val + 1) / (k.val + 1 : ℂ)) * (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1)‖ ≤ s * |θ| := by
    intro k
    have h_term_bound : ‖Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1‖ ≤ (k.val + 1 : ℝ) * |θ| := by
      have h_exp_bound : ∀ x : ℝ, ‖Complex.exp (x * I) - 1‖ ≤ |x| := by
        -- Use the fact that $|e^{ix} - 1| = 2|\sin(x/2)|$ and $|\sin(x/2)| \leq |x/2|$ for all $x$.
        have h_sin_bound : ∀ x : ℝ, ‖Complex.exp (x * I) - 1‖ = 2 * |Real.sin (x / 2)| := by
          norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ]
          intro x; rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring_nf
          nlinarith [ Real.cos_sq' x ]
        -- Use the fact that $|\sin(x/2)| \leq |x/2|$ for all $x$.
        have h_sin_le : ∀ x : ℝ, |Real.sin (x / 2)| ≤ |x / 2| :=
          fun x => Real.abs_sin_le_abs
        exact fun x => by rw [ h_sin_bound ]; exact le_trans (mul_le_mul_of_nonneg_left (h_sin_le x) zero_le_two) (by norm_num [ abs_div, mul_div_cancel₀ ])
      convert h_exp_bound ((k + 1) * θ) using 1 <;> norm_num [ abs_mul, abs_of_nonneg, add_nonneg ]
    norm_num at *
    rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast <;> norm_num
    nlinarith [hs_max k, norm_nonneg (powerSum z (k + 1)),
               norm_nonneg (Complex.exp ((k + 1) * θ * I) - 1)]
  refine le_trans h_triangle <| le_trans (Finset.sum_le_sum fun _ _ => h_term_bound _) ?_
  norm_num [ mul_comm s ]
  rw [ le_div_iff₀ ] at hθ <;> first | positivity | nlinarith

/-
Orthogonality of exponentials: ∫_{-π}^{π} e^{imθ} dθ = 2π if m = 0, and 0 otherwise.
-/
private lemma integral_exp_orthogonal (m : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp (m * θ * I) =
      if m = 0 then 2 * Real.pi else 0 := by
  by_cases hm : m = 0 <;> simp +decide [ hm ]
  · ring
  · have := @integral_exp_mul_complex (-Real.pi) Real.pi
    convert @this (m * I) (mul_ne_zero (Int.cast_ne_zero.mpr hm) Complex.I_ne_zero) using 3 <;> ring_nf
    norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]

/-
For 0 < r < 1, the r-approximation g_r equals the tail series.
-/
private lemma g_r_eq_tail_series (n : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    -Complex.log (1 - ↑r * Complex.exp (-↑θ * I)) -
      ∑ k ∈ Finset.range n, (↑r * Complex.exp (-↑θ * I)) ^ (k + 1) / (↑(k + 1) : ℂ) =
    ∑' k, (↑r * Complex.exp (-↑θ * I)) ^ (k + n + 1) / (↑(k + n + 1) : ℂ) := by
  have h_taylor : HasSum (fun k : ℕ => (r * Complex.exp (-θ * I)) ^ (k + 1) / (k + 1 : ℂ)) (-Complex.log (1 - r * Complex.exp (-θ * I))) := by
    have h_taylor : HasSum (fun k : ℕ => (r * Complex.exp (-θ * I)) ^ k / (k : ℂ)) (-Complex.log (1 - r * Complex.exp (-θ * I))) := by
      convert Complex.hasSum_taylorSeries_neg_log _ using 1
      simpa [ Complex.norm_exp, abs_of_pos hr ] using hr1
    simpa using (hasSum_nat_add_iff' 1).2 h_taylor
  rw [ ← h_taylor.tsum_eq, ← Summable.sum_add_tsum_nat_add ]
  focus
    norm_cast
  exacts [ by rw [ add_sub_cancel_left ], h_taylor.summable ]

/-
Parseval for the r-approximation: ∫|g_r|² = 2π·∑ r^{2k}/k².
-/
private lemma g_r_parseval (n : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∫ θ in (-Real.pi)..Real.pi,
      (‖∑' k, (↑r * Complex.exp (-↑θ * I)) ^ (k + n + 1) / (↑(k + n + 1) : ℂ)‖ ^ 2 : ℝ) =
    2 * Real.pi * ∑' k, (r ^ (2 * (k + n + 1)) / (↑(k + n + 1) : ℝ) ^ 2) := by
  -- By Fubini's theorem, we can interchange the sum and the integral.
  have h_fubini : ∫ θ in (-Real.pi)..Real.pi, ∑' k : ℕ, ∑' l : ℕ, (r ^ (k + n + 1) / (k + n + 1 : ℂ)) * (r ^ (l + n + 1) / (l + n + 1 : ℂ)) * Complex.exp (-(k - l) * θ * I) = ∑' k : ℕ, ∑' l : ℕ, (r ^ (k + n + 1) / (k + n + 1 : ℂ)) * (r ^ (l + n + 1) / (l + n + 1 : ℂ)) * ∫ θ in (-Real.pi)..Real.pi, Complex.exp (-(k - l) * θ * I) := by
    rw [intervalIntegral.integral_of_le (by linarith [ Real.pi_pos ]), MeasureTheory.integral_tsum]
    · refine tsum_congr fun k => ?_
      rw [ MeasureTheory.integral_tsum ]
      · norm_num [intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
                  MeasureTheory.integral_const_mul]
      · exact fun i => Continuous.aestronglyMeasurable (by continuity)
      · refine ne_of_lt (lt_of_le_of_lt
          (ENNReal.tsum_le_tsum
            (g := fun i =>
              ENNReal.ofReal
                (r ^ (k + n + 1) / (k + n + 1) *
                  r ^ (i + n + 1) / (i + n + 1) * (2 * Real.pi)))
            fun i => ?_) ?_)
        · refine le_trans
            (MeasureTheory.lintegral_mono
              (g := fun x =>
                ENNReal.ofReal
                  (r ^ (k + n + 1) / (k + n + 1) *
                    r ^ (i + n + 1) / (i + n + 1)))
              fun x => ?_) ?_
          · rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num
            · norm_num [ abs_of_pos hr, Complex.norm_exp ]; ring_nf
              norm_cast
            · exact not_eq_of_beq_eq_false rfl
            · positivity
          · simp +zetaDelta at *
            rw [ ← ENNReal.ofReal_mul (by positivity) ]; ring_nf; norm_num
        · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num
          · exact fun _ => by positivity
          · have hbase :
                Summable (fun i : ℕ => r ^ (i + n + 1) / (i + n + 1 : ℝ)) := by
              exact Summable.of_nonneg_of_le
                (f := fun i : ℕ => r ^ (i + n + 1))
                (g := fun i : ℕ => r ^ (i + n + 1) / (i + n + 1 : ℝ))
                (fun _ => by positivity)
                (fun i => by
                  exact div_le_self
                    (by positivity : 0 ≤ r ^ (i + n + 1))
                    (by norm_cast; omega : (1 : ℝ) ≤ (i + n + 1 : ℝ)))
                (Summable.comp_injective
                  (summable_geometric_of_lt_one hr.le hr1)
                  (by
                    intro a b h
                    have hnat : a + n + 1 = b + n + 1 := by exact_mod_cast h
                    omega))
            refine
              (Summable.mul_right (2 * Real.pi)
                (Summable.mul_left (r ^ (k + n + 1) / (k + n + 1)) hbase)).congr ?_
            intro a
            ring
    · intro i
      refine Continuous.aestronglyMeasurable ?_
      refine continuous_tsum
        (u := fun k =>
          (r ^ (i + n + 1) / (i + n + 1)) *
            (r ^ (k + n + 1) / (k + n + 1))) ?_ ?_ ?_
      · fun_prop
      · exact Summable.mul_left _ <| Summable.of_nonneg_of_le
          (f := fun k : ℕ => r ^ (k + n + 1))
          (g := fun k : ℕ => r ^ (k + n + 1) / (k + n + 1 : ℝ))
          (fun _ => by positivity)
          (fun k => by
            exact div_le_self
              (by positivity : 0 ≤ r ^ (k + n + 1))
              (by norm_cast; omega : (1 : ℝ) ≤ (k + n + 1 : ℝ)))
          (Summable.comp_injective
            (summable_geometric_of_lt_one (by positivity) hr1)
            (by intro a b h; norm_num at h; omega))
      · norm_num [ Complex.norm_exp, abs_of_pos hr ]
        norm_cast; norm_num
    · refine ne_of_lt (lt_of_le_of_lt
        (ENNReal.tsum_le_tsum
          (g := fun i =>
            ENNReal.ofReal
              (∑' l : ℕ,
                (r ^ (i + n + 1) / (i + n + 1)) *
                  (r ^ (l + n + 1) / (l + n + 1)) * (2 * Real.pi)))
          fun i => ?_) ?_)
      · refine le_trans
          (MeasureTheory.lintegral_mono
            (g := fun x =>
              ENNReal.ofReal
                (∑' l : ℕ,
                  (r ^ (i + n + 1) / (i + n + 1)) *
                    (r ^ (l + n + 1) / (l + n + 1))))
            fun x => ?_) ?_
        · rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num
          · convert norm_tsum_le_tsum_norm _ <;> norm_num [ Complex.norm_exp ]
            · norm_cast; norm_num [ abs_of_pos hr ]
            · simpa [abs_of_pos hr] using
                (Summable.mul_left
                  (r ^ (i + n + 1) / ‖(i : ℂ) + (n : ℂ) + 1‖)
                  (Summable.of_nonneg_of_le
                    (f := fun l : ℕ => r ^ (l + n + 1))
                    (g := fun l : ℕ => r ^ (l + n + 1) /
                      ‖(l : ℂ) + (n : ℂ) + 1‖)
                    (fun _ => by positivity)
                    (fun l => by
                      exact div_le_self
                        (by positivity : 0 ≤ r ^ (l + n + 1))
                        (by
                          rw [show ((l : ℂ) + (n : ℂ) + 1) =
                              ((l + n + 1 : ℝ) : ℂ) by norm_num]
                          rw [Complex.norm_of_nonneg
                            (by positivity : 0 ≤ (l + n + 1 : ℝ))]
                          norm_cast
                          omega))
                    (Summable.comp_injective
                      (summable_geometric_of_lt_one (by positivity) hr1)
                      (by
                        intro a b h
                        have hnat : a + n + 1 = b + n + 1 := by exact_mod_cast h
                        omega))))
          · exact tsum_nonneg fun _ => by positivity
        · simp +decide [ mul_assoc, mul_comm, mul_left_comm, tsum_mul_left, tsum_mul_right ]
          rw [ ← ENNReal.ofReal_mul (by positivity) ]; ring_nf; norm_num
      · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num [ mul_assoc, tsum_mul_left, tsum_mul_right ]
        · exact fun _ => mul_nonneg (div_nonneg (pow_nonneg hr.le _) (by positivity)) (mul_nonneg (tsum_nonneg fun _ => div_nonneg (pow_nonneg hr.le _) (by positivity)) (by positivity))
        · simpa [mul_assoc, mul_comm, mul_left_comm] using
            (Summable.mul_right
              ((∑' l : ℕ, r ^ (l + n + 1) / (l + n + 1)) * (2 * Real.pi))
              (Summable.of_nonneg_of_le (fun _ => by positivity)
                (fun i => by
                  exact div_le_self
                    (by positivity : 0 ≤ r ^ (i + n + 1))
                    (by norm_cast; omega : (1 : ℝ) ≤ (i + n + 1 : ℝ)))
                (Summable.comp_injective
                  (summable_geometric_of_lt_one hr.le hr1)
                  (by intro a b h; norm_num at h; omega))))
  convert congr_arg Complex.re h_fubini using 1
  · rw [ intervalIntegral.integral_congr fun x hx => ?_ ]
    rotate_left
    focus
      use fun x => Complex.re (∑' k : ℕ, ∑' l : ℕ, (r ^ (k + n + 1) / (k + n + 1 : ℂ)) * (r ^ (l + n + 1) / (l + n + 1 : ℂ)) * Complex.exp (- (k - l) * x * I))
    · have h_norm_sq : ‖∑' k : ℕ, (r * Complex.exp (-x * I)) ^ (k + n + 1) / (k + n + 1 : ℂ)‖ ^ 2 = (∑' k : ℕ, (r * Complex.exp (-x * I)) ^ (k + n + 1) / (k + n + 1 : ℂ)) * (∑' l : ℕ, (r * Complex.exp (x * I)) ^ (l + n + 1) / (l + n + 1 : ℂ)) := by
        have h_norm_sq : ‖∑' k : ℕ, (r * Complex.exp (-x * I)) ^ (k + n + 1) / (k + n + 1 : ℂ)‖ ^ 2 = (∑' k : ℕ, (r * Complex.exp (-x * I)) ^ (k + n + 1) / (k + n + 1 : ℂ)) * starRingEnd ℂ (∑' k : ℕ, (r * Complex.exp (-x * I)) ^ (k + n + 1) / (k + n + 1 : ℂ)) := by
          rw [ Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow ]
        convert h_norm_sq using 2
        rw [ Complex.conj_tsum ]; congr; ext; norm_num [ Complex.exp_neg, Complex.conj_ofReal ]
        norm_num [ Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.norm_exp ]
      convert congr_arg Complex.re h_norm_sq using 1
      · norm_cast
      · rw [ ← tsum_mul_right ]; congr; ext k; rw [ ← tsum_mul_left ]; congr; ext l; ring_nf
        norm_num [ mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add ]; ring_nf
        norm_num
    · rw [intervalIntegral.integral_of_le (by linarith [ Real.pi_pos ]),
          intervalIntegral.integral_of_le (by linarith [ Real.pi_pos ])]
      convert integral_re _
      any_goals tauto
      refine Continuous.integrableOn_Ioc ?_
      refine continuous_tsum
        (u := fun k => (r ^ (k + n + 1) / (k + n + 1)) *
          ∑' l : ℕ, (r ^ (l + n + 1) / (l + n + 1))) ?_ ?_ ?_
      · intro i
        refine continuous_tsum
          (u := fun k => (r ^ (i + n + 1) / (i + n + 1)) *
            (r ^ (k + n + 1) / (k + n + 1))) ?_ ?_ ?_
        · fun_prop
        · refine Summable.mul_left
            (r ^ (i + n + 1) / (i + n + 1)) ?_
          exact Summable.of_nonneg_of_le
            (fun _ => div_nonneg (pow_nonneg hr.le _) (by positivity))
            (fun k => by
              exact div_le_self
                (pow_nonneg hr.le _)
                (by norm_cast; omega : (1 : ℝ) ≤ (k + n + 1 : ℝ)))
            (Summable.comp_injective
              (summable_geometric_of_lt_one hr.le hr1)
              (by intro a b h; norm_num at h; omega))
        · norm_num [ Complex.norm_exp, abs_of_pos hr ]
          norm_cast; norm_num
      · refine Summable.mul_right
          (∑' l : ℕ, r ^ (l + n + 1) / (l + n + 1)) ?_
        exact Summable.of_nonneg_of_le
          (fun k => div_nonneg (pow_nonneg hr.le _) (by positivity))
          (fun k => by
            exact div_le_self
              (pow_nonneg hr.le _)
              (by norm_cast; omega : (1 : ℝ) ≤ (k + n + 1 : ℝ)))
          (Summable.comp_injective
            (summable_geometric_of_lt_one hr.le hr1)
            (by intro a b h; norm_num at h; omega))
      · intro k x
        refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
        · norm_num [ Complex.norm_exp ]
          simpa [abs_of_pos hr] using
            (Summable.mul_left
              (r ^ (k + n + 1) / ‖(k : ℂ) + (n : ℂ) + 1‖)
              (Summable.of_nonneg_of_le
                (f := fun l : ℕ => r ^ (l + n + 1))
                (g := fun l : ℕ => r ^ (l + n + 1) /
                  ‖(l : ℂ) + (n : ℂ) + 1‖)
                (fun _ => by positivity)
                (fun l => by
                  exact div_le_self
                    (by positivity : 0 ≤ r ^ (l + n + 1))
                    (by
                      rw [show ((l : ℂ) + (n : ℂ) + 1) =
                          ((l + n + 1 : ℝ) : ℂ) by norm_num]
                      rw [Complex.norm_of_nonneg
                        (by positivity : 0 ≤ (l + n + 1 : ℝ))]
                      norm_cast
                      omega))
                (Summable.comp_injective
                  (summable_geometric_of_lt_one (by positivity) hr1)
                  (by
                    intro a b h
                    have hnat : a + n + 1 = b + n + 1 := by exact_mod_cast h
                    omega))))
        · norm_num [ Complex.norm_exp, abs_of_pos hr ]
          norm_cast
          rw [tsum_mul_left]
  · rw [ tsum_congr fun k => tsum_eq_single k fun l hl => ?_ ]
    · norm_num [ ← sq, ← mul_pow ]
      norm_cast
      norm_num [ pow_mul', div_pow, mul_pow, tsum_mul_right ]
      let T : ℕ → ℝ :=
        fun k => (r ^ (k + n + 1)) ^ 2 / ((k : ℝ) + (n : ℝ) + 1) ^ 2
      change 2 * Real.pi * ∑' k : ℕ, T k =
        (∑' k : ℕ, T k) * (Real.pi + Real.pi)
      ring
    · have := integral_exp_orthogonal (- (k - l)); simp_all +decide [ sub_eq_iff_eq_add ]

private lemma h_parseval_fatou_bound (n : ℕ) (hn : 0 < n) :
    ∫ θ in (-Real.pi)..Real.pi, (‖h_fun n θ‖ ^ 2 : ℝ) ≤
      2 * Real.pi * ∑' k, (1 / (↑(k + n + 1) : ℝ)) ^ 2 := by
  field_simp
  -- Apply Fatou's lemma to the sequence of functions $f_m$.
  have h_fatou : ∫⁻ θ in Set.Ioc (-Real.pi) Real.pi, ENNReal.ofReal (‖h_fun n θ‖ ^ 2) ≤ ENNReal.ofReal (2 * Real.pi * (∑' k : ℕ, (1 / (k + n + 1 : ℝ) ^ 2))) := by
    -- By definition of $f_m$, we know that $f_m(\theta) = \|g_{r_m}(\theta)\|^2$.
    have h_f_m_def : ∀ m : ℕ, ∫⁻ θ in Set.Ioc (-Real.pi) Real.pi, ENNReal.ofReal (‖-Complex.log (1 - (1 - 1 / (m + 2)) * Complex.exp (-θ * Complex.I)) - ∑ k ∈ Finset.range n, ((1 - 1 / (m + 2)) * Complex.exp (-θ * Complex.I)) ^ (k + 1) / (k + 1)‖ ^ 2) = ENNReal.ofReal (2 * Real.pi * (∑' k : ℕ, ((1 - 1 / (m + 2)) ^ (2 * (k + n + 1)) / (k + n + 1 : ℝ) ^ 2))) := by
      intro m
      have h_f_m_eq : ∫ θ in (-Real.pi)..Real.pi, ‖-Complex.log (1 - (1 - 1 / (m + 2)) * Complex.exp (-θ * Complex.I)) - ∑ k ∈ Finset.range n, ((1 - 1 / (m + 2)) * Complex.exp (-θ * Complex.I)) ^ (k + 1) / (k + 1)‖ ^ 2 = 2 * Real.pi * (∑' k : ℕ, ((1 - 1 / (m + 2)) ^ (2 * (k + n + 1)) / (k + n + 1 : ℝ) ^ 2)) := by
        convert g_r_parseval n (1 - 1 / (m + 2)) ?_ ?_ using 1 <;> norm_num
        · refine intervalIntegral.integral_congr fun θ _ => ?_
          have := g_r_eq_tail_series n (1 - (m + 2 : ℝ) ⁻¹) (by exact sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| by linarith) (by exact sub_lt_self _ <| by positivity) θ; aesop
        · exact inv_lt_one_of_one_lt₀ (by linarith)
        · positivity
      rw [← h_f_m_eq, intervalIntegral.integral_of_le (by linarith [ Real.pi_pos ]),
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
      · refine ContinuousOn.integrableOn_Icc ?_ |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self
        refine ContinuousOn.pow ?_ 2
        refine ContinuousOn.norm (ContinuousOn.sub ?_ ?_)
        · refine ContinuousOn.neg (ContinuousOn.clog ?_ ?_)
          · fun_prop
          · norm_num [ Complex.slitPlane, Complex.exp_re, Complex.exp_im ]
            norm_num [ Complex.normSq ]
            exact fun x _ _ => Or.inl (by nlinarith [ inv_pos.mpr (by linarith : 0 < (m : ℝ) + 2), Real.cos_le_one x, mul_inv_cancel₀ (by linarith : (m : ℝ) + 2 ≠ 0) ])
        · fun_prop
      · exact Filter.Eventually.of_forall fun x => sq_nonneg _
    -- By definition of $f_m$, we know that $f_m(\theta) \to \|h(\theta)\|^2$ pointwise as $m \to \infty$.
    have h_f_m_pointwise : ∀ θ ∈ Set.Ioc (-Real.pi) Real.pi, θ ≠ 0 → Filter.Tendsto (fun m : ℕ => ‖-Complex.log (1 - (1 - 1 / (m + 2)) * Complex.exp (-θ * Complex.I)) - ∑ k ∈ Finset.range n, ((1 - 1 / (m + 2)) * Complex.exp (-θ * Complex.I)) ^ (k + 1) / (k + 1)‖ ^ 2) Filter.atTop (nhds (‖h_fun n θ‖ ^ 2)) := by
      intro θ hθ hθ_ne_zero
      have h_log : Filter.Tendsto (fun m : ℕ => -Complex.log (1 - (1 - 1 / (m + 2)) * Complex.exp (-θ * Complex.I))) Filter.atTop (nhds (-Complex.log (1 - Complex.exp (-θ * Complex.I)))) := by
        refine Filter.Tendsto.neg (Filter.Tendsto.comp (Complex.differentiableAt_log ?_ |> DifferentiableAt.continuousAt) ?_)
        · norm_num [ Complex.slitPlane, Complex.ext_iff, Complex.exp_re, Complex.exp_im ]
          contrapose! hθ_ne_zero
          rw [ Real.sin_eq_zero_iff_of_lt_of_lt ] at hθ_ne_zero <;> try linarith [ hθ.1, hθ.2 ]
          exact hθ.2.lt_of_ne (by rintro rfl; norm_num at hθ_ne_zero)
        · exact le_trans (tendsto_const_nhds.sub (Filter.Tendsto.mul (tendsto_const_nhds.sub <| tendsto_zero_iff_norm_tendsto_zero.mpr <| by
              simpa [Function.comp_def] using
                tendsto_inv_atTop_zero.comp <|
                  Filter.tendsto_atTop_mono
                    (fun m => by norm_cast; linarith)
                    tendsto_natCast_atTop_atTop) tendsto_const_nhds)) (by norm_num)
      convert Filter.Tendsto.pow (Filter.Tendsto.norm (h_log.sub (show Filter.Tendsto (fun m : ℕ => ∑ k ∈ Finset.range n, ((1 - 1 / (m + 2 : ℂ)) * Complex.exp (-θ * Complex.I)) ^ (k + 1) / (k + 1 : ℂ)) Filter.atTop (nhds (∑ k ∈ Finset.range n, (Complex.exp (-θ * Complex.I)) ^ (k + 1) / (k + 1 : ℂ))) from ?_))) 2 using 2
      · unfold h_fun; norm_num [ ← Complex.exp_nat_mul ]
        exact congr_arg Norm.norm (by congr; ext; ring_nf)
      · refine tendsto_finsetSum (Finset.range n) fun i hi => ?_
        refine Filter.Tendsto.div_const ?_ ((i + 1 : ℂ))
        refine Filter.Tendsto.pow ?_ (i + 1)
        rw [ tendsto_iff_norm_sub_tendsto_zero ]
        norm_num [ sub_mul ]
        norm_num [ Complex.norm_exp ]
        simpa [Function.comp_def] using
          tendsto_inv_atTop_zero.comp
            (Filter.tendsto_atTop_mono
              (fun m => by norm_cast; linarith)
              tendsto_natCast_atTop_atTop)
    -- Apply Fatou's lemma to the sequence of functions $f_m$ to conclude the proof.
    have h_fatou : ∫⁻ θ in Set.Ioc (-Real.pi) Real.pi, ENNReal.ofReal (‖h_fun n θ‖ ^ 2) ≤ ∫⁻ θ in Set.Ioc (-Real.pi) Real.pi, Filter.liminf (fun m : ℕ => ENNReal.ofReal (‖-Complex.log (1 - (1 - 1 / (m + 2)) * Complex.exp (-θ * Complex.I)) - ∑ k ∈ Finset.range n, ((1 - 1 / (m + 2)) * Complex.exp (-θ * Complex.I)) ^ (k + 1) / (k + 1)‖ ^ 2)) Filter.atTop := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
                      MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (MeasureTheory.measure_singleton 0)] with θ hθ hθ' using by simpa using Filter.Tendsto.liminf_eq (ENNReal.tendsto_ofReal (h_f_m_pointwise θ hθ hθ')) |> ge_of_eq
    refine le_trans h_fatou (le_trans (MeasureTheory.lintegral_liminf_le ?_) ?_)
    · fun_prop
    · rw [ Filter.liminf_congr (Filter.eventuallyEq_of_mem (Filter.Ioi_mem_atTop 0) fun m hm => h_f_m_def m) ]
      refine Filter.Tendsto.liminf_eq ?_ |> le_of_eq
      refine ENNReal.tendsto_ofReal (tendsto_const_nhds.mul ?_)
      refine (tendsto_tsum_of_dominated_convergence
        (bound := fun k => 1 / (k + n + 1) ^ 2) ?_ ?_ ?_)
      · exact_mod_cast summable_nat_add_iff (n + 1) |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two
      · exact fun k => le_trans (Filter.Tendsto.div_const (Filter.Tendsto.pow (tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop) _) _) <| by norm_num
      · norm_num +zetaDelta at *
        exact ⟨0, fun m hm k => mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by positivity) (abs_le.mpr ⟨by nlinarith [ inv_mul_cancel₀ (by positivity : (m : ℝ) + 2 ≠ 0) ], by nlinarith [ inv_mul_cancel₀ (by positivity : (m : ℝ) + 2 ≠ 0) ]⟩))⟩
  rw [intervalIntegral.integral_of_le (by linarith [ Real.pi_pos ]),
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · convert ENNReal.toReal_mono _ h_fatou using 1 <;> norm_num
    rw [ ENNReal.toReal_ofReal (by positivity) ]; ring
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.pow_const ?_ 2
    refine Measurable.norm ?_
    refine Measurable.sub ?_ ?_
    · fun_prop
    · fun_prop

/-
Sum of reciprocal squares tail: ∑_{k>n} 1/k² < 1/n.
-/
private lemma sum_inv_sq_tail_bound (n : ℕ) (hn : 0 < n) :
    ∑' k, (1 / (↑(k + n + 1) : ℝ)) ^ 2 < 1 / (↑n : ℝ) := by
  -- We need to show that the sum of the reciprocals of squares is less than 1/n.
  have h_tail : ∑' k : ℕ, (1 / (k + n + 1 : ℝ)) ^ 2 < ∑' k : ℕ, (1 / ((k + n) * (k + n + 1) : ℝ))
      := by
    fapply Summable.tsum_lt_tsum
    focus
      use 0
    · exact fun x => by rw [div_pow,
                            div_le_div_iff₀] <;> ring_nf <;> nlinarith only [ show (n : ℝ) ≥ 1 by norm_cast ]
    · rw [ div_pow, div_lt_div_iff₀ ] <;> norm_cast <;> nlinarith
    · exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun _ => by simpa using inv_anti₀ (by positivity) (by ring_nf; nlinarith)) (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
    · exact Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> nlinarith) (summable_nat_add_iff n |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
  -- Notice that $\sum_{k=0}^{\infty} \frac{1}{(k+n)(k+n+1)}$ is a telescoping series.
  have h_telescope : ∑' k : ℕ, (1 / ((k + n) * (k + n + 1) : ℝ)) = 1 / (n : ℝ) := by
    -- Notice that $\sum_{k=0}^{\infty} \frac{1}{(k+n)(k+n+1)}$ is a telescoping series, so most terms cancel out.
    have h_telescope : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 / ((k + n) * (k + n + 1) : ℝ)) = 1 / (n : ℝ) - 1 / (N + n : ℝ) := by
      intro N; induction N <;> simp_all +decide [ Finset.sum_range_succ ]; ring_nf
      -- Combine and simplify the terms on the left-hand side.
      field_simp
      ring
    -- Taking the limit of the partial sum as $N$ approaches infinity, we get the sum of the series.
    have h_limit : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (1 / ((k + n) * (k + n + 1) : ℝ))) Filter.atTop (nhds (1 / (n : ℝ))) := by
      have h_zero :
          Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N + n))
            Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop <|
          Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa only [h_telescope, sub_zero] using tendsto_const_nhds.sub h_zero
    exact tendsto_nhds_unique (by exact (Summable.hasSum <| by exact (by by_contra h; exact not_tendsto_atTop_of_tendsto_nhds (h_limit) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg (fun _ => by positivity) |>.1 h)) |> HasSum.tendsto_sum_nat) h_limit
  grind

private lemma one_sub_mul_neg_log_eq {θ : ℝ} (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi)
    (hθ_ne : θ ≠ 0) :
    (1 - Complex.exp (-(↑θ : ℂ) * I)) * (-Complex.log (1 - Complex.exp (-(↑θ : ℂ) * I))) =
      Complex.exp (-(↑θ : ℂ) * I) -
        ∑' k, Complex.exp (-(↑(k + 2 : ℕ) : ℂ) * ↑θ * I) / ((↑(k + 2 : ℕ) : ℂ) * (↑(k + 1 : ℕ) : ℂ)) := by
  have h_taylor : ∀ z : ℂ, ‖z‖ < 1 → (1 - z) * (-Complex.log (1 - z)) = z - ∑' k : ℕ, z^(k + 2) / ((k + 2) * (k + 1)) := by
    intro z hz
    have h_taylor : -Complex.log (1 - z) = ∑' k : ℕ, z^(k + 1) / (k + 1) := by
      have h_series : HasSum (fun k : ℕ => z ^ (k + 1) / (k + 1)) (-Complex.log (1 - z)) := by
        have h_series : HasSum (fun k : ℕ => z ^ k / (k : ℂ)) (-Complex.log (1 - z)) :=
          Complex.hasSum_taylorSeries_neg_log hz
        simpa using (hasSum_nat_add_iff' 1).2 h_series
      exact h_series.tsum_eq.symm
    rw [ h_taylor, sub_mul ]
    rw [ ← tsum_mul_left ]; rw [ Summable.tsum_eq_zero_add ]
    focus
      norm_num
    · rw [ ← tsum_mul_left ]; ring_nf
      rw [show z + (∑' b : ℕ, z ^ 2 * z ^ b * (2 + ↑b)⁻¹) -
            (∑' x : ℕ, z ^ 2 * z ^ x * (1 + ↑x)⁻¹) =
          z + ((∑' b : ℕ, z ^ 2 * z ^ b * (2 + ↑b)⁻¹) -
            (∑' x : ℕ, z ^ 2 * z ^ x * (1 + ↑x)⁻¹)) by ring]
      rw [ ← Summable.tsum_sub ]
      focus
        ring_nf
      · rw [ sub_eq_add_neg, ← tsum_neg ]; congr; ext k; ring_nf
        field_simp
        rw [ div_sub_div ] <;> ring_nf <;> norm_cast <;> norm_num
      · refine Summable.of_norm ?_
        norm_num +zetaDelta at *
        exact Summable.of_nonneg_of_le (fun k => by positivity) (fun k => mul_le_of_le_one_right (by positivity) <| inv_le_one_of_one_le₀ <| by norm_cast; linarith) <| Summable.mul_left _ <| summable_geometric_of_lt_one (by positivity) hz
      · exact Summable.of_norm <| by simpa [ mul_assoc ] using Summable.mul_left _ <| Summable.of_nonneg_of_le (fun n => by positivity) (fun n => by simpa [ abs_of_nonneg, add_nonneg ] using mul_le_of_le_one_right (by positivity) <| inv_le_one_of_one_le₀ <| mod_cast by linarith) <| summable_geometric_of_lt_one (by positivity) hz
    · exact Summable.of_norm <| by simpa using Summable.of_nonneg_of_le (fun n => by positivity) (fun n => by simpa using div_le_self (by positivity) (mod_cast Nat.le_add_left _ _)) (summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one (by positivity) hz)
  have h_cont : Filter.Tendsto (fun r : ℝ => (1 - r * Complex.exp (-θ * I)) * (-Complex.log (1 - r * Complex.exp (-θ * I)))) (nhdsWithin 1 (Set.Iio 1)) (nhds ((1 - Complex.exp (-θ * I)) * (-Complex.log (1 - Complex.exp (-θ * I))))) := by
    refine Filter.Tendsto.mul ?_ ?_
    · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ <| by norm_num)
    · refine Filter.Tendsto.neg (Filter.Tendsto.comp (Complex.differentiableAt_log ?_ |> DifferentiableAt.continuousAt) ?_)
      · norm_num [ Complex.slitPlane, Complex.exp_re, Complex.exp_im ]
        exact Or.inr (by exact fun h => hθ_ne <| by rw [ Real.sin_eq_zero_iff_of_lt_of_lt ] at h <;> linarith [ hθ.1, hθ.2 ])
      · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ <| by norm_num)
  have h_cont_sum : Filter.Tendsto (fun r : ℝ => r * Complex.exp (-θ * I) - ∑' k : ℕ, (r * Complex.exp (-θ * I))^(k + 2) / ((k + 2) * (k + 1))) (nhdsWithin 1 (Set.Iio 1)) (nhds (Complex.exp (-θ * I) - ∑' k : ℕ, Complex.exp (- (k + 2) * θ * I) / ((k + 2) * (k + 1)))) := by
    refine Filter.Tendsto.sub ?_ ?_
    · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ (by norm_num))
    · refine tendsto_tsum_of_dominated_convergence
        (bound := fun k => 1 / ((k + 2) * (k + 1))) ?_ ?_ ?_
      · exact Summable.of_nonneg_of_le (fun k => by positivity) (fun k => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> nlinarith) (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
      · intro k
        refine Filter.Tendsto.div_const ?_ (((k + 2 : ℂ) * (k + 1 : ℂ)))
        refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
        norm_num [mul_pow, ← Complex.exp_nat_mul]
        ring_nf
        exact Continuous.tendsto' (by continuity) _ _ (by norm_num)
      · norm_num [ Complex.norm_exp ]
        norm_cast; norm_num [ div_eq_mul_inv, mul_comm ]
        filter_upwards [ Ioo_mem_nhdsLT zero_lt_one ] with n hn using fun k => mul_le_of_le_one_left (by positivity) (pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith [ hn.1 ], by linarith [ hn.2 ]⟩))
  norm_num +zetaDelta at *
  exact tendsto_nhds_unique (h_cont.neg.congr' <| Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one) fun x hx => by rw [ ← h_taylor _ <| by simpa [ abs_of_pos hx.1, Complex.norm_exp ] using hx.2 ]) h_cont_sum

/-
Abel summation bound: for θ ≠ 0, |(1-e^{-iθ})·h_fun n θ| ≤ 2/(n+1).
-/
private lemma h_mul_one_sub_exp_bound (n : ℕ) (hn : 0 < n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi) (hθ_ne : θ ≠ 0) :
    ‖(1 - Complex.exp (-(↑θ : ℂ) * I)) * h_fun n θ‖ ≤ 2 / (↑n + 1) := by
  -- Now use the given equality and bound the terms accordingly.
  have h_eq_bound : ‖(1 - Complex.exp (-θ * I)) * h_fun n θ‖ ≤ ‖Complex.exp (-(↑(n + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(n + 1 : ℕ) : ℂ)‖ + ‖∑' k : ℕ, Complex.exp (-(↑(k + n + 2 : ℕ) : ℂ) * ↑θ * I) / ((↑(k + n + 2 : ℕ) : ℂ) * (↑(k + n + 1 : ℕ) : ℂ))‖ := by
    have h_eq_bound : (1 - Complex.exp (-θ * I)) * h_fun n θ = Complex.exp (-(↑(n + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(n + 1 : ℕ) : ℂ) - ∑' k : ℕ, Complex.exp (-(↑(k + n + 2 : ℕ) : ℂ) * ↑θ * I) / ((↑(k + n + 2 : ℕ) : ℂ) * (↑(k + n + 1 : ℕ) : ℂ)) := by
      have h_eq_bound : (1 - Complex.exp (-θ * I)) * h_fun n θ = Complex.exp (-θ * I) - ∑' k : ℕ, Complex.exp (-(↑(k + 2 : ℕ) : ℂ) * ↑θ * I) / ((↑(k + 2 : ℕ) : ℂ) * (↑(k + 1 : ℕ) : ℂ)) - (Complex.exp (-θ * I) - ∑ k ∈ Finset.range n, Complex.exp (-(↑(k + 2 : ℕ) : ℂ) * ↑θ * I) / ((↑(k + 2 : ℕ) : ℂ) * (↑(k + 1 : ℕ) : ℂ)) - Complex.exp (-(↑(n + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(n + 1 : ℕ) : ℂ)) := by
        have h_simplify :
            (1 - Complex.exp (-(θ : ℂ) * I)) * (-Complex.log (1 - Complex.exp (-(θ : ℂ) * I))) =
          Complex.exp (-(θ : ℂ) * I) - ∑' k : ℕ, Complex.exp (-(↑(k + 2) : ℂ) * θ * I) / ((↑(k + 2) : ℂ) * (↑(k + 1) : ℂ)) :=
            one_sub_mul_neg_log_eq hθ hθ_ne
        convert congr_arg (fun x : ℂ => x - (1 - Complex.exp (-θ * I)) * (∑ k ∈ Finset.range n, Complex.exp (-↑ (k + 1) * θ * I) / (k + 1 : ℂ))) h_simplify using 1
        · unfold h_fun; norm_num [ mul_sub ]
        · have h_simplify : ∀ m : ℕ, (1 - Complex.exp (-(θ : ℂ) * I)) * (∑ k ∈ Finset.range m, Complex.exp (-(↑(k + 1) : ℂ) * θ * I) / (↑(k + 1) : ℂ)) = Complex.exp (-(θ : ℂ) * I) - ∑ k ∈ Finset.range m, Complex.exp (-(↑(k + 2) : ℂ) * θ * I) / ((↑(k + 2) : ℂ) * (↑(k + 1) : ℂ)) - Complex.exp (-(↑(m + 1) : ℂ) * θ * I) / (↑(m + 1) : ℂ) := by
            intro m
            let q : ℂ := Complex.exp (-(θ : ℂ) * I)
            have hpow : ∀ r : ℕ, q ^ r = Complex.exp (-(↑r : ℂ) * θ * I) := by
              intro r
              dsimp [q]
              rw [← Complex.exp_nat_mul]
              congr 1
              ring
            have hfinite : ∀ m : ℕ,
                (1 - q) * (∑ k ∈ Finset.range m, q ^ (k + 1) / (↑(k + 1) : ℂ)) =
                  q - ∑ k ∈ Finset.range m, q ^ (k + 2) / ((↑(k + 2) : ℂ) * (↑(k + 1) : ℂ)) -
                    q ^ (m + 1) / (↑(m + 1) : ℂ) := by
              intro m
              induction m with
              | zero =>
                  simp [q]
              | succ m ih =>
                  rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
                  have hm1 : ((↑(m + 1) : ℂ) ≠ 0) := by
                    exact_mod_cast (Nat.succ_ne_zero m)
                  have hm2 : ((↑(m + 2) : ℂ) ≠ 0) := by
                    exact_mod_cast (Nat.succ_ne_zero (m + 1))
                  have hfrac :
                      q ^ (m + 2) / (↑(m + 1) : ℂ) =
                        q ^ (m + 2) / ((↑(m + 2) : ℂ) * (↑(m + 1) : ℂ)) +
                          q ^ (m + 2) / (↑(m + 2) : ℂ) := by
                    field_simp [hm1, hm2]
                    rw [show (↑(m + 2) : ℂ) = 1 + ↑(m + 1) by norm_num; ring]
                  calc
                    q - ∑ k ∈ Finset.range m, q ^ (k + 2) / ((↑(k + 2) : ℂ) * (↑(k + 1) : ℂ)) -
                          q ^ (m + 1) / (↑(m + 1) : ℂ) +
                        (1 - q) * (q ^ (m + 1) / (↑(m + 1) : ℂ))
                        = q - ∑ k ∈ Finset.range m, q ^ (k + 2) / ((↑(k + 2) : ℂ) * (↑(k + 1) : ℂ)) -
                            q ^ (m + 2) / (↑(m + 1) : ℂ) := by
                            ring
                    _ = q - ∑ k ∈ Finset.range m, q ^ (k + 2) / ((↑(k + 2) : ℂ) * (↑(k + 1) : ℂ)) -
                          (q ^ (m + 2) / ((↑(m + 2) : ℂ) * (↑(m + 1) : ℂ)) +
                            q ^ (m + 2) / (↑(m + 2) : ℂ)) := by
                            rw [hfrac]
                    _ = q - (∑ k ∈ Finset.range m, q ^ (k + 2) / ((↑(k + 2) : ℂ) * (↑(k + 1) : ℂ)) +
                            q ^ (m + 2) / ((↑(m + 2) : ℂ) * (↑(m + 1) : ℂ))) -
                          q ^ (m + 2) / (↑(m + 2) : ℂ) := by
                            ring
            have hpow_succ : ∀ r : ℕ,
                q ^ (r + 1) = Complex.exp ((-1 + -↑r) * (θ : ℂ) * I) := by
              intro r
              rw [hpow (r + 1)]
              congr 1
              norm_num [Nat.cast_add, Nat.cast_one]
            have hpow_succ_succ : ∀ r : ℕ,
                q ^ (r + 2) = Complex.exp ((-2 + -↑r) * (θ : ℂ) * I) := by
              intro r
              rw [hpow (r + 2)]
              congr 1
              norm_num [Nat.cast_add, Nat.cast_one]
            have hf := hfinite m
            simp_rw [hpow_succ_succ] at hf
            simp_rw [hpow_succ] at hf
            simpa [q, Nat.cast_add, Nat.cast_one] using hf
          rw [← h_simplify n]
          simp [Nat.cast_add, Nat.cast_one]
      rw [ h_eq_bound, ← Summable.sum_add_tsum_nat_add n ]
      · ring
      · rw [ ← summable_norm_iff ]
        norm_num [ Complex.norm_exp ]
        field_simp
        exact Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> nlinarith) (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
    exact h_eq_bound ▸ norm_sub_le _ _
  -- Now use the given equality and bound the terms accordingly. We'll first bound the first term.
  have h_first_term : ‖Complex.exp (-(↑(n + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(n + 1 : ℕ) : ℂ)‖ ≤ 1 / (↑(n + 1 : ℕ) : ℝ) := by
    norm_num [ Complex.norm_exp ]
    norm_cast
  -- Now use the given equality and bound the terms accordingly. We'll first bound the second term.
  have h_second_term : ‖∑' k : ℕ, Complex.exp (-(↑(k + n + 2 : ℕ) : ℂ) * ↑θ * I) / ((↑(k + n + 2 : ℕ) : ℂ) * (↑(k + n + 1 : ℕ) : ℂ))‖ ≤ ∑' k : ℕ, (1 : ℝ) / ((↑(k + n + 2 : ℕ) : ℝ) * (↑(k + n + 1 : ℕ) : ℝ)) := by
    convert norm_tsum_le_tsum_norm _ <;> norm_num [ Complex.norm_exp ]
    · norm_cast
    · exact Summable.of_nonneg_of_le (fun _ => by positivity) (fun i => by rw [ ← mul_inv ]; rw [ inv_le_comm₀ ] <;> norm_num <;> ring_nf <;> norm_cast <;> nlinarith) (summable_nat_add_iff n |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
  -- Now use the given equality and bound the terms accordingly. We'll first bound the sum.
  have h_sum_bound : ∑' k : ℕ, (1 : ℝ) / ((↑(k + n + 2 : ℕ) : ℝ) * (↑(k + n + 1 : ℕ) : ℝ)) ≤ 1 / (↑(n + 1 : ℕ) : ℝ) := by
    have h_sum_bound : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 : ℝ) / ((↑(k + n + 2 : ℕ) : ℝ) * (↑(k + n + 1 : ℕ) : ℝ)) ≤ 1 / (↑(n + 1 : ℕ) : ℝ) - 1 / (↑(N + n + 1 : ℕ) : ℝ) := by
      intro N
      induction N with
      | zero =>
          norm_num
      | succ N ih =>
          norm_num [add_assoc, Finset.sum_range_succ] at *
          nlinarith [inv_pos.mpr (by positivity : 0 < (N : ℝ) + (n + 1)),
                     inv_pos.mpr (by positivity : 0 < (N : ℝ) + (n + 2)),
                     inv_pos.mpr (by positivity : 0 < (N : ℝ) + (1 + (n + 1))),
                     mul_inv_cancel₀ (by positivity : (N : ℝ) + (n + 1) ≠ 0),
                     mul_inv_cancel₀ (by positivity : (N : ℝ) + (n + 2) ≠ 0),
                     mul_inv_cancel₀ (by positivity : (N : ℝ) + (1 + (n + 1)) ≠ 0)]
    refine le_of_tendsto_of_tendsto' (Summable.hasSum (by exact Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> nlinarith) <| summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two) |> HasSum.tendsto_sum_nat) tendsto_const_nhds fun N => le_trans (h_sum_bound N) <| sub_le_self (1 / (↑(n + 1 : ℕ) : ℝ)) <| by positivity
  exact h_eq_bound.trans (by convert add_le_add h_first_term (h_second_term.trans h_sum_bound) using 1; push_cast; ring)

/-
Jordan's inequality: |sin(x)| ≥ 2|x|/π for |x| ≤ π/2.
-/
private lemma jordan_inequality {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    |Real.sin x| ≥ 2 * |x| / Real.pi := by
  -- By considering the interval [0, π/2], we can use the fact that sin(x) is concave and apply Jensen's inequality.
  have h_sin_bound : ∀ x ∈ Set.Icc 0 (Real.pi / 2), Real.sin x ≥ (2 * x) / Real.pi := by
    exact fun x hx => by have := Real.mul_le_sin hx.1 hx.2; ring_nf at this ⊢; linarith
  cases abs_cases x <;> cases abs_cases (Real.sin x) <;> simp +decide [ * ]
  · exact h_sin_bound x ⟨by linarith, by linarith⟩
  · linarith [h_sin_bound x ⟨by linarith, by linarith⟩,
              Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ x) (by linarith)]
  · linarith [ Real.sin_neg_of_neg_of_neg_pi_lt (by linarith : x < 0) (by linarith) ]
  · have := h_sin_bound (-x) ⟨by linarith, by linarith⟩; norm_num at *; ring_nf at *; linarith

/-
|1 - e^{-iθ}| = 2|sin(θ/2)|
-/
private lemma norm_one_sub_exp (θ : ℝ) :
    ‖(1 : ℂ) - Complex.exp (-(↑θ : ℂ) * I)‖ = 2 * |Real.sin (θ / 2)| := by
  norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ]
  rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring_nf
  nlinarith [ Real.cos_sq' θ ]

/-
For π/n ≤ |θ| ≤ π, the pointwise bound |h(θ)| ≤ π/(n|θ|).
This follows from Abel summation / summation by parts.
-/
lemma h_pointwise_far_bound (n : ℕ) (hn : 0 < n) {θ : ℝ}
    (hθ_lo : Real.pi / n ≤ |θ|) (hθ_hi : |θ| ≤ Real.pi) :
    ‖h_fun n θ‖ ≤ Real.pi / (n * |θ|) := by
  -- Apply the bound from h_mul_one_sub_exp_bound and use the fact that |1 - e^{-iθ}| = 2|sin(θ/2)|.
  have h_bound : ‖h_fun n θ‖ ≤ 2 / (n + 1) / (2 * |Real.sin (θ / 2)|) := by
    by_cases hθ_eq : θ = Real.pi ∨ θ = -Real.pi
    · obtain rfl | rfl := hθ_eq <;> norm_num [ neg_div ] at *
      · have h_cont : Filter.Tendsto (fun ε => h_fun n (Real.pi - ε) * (1 - Complex.exp (-(Real.pi - ε) * Complex.I))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (h_fun n Real.pi * (1 - Complex.exp (-Real.pi * Complex.I)))) := by
          refine Filter.Tendsto.mul ?_ ?_
          · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
            refine (ContinuousAt.tendsto ?_).comp ?_
            · refine ContinuousAt.sub ?_ ?_
              · refine ContinuousAt.neg (ContinuousAt.clog ?_ ?_)
                · exact Continuous.continuousAt (by continuity)
                · norm_num [ Complex.slitPlane, Complex.exp_re, Complex.exp_im ]
              · exact tendsto_finsetSum _ fun _ _ => Continuous.continuousAt (by continuity)
            · convert (((continuous_const : Continuous fun _ : ℝ => Real.pi).sub continuous_id).tendsto
                (0 : ℝ)) using 1
              · ext ε
                rfl
              · norm_num
          · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ <| by norm_num)
        have h_bound : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), ‖h_fun n (Real.pi - ε) * (1 - Complex.exp (-(Real.pi - ε) * Complex.I))‖ ≤ 2 / (n + 1) := by
          filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨le_rfl, Real.pi_pos⟩ ] with ε hε
          have := h_mul_one_sub_exp_bound n hn (show Real.pi - ε ∈ Set.Ioo (-Real.pi) Real.pi from ⟨by linarith [ hε.1, hε.2 ], by linarith [ hε.1, hε.2 ]⟩) (show Real.pi - ε ≠ 0 from by linarith [ hε.1, hε.2 ]); simp_all +decide [ mul_comm ]
        have h_bound : ‖h_fun n Real.pi * (1 - Complex.exp (-Real.pi * Complex.I))‖ ≤ 2 / (n + 1)
            := by
          exact le_of_tendsto (h_cont.norm) h_bound
        norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ] at *
        linarith
      · -- By continuity of $h_fun$, we can extend the bound to $\theta = -\pi$.
        have h_cont : Filter.Tendsto (fun θ => ‖h_fun n θ‖) (nhdsWithin (-Real.pi) (Set.Ioi (-Real.pi))) (nhds (‖h_fun n (-Real.pi)‖)) := by
          refine Filter.Tendsto.norm ?_
          refine Filter.Tendsto.sub ?_ ?_
          · refine Filter.Tendsto.neg (Filter.Tendsto.comp (Complex.differentiableAt_log ?_ |> DifferentiableAt.continuousAt) ?_)
            · norm_num [ Complex.slitPlane, Complex.exp_re, Complex.exp_im ]
            · exact tendsto_const_nhds.sub (Complex.continuous_exp.continuousAt.tendsto.comp <| Continuous.continuousWithinAt <| by continuity)
          · exact tendsto_finsetSum _ fun _ _ => Continuous.continuousWithinAt (by continuity)
        have h_bound : ∀ᶠ θ in nhdsWithin (-Real.pi) (Set.Ioi (-Real.pi)), ‖h_fun n θ‖ ≤ 2 / (n + 1) / (2 * |Real.sin (θ / 2)|) := by
          have h_bound : ∀ᶠ θ in nhdsWithin (-Real.pi) (Set.Ioi (-Real.pi)), θ ≠ 0 ∧ θ ∈ Set.Ioo (-Real.pi) Real.pi := by
            rw [ eventually_nhdsWithin_iff ]
            filter_upwards [ gt_mem_nhds (show -Real.pi < 0 by linarith [ Real.pi_pos ]) ] with x hx₁ hx₂ using ⟨by linarith [ hx₂.out ], hx₂.out, by linarith [ hx₂.out, Real.pi_pos ]⟩
          filter_upwards [ h_bound ] with θ hθ
          have := h_mul_one_sub_exp_bound n hn hθ.2 hθ.1
          have hden_pos : 0 < 2 * |Real.sin (θ / 2)| :=
            mul_pos zero_lt_two
              (abs_pos.mpr (show Real.sin (θ / 2) ≠ 0 from by
                exact fun h => hθ.1 <| by
                  rw [ Real.sin_eq_zero_iff_of_lt_of_lt ] at h <;>
                    linarith [ hθ.2.1, hθ.2.2 ]))
          have hmul : ‖h_fun n θ‖ * (2 * |Real.sin (θ / 2)|) ≤ 2 / (n + 1) := by
            rw [← norm_one_sub_exp θ, ← norm_mul]
            simpa [mul_assoc, mul_comm, mul_left_comm] using this
          exact (le_div_iff₀ hden_pos).2 hmul
        have h_lim_bound : Filter.Tendsto (fun θ => 2 / (n + 1) / (2 * |Real.sin (θ / 2)|)) (nhdsWithin (-Real.pi) (Set.Ioi (-Real.pi))) (nhds (2 / (n + 1) / 2)) := by
          have hden :
              Filter.Tendsto (fun θ : ℝ => 2 * |Real.sin (θ / 2)|)
                (nhdsWithin (-Real.pi) (Set.Ioi (-Real.pi))) (nhds 2) := by
            simpa [neg_div] using
              ((show ContinuousAt (fun θ : ℝ => 2 * |Real.sin (θ / 2)|) (-Real.pi) from
                (show Continuous fun θ : ℝ => 2 * |Real.sin (θ / 2)| from
                  Continuous.mul continuous_const <| Continuous.abs <|
                    Real.continuous_sin.comp <| by continuity).continuousAt).tendsto.mono_left
                  nhdsWithin_le_nhds)
          exact tendsto_const_nhds.div hden (by norm_num)
        exact le_of_tendsto_of_tendsto h_cont h_lim_bound h_bound
    · have h_bound : ‖(1 - Complex.exp (-(θ : ℂ) * I)) * h_fun n θ‖ ≤ 2 / (n + 1) := by
        apply h_mul_one_sub_exp_bound n hn
        · exact ⟨lt_of_le_of_ne (neg_le_of_abs_le hθ_hi) (by tauto), lt_of_le_of_ne (le_of_abs_le hθ_hi) (by tauto)⟩
        · rintro rfl; exact absurd hθ_lo (by norm_num; positivity)
      have h_norm : ‖1 - Complex.exp (-(θ : ℂ) * I)‖ = 2 * |Real.sin (θ / 2)| :=
        norm_one_sub_exp θ
      rw [ le_div_iff₀ ]
      · rw [ ← h_norm, mul_comm, ← norm_mul ]; aesop
      · simp +zetaDelta at *
        exact fun h => hθ_eq.1 <| mul_left_cancel₀ (sub_ne_zero_of_ne hθ_eq.2) <| by rw [ Real.sin_eq_zero_iff_of_lt_of_lt ] at h <;> cases abs_cases θ <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0) ]
  -- Apply the bound from jordan_inequality to get |sin(θ/2)| ≥ |θ|/π.
  have h_sin_bound : |Real.sin (θ / 2)| ≥ |θ| / Real.pi := by
    have := jordan_inequality (show |θ / 2| ≤ Real.pi / 2 by rw [ abs_div, abs_two ]; linarith)
    cases abs_cases θ <;> cases abs_cases (θ / 2) <;> ring_nf at * <;> nlinarith [Real.pi_pos,
                                                                                  mul_inv_cancel₀ Real.pi_ne_zero]
  refine le_trans h_bound ?_
  rw [ div_div, div_le_div_iff₀ ]
  · rw [ge_iff_le,
        div_le_iff₀] at h_sin_bound <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, abs_nonneg θ ]
  · exact mul_pos (by positivity) (mul_pos zero_lt_two (lt_of_lt_of_le (by exact div_pos (lt_of_lt_of_le (by positivity) hθ_lo) Real.pi_pos) h_sin_bound))
  · exact mul_pos (Nat.cast_pos.mpr hn) (lt_of_lt_of_le (by positivity) hθ_lo)

/-
In the far region π/n ≤ |θ| ≤ π, the g deviation satisfies
|g(θ)-g(0)| ≤ s(π+2) + 2s·log(n|θ|/π).
-/
private lemma g_deviation_far {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (_hz : ∀ i, ‖z i‖ ≤ 1)
    {s : ℝ} (hs_pos : 0 < s)
    (hs_max : ∀ k : Fin n, ‖powerSum z (k.val + 1)‖ ≤ s)
    {θ : ℝ} (hθ_lo : Real.pi / n ≤ |θ|) (hθ_hi : |θ| ≤ Real.pi) :
    ‖g_fun z θ - g_fun z 0‖ ≤ s * (Real.pi + 2) + 2 * s * Real.log (↑n * |θ| / Real.pi) := by
  unfold g_fun
  -- For near terms with $m \leq \pi/|\theta|$, $|term_m| \leq s|\theta|$. Sum $\leq (\pi/|\theta|) \cdot s \cdot |\theta| = \pi s$.
  have h_near : ‖∑ k : Fin n, (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) * (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) * (if (k.val + 1 : ℝ) ≤ Real.pi / |θ| then 1 else 0)‖ ≤ Real.pi * s := by
    have h_near : ∀ k : Fin n, (k.val + 1 : ℝ) ≤ Real.pi / |θ| → ‖(powerSum z (k.val + 1) / (k.val + 1 : ℂ)) * (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1)‖ ≤ s * |θ| := by
      intros k hk
      have h_term : ‖Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1‖ ≤ (k.val + 1 : ℝ) * |θ| := by
        -- Using the fact that $|e^{i\theta} - 1| \leq |\theta|$ for any real $\theta$, we get:
        have h_exp_bound : ∀ θ : ℝ, ‖Complex.exp (θ * I) - 1‖ ≤ |θ| := by
          -- Using the fact that $|e^{i\theta} - 1| = 2|\sin(\theta/2)|$, we get:
          have h_exp_bound : ∀ θ : ℝ, ‖Complex.exp (θ * I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
            norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ]
            intro θ; rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring_nf
            nlinarith [ Real.cos_sq' θ ]
          -- Using the fact that $|\sin(x)| \leq |x|$ for all $x$, we get:
          have h_sin_bound : ∀ x : ℝ, |Real.sin x| ≤ |x| := by
            exact fun x => Real.abs_sin_le_abs
          intro θ; rw [ h_exp_bound θ ]; specialize h_sin_bound (θ / 2); cases abs_cases (θ / 2) <;> cases abs_cases θ <;> linarith
        convert h_exp_bound ((k + 1) * θ) using 1
        focus
          norm_num [ abs_mul, abs_of_nonneg, add_nonneg ]
        norm_num [ abs_mul, abs_of_nonneg, add_nonneg ]
      simp_all +decide [ div_mul_eq_mul_div ]
      rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num
      nlinarith [hs_max k, norm_nonneg (powerSum z (k.val + 1)),
                 norm_nonneg (Complex.exp ((k.val + 1) * θ * I) - 1)]
    have h_near_sum : ‖∑ k : Fin n, (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) * (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) * (if (k.val + 1 : ℝ) ≤ Real.pi / |θ| then 1 else 0)‖ ≤ ∑ k : Fin n, (if (k.val + 1 : ℝ) ≤ Real.pi / |θ| then s * |θ| else 0) := by
      refine le_trans
        (norm_sum_le (Finset.univ : Finset (Fin n))
          (fun k =>
            (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) *
              (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) *
                (if (k.val + 1 : ℝ) ≤ Real.pi / |θ| then 1 else 0))) ?_
      gcongr; aesop
    -- The number of terms in the sum is at most $\pi / |\theta|$.
    have h_num_terms :
        ∑ k : Fin n, (if (k.val + 1 : ℝ) ≤ Real.pi / |θ| then 1 else 0) ≤ Real.pi / |θ| := by
      have h_num_terms : Finset.card (Finset.filter (fun k : Fin n => (k.val + 1 : ℝ) ≤ Real.pi / |θ|) Finset.univ) ≤ Nat.floor (Real.pi / |θ|) := by
        have h_num_terms : Finset.card (Finset.filter (fun k : Fin n => (k.val + 1 : ℝ) ≤ Real.pi / |θ|) Finset.univ) ≤ Finset.card (Finset.Ico 1 (Nat.floor (Real.pi / |θ|) + 1)) := by
          have h_num_terms : Finset.image (fun k : Fin n => k.val + 1) (Finset.filter (fun k : Fin n => (k.val + 1 : ℝ) ≤ Real.pi / |θ|) Finset.univ) ⊆ Finset.Ico 1 (Nat.floor (Real.pi / |θ|) + 1) := by
            exact Finset.image_subset_iff.mpr fun k hk => Finset.mem_Ico.mpr ⟨by linarith [ Fin.is_lt k ], Nat.lt_succ_of_le <| Nat.le_floor <| by simpa using Finset.mem_filter.mp hk |>.2⟩
          exact le_trans (by rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ]) (Finset.card_mono h_num_terms)
        aesop
      simpa using Nat.floor_le (show 0 ≤ Real.pi / |θ| by positivity) |> le_trans (Nat.cast_le.mpr h_num_terms)
    simp_all +decide [ Finset.sum_ite ]
    exact h_near_sum.trans (by rw [ le_div_iff₀ (abs_pos.mpr <| show θ ≠ 0 from by rintro rfl; exact absurd hθ_lo <| by norm_num; positivity) ] at h_num_terms; nlinarith)
  -- For far terms with $m > \pi/|\theta|$, $|term_m| \leq 2s/m$. Sum $\leq 2s \cdot \sum_{m>\pi/|\theta|}^n 1/m$.
  have h_far : ‖∑ k : Fin n, (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) * (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) * (if (k.val + 1 : ℝ) > Real.pi / |θ| then 1 else 0)‖ ≤ 2 * s * ∑ k ∈ Finset.Ico (Nat.floor (Real.pi / |θ|) + 1) (n + 1), (1 / (k : ℝ)) := by
    have h_far : ∀ k : Fin n, ‖(powerSum z (k.val + 1) / (k.val + 1 : ℂ)) * (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) * (if (k.val + 1 : ℝ) > Real.pi / |θ| then 1 else 0)‖ ≤ 2 * s * (if (k.val + 1 : ℝ) > Real.pi / |θ| then 1 / (k.val + 1 : ℝ) else 0) := by
      intro k; split_ifs <;> simp_all +decide [ div_eq_mul_inv, mul_comm, mul_left_comm ]
      have h_norm_sub :=
        norm_sub_le (Complex.exp ((k.val + 1 : ℂ) * θ * I)) (1 : ℂ)
      norm_cast
      norm_num [ mul_assoc, mul_comm, mul_left_comm ] at h_norm_sub ⊢
      refine le_trans
        (mul_le_mul_of_nonneg_right
          h_norm_sub (by positivity)) ?_
      norm_num [ Complex.norm_exp ]
      nlinarith [ hs_max k, inv_pos.mpr (by positivity : 0 < (k : ℝ) + 1) ]
    refine le_trans
      (norm_sum_le (Finset.univ : Finset (Fin n))
        (fun k =>
          (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) *
            (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) *
              (if (k.val + 1 : ℝ) > Real.pi / |θ| then 1 else 0))) ?_
    refine le_trans (Finset.sum_le_sum fun k _ => h_far k) ?_
    norm_num [ Finset.sum_ite, Finset.mul_sum _ _ _ ]
    refine le_of_eq ?_
    refine Finset.sum_bij (fun x hx => x + 1) ?_ ?_ ?_ ?_ <;> norm_num
    · exact fun k hk => Nat.le_of_lt_succ <| by rw [ Nat.floor_lt' ] <;> norm_num; linarith
    · exact fun a₁ ha₁ a₂ ha₂ h => Fin.ext h
    · exact fun b hb₁ hb₂ => ⟨⟨b - 1, Nat.lt_of_lt_of_le (Nat.sub_lt (by linarith) zero_lt_one) hb₂⟩, by simpa [ Nat.cast_sub (show 1 ≤ b by linarith) ] using Nat.lt_of_floor_lt hb₁, by cases b <;> aesop⟩
  -- Now use the fact that $\sum_{m=\lfloor \pi/|\theta| \rfloor + 1}^n \frac{1}{m} \leq \log(n) - \log(\lfloor \pi/|\theta| \rfloor) \leq \log(n|\theta|/\pi) + 1$.
  have h_sum_bound : ∑ k ∈ Finset.Ico (Nat.floor (Real.pi / |θ|) + 1) (n + 1), (1 / (k : ℝ)) ≤ Real.log (n * |θ| / Real.pi) + 1 := by
    -- The sum of reciprocals of integers from $a$ to $b$ is bounded by $\log(b) - \log(a) + 1$.
    have h_sum_bound : ∀ a b : ℕ, 1 ≤ a → a ≤ b → ∑ k ∈ Finset.Ico a (b + 1), (1 / (k : ℝ)) ≤ Real.log b - Real.log a + 1 := by
      intros a b ha hb
      have h_sum_bound : ∑ k ∈ Finset.Ico a b, (1 / (k + 1 : ℝ)) ≤ Real.log b - Real.log a := by
        have h_sum_bound : ∀ k ∈ Finset.Ico a b, (1 / (k + 1 : ℝ)) ≤ Real.log (k + 1) - Real.log k
            := by
          intros k hk
          have := exists_deriv_eq_slope Real.log (show (k : ℝ) < k + 1 by norm_num); norm_num at *
          exact this (continuousOn_of_forall_continuousAt fun x hx => Real.continuousAt_log <| ne_of_gt <| lt_of_lt_of_le (by norm_cast; linarith) hx.1) (fun x hx => DifferentiableAt.differentiableWithinAt <| Real.differentiableAt_log <| ne_of_gt <| lt_of_lt_of_le (by norm_cast; linarith) hx.1.le) |> fun ⟨c, hc₁, hc₂⟩ => hc₂ ▸ inv_anti₀ (by linarith) (by linarith)
        refine le_trans (Finset.sum_le_sum h_sum_bound) ?_
        exact le_of_eq <| by
          rw [ Finset.sum_Ico_eq_sub _ hb ]
          exact Nat.recOn b (Nat.recOn a (by norm_num) fun n ihn => by norm_num [ Finset.sum_range_succ ] at *; linarith) fun n ihn => by norm_num [ Finset.sum_range_succ ] at *; linarith
      rw [ Finset.sum_Ico_eq_sum_range ] at *
      rw [ Nat.succ_sub hb, Finset.sum_range_succ' ]
      norm_num [ add_assoc ] at *; linarith [ inv_le_one_of_one_le₀ (show (a : ℝ) ≥ 1 by norm_cast) ]
    by_cases h : ⌊Real.pi / |θ|⌋₊ + 1 ≤ n <;> simp_all +decide [ div_le_iff₀ ]
    · refine le_trans (h_sum_bound _ _ (Nat.succ_pos _) (by linarith)) ?_
      rw [ Real.log_div, Real.log_mul ] <;> norm_num <;> try positivity
      · have h_log_bound : Real.log (⌊Real.pi / |θ|⌋₊ + 1) ≥ Real.log (Real.pi / |θ|) := by
          exact Real.log_le_log (div_pos Real.pi_pos (abs_pos.mpr (show θ ≠ 0 by rintro rfl; norm_num at *; linarith [ Real.pi_pos ]))) (by linarith [ Nat.lt_floor_add_one (Real.pi / |θ|) ])
        rw [ Real.log_div (by positivity) (by cases abs_cases θ <;> nlinarith [ Real.pi_pos ]) ] at h_log_bound; cases abs_cases θ <;> simp_all +decide []
        · rw [ abs_of_nonneg ‹_› ]; linarith
        · rw [ abs_of_nonpos (by linarith) ]; linarith
      · rintro rfl; norm_num at *; linarith [ Real.pi_pos ]
      · exact ⟨hn.ne', by rintro rfl; norm_num at hθ_lo; linarith [ Real.pi_pos ]⟩
    · exact add_nonneg (Real.log_nonneg (by rw [ le_div_iff₀ Real.pi_pos ]; nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast ])) zero_le_one
  -- Combine the bounds for the near and far terms.
  have h_combined : ‖∑ k : Fin n, (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) * (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1)‖ ≤ Real.pi * s + 2 * s * (Real.log (n * |θ| / Real.pi) + 1) := by
    calc
      ‖∑ k : Fin n,
          (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) *
            (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1)‖
          = ‖(∑ k : Fin n,
                (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) *
                  (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) *
                    if k.val + 1 ≤ Real.pi / |θ| then 1 else 0) +
              (∑ k : Fin n,
                (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) *
                  (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) *
                    if k.val + 1 > Real.pi / |θ| then 1 else 0)‖ := by
            congr 1
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            split_ifs <;> ring_nf <;> linarith
      _ ≤
          ‖∑ k : Fin n,
            (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) *
              (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) *
                if k.val + 1 ≤ Real.pi / |θ| then 1 else 0‖ +
            ‖∑ k : Fin n,
              (powerSum z (k.val + 1) / (k.val + 1 : ℂ)) *
                (Complex.exp ((k.val + 1 : ℂ) * θ * I) - 1) *
                  if k.val + 1 > Real.pi / |θ| then 1 else 0‖ :=
        norm_add_le _ _
      _ ≤ Real.pi * s + 2 * s * (Real.log (n * |θ| / Real.pi) + 1) :=
        add_le_add h_near
          (h_far.trans (mul_le_mul_of_nonneg_left h_sum_bound <| by positivity))
  convert h_combined using 1 <;> norm_num
  focus
    ring_nf
  · norm_num [ add_comm, add_left_comm, add_assoc, Finset.sum_add_distrib ]
    norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]
    rw [ ← norm_neg ]; ring_nf
  · ring

/-! ### Helper lemmas for h_L2_bound -/

/-
The tail sum ∑_{m≥n+1} 1/m² < 1/n, by comparison with the telescoping series
1/(m(m-1)) = 1/(m-1) - 1/m.
-/
private lemma tsum_inv_sq_lt_inv (n : ℕ) (hn : 0 < n) :
    ∑' (m : ℕ), (1 : ℝ) / (↑(m + n + 1) : ℝ) ^ 2 < 1 / ↑n := by
  -- Since the series is monotone, we can compare the sum to the integral.
  have h_integral : ∑' m : ℕ, (1 : ℝ) / (m + n + 1) ^ 2 < ∑' m : ℕ, (1 : ℝ) / (m + n) / (m + n + 1)
      := by
    fapply Summable.tsum_lt_tsum
    focus
      exact 0
    · exact fun x => by rw [div_div,
                            div_le_div_iff₀] <;> ring_nf <;> nlinarith only [ show (n : ℝ) ≥ 1 by norm_cast ]
    · rw [ div_div, div_lt_div_iff₀ ] <;> norm_cast <;> nlinarith [ USize.le_size ]
    · exact_mod_cast summable_nat_add_iff (n + 1) |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two
    · field_simp
      exact Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> nlinarith) (summable_nat_add_iff n |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
  -- The series $\sum_{m=n}^{\infty} \frac{1}{m(m+1)}$ is a telescoping series.
  have h_telescoping :
      ∀ N : ℕ, ∑ m ∈ Finset.range N, (1 : ℝ) / (m + n) / (m + n + 1) = 1 / n - 1 / (N + n) := by
    intro N; induction N <;> simp_all +decide [ Finset.sum_range_succ ]
    -- Combine and simplify the terms on the left-hand side.
    field_simp
    ring
  -- Taking the limit of the telescoping series as $N$ approaches infinity, we get $\sum_{m=n}^{\infty} \frac{1}{m(m+1)} = \frac{1}{n}$.
  have h_limit : Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, (1 : ℝ) / (m + n) / (m + n + 1)) Filter.atTop (nhds (1 / n)) := by
    have h_zero :
        Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N + n))
          Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop <|
        Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa only [h_telescoping, sub_zero] using tendsto_const_nhds.sub h_zero
  simp +zetaDelta at *
  exact h_integral.trans_le <| le_of_tendsto_of_tendsto' (by exact (Summable.hasSum <| by exact (by { by_contra h; exact not_tendsto_atTop_of_tendsto_nhds (h_limit) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg (fun _ => by positivity) |>.1 h })) |> HasSum.tendsto_sum_nat) h_limit fun N => by simp +decide [ h_telescoping ]

/-
For θ ≠ 0 with |θ| ≤ π, the partial sums ∑_{k=1}^{N} (exp(-iθ))^k / k converge to
-log(1 - exp(-iθ)). This combines Dirichlet's test for convergence with Abel's
theorem for identification of the limit.
Note: We use Tendsto (not HasSum) because the series is only conditionally convergent.
-/
private lemma neg_log_one_sub_cexp_tendsto {θ : ℝ} (hθ : θ ≠ 0) (hθ_range : |θ| ≤ Real.pi) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        (Complex.exp (-(↑θ : ℂ) * I)) ^ (k + 1) / (↑(k + 1 : ℕ) : ℂ))
      Filter.atTop
      (nhds (-Complex.log (1 - Complex.exp (-(↑θ : ℂ) * I)))) := by
  by_contra h_contra
  have h_cauchy_seq : CauchySeq (fun N => ∑ k ∈ Finset.range N, (Complex.exp (-(↑θ : ℂ) * I)) ^ (k + 1) / (↑(k + 1) : ℂ)) := by
    have h_cauchy_seq : ∀ N : ℕ, ‖∑ k ∈ Finset.range N, (Complex.exp (-(↑θ : ℂ) * I)) ^ (k + 1)‖ ≤ 2 / ‖1 - Complex.exp (-(↑θ : ℂ) * I)‖ := by
      intro N
      have h_sum : ∑ k ∈ Finset.range N, (Complex.exp (-θ * I)) ^ (k + 1) = (Complex.exp (-θ * I) * (1 - (Complex.exp (-θ * I)) ^ N)) / (1 - Complex.exp (-θ * I)) := by
        rw [ eq_div_iff ]
        · exact Nat.recOn N (by norm_num) fun n ih => by norm_num [pow_succ,
                                                                   Finset.sum_range_succ] at *; linear_combination ih
        · norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]
          intro h; rw [sub_eq_zero,
                       eq_comm] at h; rw [ Real.cos_eq_one_iff ] at h; obtain ⟨k, hk⟩ := h; rcases k with ⟨_ | k⟩ <;> norm_num at hk <;> cases lt_or_gt_of_ne hθ <;> nlinarith [ Real.pi_pos, abs_le.mp hθ_range ]
      rw [ h_sum, norm_div, norm_mul ]
      gcongr
      norm_num [ Complex.norm_exp ]
      exact le_trans (norm_sub_le _ _) (by norm_num [ Complex.norm_exp ])
    have h_cauchy_seq : CauchySeq (fun N => ∑ k ∈ Finset.range N, (1 / (k + 1 : ℝ)) • (Complex.exp (-(↑θ : ℂ) * I)) ^ (k + 1)) := by
      apply_rules [ Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded ]
      · exact fun i j hij => by simpa using inv_anti₀ (by positivity) (by norm_cast; linarith)
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
    convert h_cauchy_seq using 2; norm_num [ div_eq_inv_mul ]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete h_cauchy_seq
  have h_abel : Filter.Tendsto (fun r : ℝ => ∑' k : ℕ, (Complex.exp (-(↑θ : ℂ) * I)) ^ (k + 1) / (↑(k + 1) : ℂ) * r ^ (k + 1)) (nhdsWithin 1 (Set.Iio 1)) (nhds L) := by
    have := @Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
    specialize @this (fun n => (Complex.exp (-θ * I)) ^ (n + 1) / (n + 1 : ℂ)) L
    simp_all +decide [ mul_comm, pow_succ ]
    convert this.mul (Complex.continuous_ofReal.continuousWithinAt) using 2 <;> norm_num [Function.comp,
                                                                                          mul_assoc,
                                                                                          mul_comm,
                                                                                          mul_left_comm,
                                                                                          tsum_mul_left]
  have h_abel : ∀ r : ℝ, 0 < r ∧ r < 1 → ∑' k : ℕ, (Complex.exp (-(↑θ : ℂ) * I)) ^ (k + 1) / (↑(k + 1) : ℂ) * r ^ (k + 1) = -Complex.log (1 - r * Complex.exp (-(↑θ : ℂ) * I)) := by
    intro r hr
    have h_series : HasSum (fun k : ℕ => (r * Complex.exp (-(↑θ : ℂ) * I)) ^ (k + 1) / (↑(k + 1) : ℂ)) (-Complex.log (1 - r * Complex.exp (-(↑θ : ℂ) * I))) := by
      have h_series : HasSum (fun k : ℕ => (r * Complex.exp (-(↑θ : ℂ) * I)) ^ k / (↑k : ℂ)) (-Complex.log (1 - r * Complex.exp (-(↑θ : ℂ) * I))) := by
        convert Complex.hasSum_taylorSeries_neg_log _ using 1
        simpa [ Complex.norm_exp, abs_of_pos hr.1 ] using hr.2
      simpa using (hasSum_nat_add_iff' 1).2 h_series
    rw [← h_series.tsum_eq]
    apply tsum_congr
    intro k
    rw [mul_pow]
    ring
  have h_abel_limit : Filter.Tendsto (fun r : ℝ => -Complex.log (1 - r * Complex.exp (-(↑θ : ℂ) * I))) (nhdsWithin 1 (Set.Iio 1)) (nhds (-Complex.log (1 - Complex.exp (-(↑θ : ℂ) * I)))) := by
    refine Filter.Tendsto.neg ?_
    refine Filter.Tendsto.comp (Complex.differentiableAt_log ?_ |> DifferentiableAt.continuousAt) ?_
    · norm_num [ Complex.slitPlane, Complex.exp_re, Complex.exp_im ]
      by_cases h_sin_zero : Real.sin θ = 0
      · rw [ Real.sin_eq_zero_iff ] at h_sin_zero
        rcases h_sin_zero with ⟨n, rfl⟩; rcases n with ⟨_ | _ | n⟩ <;> norm_num at *
        · rw [ abs_of_nonneg, abs_of_nonneg ] at hθ_range <;> nlinarith [ Real.pi_pos ]
        · norm_num [ abs_of_nonneg Real.pi_pos.le ] at *
          norm_num [ show (‹ℕ› : ℕ) = 0 by exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (by rw [ ← @Nat.cast_lt ℝ ]; push_cast; nlinarith [ Real.pi_pos, abs_of_nonpos (by linarith : (-1 + -↑‹ℕ› : ℝ) ≤ 0) ])) ] at *
      · exact Or.inr h_sin_zero
    · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ <| by norm_num)
  exact h_contra <| hL.trans <| by simpa using tendsto_nhds_unique ‹Filter.Tendsto (fun r : ℝ => ∑' k : ℕ, cexp (-↑θ * I) ^ (k + 1) / ↑ (k + 1) * ↑r ^ (k + 1)) (nhdsWithin 1 (Set.Iio 1)) (nhds L) › <| h_abel_limit.congr' <| Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one) fun x hx => h_abel x hx ▸ rfl

/-- The partial sums of h_fun converge: ∑_{m=0}^{N-1} exp(-i(m+n+1)θ)/(m+n+1) → h_fun n θ
as N → ∞, for θ ≠ 0 with |θ| ≤ π. -/
private lemma h_fun_partial_sum_tendsto (n : ℕ) {θ : ℝ} (hθ : θ ≠ 0) (hθ_range : |θ| ≤ Real.pi) :
    Filter.Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.range N,
        Complex.exp (-(↑(m + n + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(m + n + 1 : ℕ) : ℂ))
      Filter.atTop
      (nhds (h_fun n θ)) := by
  set z := Complex.exp (-(↑θ : ℂ) * I)
  set f := fun k : ℕ => z ^ (k + 1) / (↑(k + 1 : ℕ) : ℂ)
  -- Each summand equals f(m+n)
  have h_term :
      ∀ m, Complex.exp (-(↑(m + n + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(m + n + 1 : ℕ) : ℂ) = f (m + n) := by
    intro m; simp only [f]; congr 1
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- Rewrite: ∑_{m<N} f(m+n) = (∑_{k<n+N} f k) - (∑_{k<n} f k)
  have h_eq : ∀ N, ∑ m ∈ Finset.range N,
      Complex.exp (-(↑(m + n + 1 : ℕ) : ℂ) * ↑θ * I) / (↑(m + n + 1 : ℕ) : ℂ) =
      (∑ k ∈ Finset.range (n + N), f k) - (∑ k ∈ Finset.range n, f k) := by
    intro N; simp_rw [h_term]
    have h2 : ∀ m, f (m + n) = f (n + m) := fun m => by
      simp only [f]; congr 1 <;> (push_cast; ring)
    simp_rw [h2]; linear_combination -(Finset.sum_range_add f n N)
  simp_rw [h_eq]
  -- h_fun n θ = -log(1-z) - ∑_{k<n} f(k)
  have h_target : h_fun n θ = -Complex.log (1 - z) - ∑ k ∈ Finset.range n, f k := by
    simp only [h_fun, f]; congr 1
    apply Finset.sum_congr rfl; intro k _; congr 1
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h_target]
  exact ((neg_log_one_sub_cexp_tendsto hθ hθ_range).comp
    (Filter.tendsto_atTop_atTop_of_monotone (fun a b h => by omega) (fun n => ⟨n, by omega⟩))).sub_const _

/-
The Parseval-type bound on ∫|h|²: the L² norm of h on [-π,π] is < 2π/n.
This uses the fact that h has Fourier coefficients 1/m for m > n.
-/
lemma h_L2_bound (n : ℕ) (hn : 0 < n) :
    ∫ θ in (-Real.pi)..Real.pi, (‖h_fun n θ‖ ^ 2 : ℝ) < 2 * Real.pi / n := by
  exact (h_parseval_fatou_bound n hn).trans_lt (by
    exact mul_lt_mul_of_pos_left (sum_inv_sq_tail_bound n hn) (by positivity)
) |>.trans_eq (by ring)

/-
The near region integral bound:
∫_{-π/n}^{π/n} ‖exp(g-g(0))·h‖² < exp(2πs) · 2π/n.
-/
private lemma near_integral_bound {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ) {s : ℝ} (hs_pos : 0 < s)
    (hs_max : ∀ k : Fin n, ‖powerSum z (k.val + 1)‖ ≤ s) :
    ∫ θ in (-(Real.pi / ↑n))..((Real.pi / ↑n)),
      (‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 : ℝ) <
      Real.exp (2 * Real.pi * s) * (2 * Real.pi / ↑n) := by
  -- But this follows from the previous results:
  have h_integral_bound : ∫ θ in -(Real.pi / n)..Real.pi / n, ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 ≤ Real.exp (2 * Real.pi * s) * ∫ θ in -(Real.pi / n)..Real.pi / n, ‖h_fun n θ‖ ^ 2 := by
    rw [ intervalIntegral.integral_of_le, intervalIntegral.integral_of_le ]
    · -- Apply the bound |exp(g - g(0))| ≤ exp(πs) to each term in the integral.
      have h_exp_bound : ∀ θ ∈ Set.Icc (-(Real.pi / n)) (Real.pi / n), ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 ≤ Real.exp (2 * Real.pi * s) * ‖h_fun n θ‖ ^ 2 := by
        intros θ hθ
        have h_exp_bound : ‖Complex.exp (g_fun z θ - g_fun z 0)‖ ≤ Real.exp (Real.pi * s) := by
          have h_exp_bound : ‖g_fun z θ - g_fun z 0‖ ≤ Real.pi * s := by
            apply g_deviation_near hn z hs_pos.le hs_max
            exact abs_le.mpr ⟨by linarith [ hθ.1 ], by linarith [ hθ.2 ]⟩
          simpa [ Complex.norm_exp ] using Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm _) h_exp_bound)
        have hmul :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) h_exp_bound 2)
            (sq_nonneg (‖h_fun n θ‖))
        simpa [norm_mul, mul_pow, ← Real.exp_nat_mul, mul_assoc, mul_comm,
          mul_left_comm] using hmul
      rw [ ← MeasureTheory.integral_const_mul ]
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun x => sq_nonneg _
      · have h_integrable : IntervalIntegrable (fun θ => ‖h_fun n θ‖ ^ 2) volume (-Real.pi) Real.pi := by
          convert exp_g_h_sq_intervalIntegrable hn (fun _ => 0) _ using 1
          · unfold g_fun; norm_num
            unfold powerSum; norm_num
          · norm_num
        exact MeasureTheory.Integrable.const_mul (h_integrable.1.mono_set <| Set.Ioc_subset_Ioc (by linarith [ Real.pi_pos, show (Real.pi : ℝ) / n ≤ Real.pi by exact div_le_self Real.pi_pos.le <| mod_cast hn ]) <| by linarith [ Real.pi_pos, show (Real.pi : ℝ) / n ≤ Real.pi by exact div_le_self Real.pi_pos.le <| mod_cast hn ]) _
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using h_exp_bound x <| Set.Ioc_subset_Icc_self hx
    · exact neg_le_self (by positivity)
    · exact neg_le_self (by positivity)
  -- Using the L2 bound for h,
  have L2_bound : ∫ θ in -(Real.pi / n)..Real.pi / n, ‖h_fun n θ‖ ^ 2 ≤ ∫ θ in -(Real.pi)..Real.pi, ‖h_fun n θ‖ ^ 2 := by
    apply_rules [ intervalIntegral.integral_mono_interval ]
    · exact neg_le_neg (div_le_self Real.pi_pos.le (mod_cast hn))
    · exact neg_le_self (by positivity)
    · exact div_le_self Real.pi_pos.le <| mod_cast hn
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _
    · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ]
      have L2_bound : IntervalIntegrable (fun θ => ‖h_fun n θ‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi := by
        have := @exp_g_h_sq_intervalIntegrable n hn
        convert this (fun _ => 0) (fun _ => by norm_num) using 1
        unfold g_fun; norm_num
        unfold powerSum; norm_num
      rwa [Set.uIcc_of_le (by linarith [ Real.pi_pos ]),
           intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [ Real.pi_pos ])] at *
  exact h_integral_bound.trans_lt (mul_lt_mul_of_pos_left (L2_bound.trans_lt (h_L2_bound n hn)) (Real.exp_pos _))

/-
The far positive region integral bound:
∫_{π/n}^{π} ‖exp(g-g(0))·h‖² ≤ (π/n) · exp(2s(π+2)) / (1-4s).
-/
private lemma far_pos_integral_bound {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    {s : ℝ} (hs_pos : 0 < s) (hs_bound : s < 1 / 4)
    (hs_max : ∀ k : Fin n, ‖powerSum z (k.val + 1)‖ ≤ s) :
    ∫ θ in ((Real.pi / ↑n))..(Real.pi),
      (‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 : ℝ) ≤
      Real.pi / ↑n * Real.exp (2 * s * (Real.pi + 2)) / (1 - 4 * s) := by
  revert z
  intro z hz h_pow
  have h_integral_bound : ∫ θ in (Real.pi / n)..Real.pi, ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 ≤ ∫ θ in (Real.pi / n)..Real.pi, Real.exp (2 * s * (Real.pi + 2) + 4 * s * Real.log (n * θ / Real.pi)) * (Real.pi / (n * θ)) ^ 2 := by
    refine intervalIntegral.integral_mono_on
      (g := fun θ =>
        Real.exp (2 * s * (Real.pi + 2) + 4 * s * Real.log (n * θ / Real.pi)) *
          (Real.pi / (n * θ)) ^ 2) ?_ ?_ ?_ ?_
    · exact div_le_self Real.pi_pos.le <| mod_cast hn
    · have := exp_g_h_sq_intervalIntegrable hn z hz
      apply_rules [ this.mono_set, Set.Icc_subset_Icc ] <;> norm_num
      · exact Or.inl (by linarith [ Real.pi_pos, show (0 : ℝ) ≤ Real.pi / n by positivity ])
      · exact Or.inr (div_le_self Real.pi_pos.le (mod_cast hn))
    · apply_rules [ ContinuousOn.intervalIntegrable ]
      field_simp
      exact ContinuousOn.div (ContinuousOn.mul continuousOn_const <| ContinuousOn.rexp <| ContinuousOn.mul continuousOn_const <| ContinuousOn.add continuousOn_const <| ContinuousOn.mul continuousOn_const <| ContinuousOn.log (ContinuousOn.div_const (continuousOn_const.mul continuousOn_id) _) fun x hx => ne_of_gt <| div_pos (mul_pos (Nat.cast_pos.mpr hn) <| by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0) ]) <| by positivity) (ContinuousOn.mul continuousOn_const <| continuousOn_pow 2) fun x hx => ne_of_gt <| mul_pos (sq_pos_of_pos <| Nat.cast_pos.mpr hn) <| sq_pos_of_pos <| by cases Set.mem_uIcc.mp hx <;> nlinarith [Real.pi_pos,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           show (n : ℝ) ≥ 1 by norm_cast,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           div_mul_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0)]
    · intro x hx
      have h_exp_bound : ‖Complex.exp (g_fun z x - g_fun z 0)‖ ≤ Real.exp (s * (Real.pi + 2) + 2 * s * Real.log (n * x / Real.pi)) := by
        have h_exp_bound :
            ‖g_fun z x - g_fun z 0‖ ≤ s * (Real.pi + 2) + 2 * s * Real.log (n * x / Real.pi) := by
          convert g_deviation_far hn z hz hs_pos h_pow _ _ using 1
          · rw [ abs_of_nonneg (le_trans (by positivity) hx.1) ]
          · exact le_trans hx.1 (le_abs_self _)
          · exact abs_le.mpr ⟨by linarith [ hx.1, Real.pi_pos, div_nonneg Real.pi_pos.le (Nat.cast_nonneg n) ], by linarith [ hx.2, Real.pi_pos, div_nonneg Real.pi_pos.le (Nat.cast_nonneg n) ]⟩
        simpa [ Complex.norm_exp ] using Real.exp_le_exp.mpr (Complex.re_le_norm (g_fun z x - g_fun z 0) |> le_trans <| h_exp_bound)
      have h_h_bound : ‖h_fun n x‖ ≤ Real.pi / (n * x) := by
        convert h_pointwise_far_bound n hn _ _ using 1
        · rw [ abs_of_nonneg (le_trans (by positivity) hx.1) ]
        · exact le_trans hx.1 (le_abs_self _)
        · exact abs_le.mpr ⟨by linarith [ hx.1, Real.pi_pos, show (0 : ℝ) ≤ Real.pi / n by positivity ], by linarith [ hx.2, Real.pi_pos ]⟩
      have hmul :=
        mul_le_mul
          (pow_le_pow_left₀ (by positivity) h_exp_bound 2)
          (pow_le_pow_left₀ (by positivity) h_h_bound 2)
          (by positivity) (by positivity)
      have harg :
          2 * (s * (Real.pi + 2) + s * (2 * Real.log (x * ↑n / Real.pi))) =
            s * (2 * (Real.pi + 2)) + s * (4 * Real.log (x * ↑n / Real.pi)) := by
        ring
      simpa [norm_mul, mul_pow, ← Real.exp_nat_mul, mul_assoc, mul_comm,
        mul_left_comm, harg] using hmul
  -- Simplify the integral expression.
  have h_integral_simplified : ∫ θ in (Real.pi / n)..Real.pi, Real.exp (2 * s * (Real.pi + 2) + 4 * s * Real.log (n * θ / Real.pi)) * (Real.pi / (n * θ)) ^ 2 = (Real.pi / n) * Real.exp (2 * s * (Real.pi + 2)) * ∫ u in (1)..n, u ^ (4 * s - 2) := by
    have h_integral_simplified : ∫ θ in (Real.pi / n)..Real.pi, Real.exp (2 * s * (Real.pi + 2) + 4 * s * Real.log (n * θ / Real.pi)) * (Real.pi / (n * θ)) ^ 2 = (Real.pi / n) * ∫ u in (1)..n, Real.exp (2 * s * (Real.pi + 2) + 4 * s * Real.log u) * (Real.pi / (n * (Real.pi * u / n))) ^ 2 := by
      convert (intervalIntegral.integral_comp_div
        (f := fun u : ℝ =>
          Real.exp (2 * s * (Real.pi + 2) + 4 * s * Real.log u) *
            (Real.pi / (n * (Real.pi * u / n))) ^ 2)
        (a := Real.pi / n) (b := Real.pi) (c := Real.pi / n)
        (by positivity : Real.pi / n ≠ 0)) using 3 <;>
        norm_num [hn.ne', Real.pi_ne_zero, div_eq_mul_inv, mul_assoc, mul_comm,
          mul_left_comm]
    rw [ h_integral_simplified, ← intervalIntegral.integral_const_mul ]
    rw [ ← intervalIntegral.integral_const_mul ]; refine intervalIntegral.integral_congr fun x hx => ?_; by_cases hx' : x = 0 <;> simp +decide [ hx', mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, Real.exp_add, hn.ne', Real.pi_ne_zero ]
    focus
      ring_nf
    · rw [ Real.zero_rpow (by linarith) ]
    · rw [Real.rpow_sub (by cases Set.mem_uIcc.mp hx <;> linarith [ show (n : ℝ) ≥ 1 by norm_cast ]),
          Real.rpow_two]; ring_nf
      norm_num [Real.rpow_def_of_pos (show 0 < x by cases Set.mem_uIcc.mp hx <;> linarith [ show (n : ℝ) ≥ 1 by norm_cast ]),
                mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero]
      simp +decide [mul_left_comm (Real.pi ^ 2), Real.pi_ne_zero]
  rw [ integral_rpow ] at * <;> norm_num at *
  · refine le_trans h_integral_bound <| h_integral_simplified.le.trans ?_
    rw [ ← neg_div_neg_eq ]; ring_nf; norm_num
    rw [ show (-1 + s * 4 : ℝ) = - (1 - s * 4) by ring, inv_neg ]; ring_nf; norm_num
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le (inv_nonneg.mpr (Nat.cast_nonneg _))) (Real.exp_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (inv_nonneg.mpr (by linarith))
  · exact Or.inr ⟨by linarith, Set.notMem_uIcc_of_lt (by norm_num) (by norm_num; linarith)⟩

/-
The far negative region integral bound:
∫_{-π}^{-π/n} ‖exp(g-g(0))·h‖² ≤ (π/n) · exp(2s(π+2)) / (1-4s).
-/
private lemma far_neg_integral_bound {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    {s : ℝ} (hs_pos : 0 < s) (hs_bound : s < 1 / 4)
    (hs_max : ∀ k : Fin n, ‖powerSum z (k.val + 1)‖ ≤ s) :
    ∫ θ in (-Real.pi)..(-(Real.pi / ↑n)),
      (‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 : ℝ) ≤
      Real.pi / ↑n * Real.exp (2 * s * (Real.pi + 2)) / (1 - 4 * s) := by
  by_contra h_contra
  refine h_contra (le_trans
    (intervalIntegral.integral_mono_on
      (g := fun θ =>
        (Real.exp (s * (Real.pi + 2) + 2 * s *
          Real.log (n * |θ| / Real.pi))) ^ 2 *
            (Real.pi / (n * |θ|)) ^ 2) ?_ ?_ ?_ ?_) ?_)
  · exact neg_le_neg (div_le_self Real.pi_pos.le (mod_cast hn))
  · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ]
    contrapose! h_contra
    rw [ intervalIntegral.integral_undef ]
    · exact div_nonneg (mul_nonneg (div_nonneg Real.pi_pos.le (Nat.cast_nonneg _)) (Real.exp_nonneg _)) (by linarith)
    · rw [ intervalIntegrable_iff_integrableOn_Icc_of_le ]
      · rwa [ Set.uIcc_of_le (neg_le_neg <| div_le_self Real.pi_pos.le <| mod_cast hn) ] at h_contra
      · exact neg_le_neg (div_le_self Real.pi_pos.le (mod_cast hn))
  · apply_rules [ ContinuousOn.intervalIntegrable ]
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.rexp (ContinuousOn.add continuousOn_const <| ContinuousOn.mul continuousOn_const <| ContinuousOn.log ?_ ?_)
      · exact Continuous.continuousOn (by continuity)
      · norm_num [ Real.pi_ne_zero, hn.ne' ]
        intro x hx; cases Set.mem_uIcc.mp hx <;> nlinarith [Real.pi_pos,
                                                            show (n : ℝ) ≥ 1 by norm_cast,
                                                            mul_div_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0)]
    · refine ContinuousOn.pow ?_ 2
      refine continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ?_ ?_
      · exact ContinuousAt.mul continuousAt_const (continuousAt_id.abs)
      · simp +zetaDelta at *
        exact ⟨hn.ne', by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0) ]⟩
  · intro x hx
    have h_exp : ‖Complex.exp (g_fun z x - g_fun z 0)‖ ≤ Real.exp (s * (Real.pi + 2) + 2 * s * Real.log (n * |x| / Real.pi)) := by
      have h_exp_bound :
          ‖g_fun z x - g_fun z 0‖ ≤ s * (Real.pi + 2) + 2 * s * Real.log (n * |x| / Real.pi) := by
        apply g_deviation_far hn z hz hs_pos hs_max
        · cases abs_cases x <;> linarith [ hx.1, hx.2 ]
        · exact abs_le.mpr ⟨by linarith [ hx.1, Real.pi_pos ], by linarith [ hx.2, Real.pi_pos, show (Real.pi : ℝ) / n ≥ 0 by positivity ]⟩
      simpa [ Complex.norm_exp ] using Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm _) h_exp_bound)
    have h_h : ‖h_fun n x‖ ≤ Real.pi / (n * |x|) := by
      apply h_pointwise_far_bound n hn
      · cases abs_cases x <;> linarith [ hx.1, hx.2 ]
      · cases abs_cases x <;> linarith [hx.1, hx.2, Real.pi_pos,
                                        show (Real.pi : ℝ) / n ≥ 0 by positivity]
    simp
    simpa only [ mul_pow ] using mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h_exp 2) (pow_le_pow_left₀ (norm_nonneg _) h_h 2) (by positivity) (by positivity)
  · -- Simplify the integral expression.
    suffices h_simp : ∫ u in (Real.pi / n)..Real.pi, (Real.exp (s * (Real.pi + 2) + 2 * s * Real.log (n * u / Real.pi))) ^ 2 * (Real.pi / (n * u)) ^ 2 ≤ (Real.pi / n) * Real.exp (2 * s * (Real.pi + 2)) / (1 - 4 * s) by
      calc
        ∫ θ in -Real.pi..-(Real.pi / ↑n),
            (Real.exp (s * (Real.pi + 2) + 2 * s *
              Real.log (↑n * |θ| / Real.pi))) ^ 2 *
                (Real.pi / (↑n * |θ|)) ^ 2
            = ∫ u in (Real.pi / n)..Real.pi,
                (Real.exp (s * (Real.pi + 2) + 2 * s *
                  Real.log (n * u / Real.pi))) ^ 2 *
                    (Real.pi / (n * u)) ^ 2 := by
              rw [← intervalIntegral.integral_comp_neg]
              norm_num
              refine intervalIntegral.integral_congr fun x hx => ?_
              rw [abs_of_nonneg (by
                cases Set.mem_uIcc.mp hx <;>
                  nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast,
                    div_mul_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0)])]
        _ ≤ (Real.pi / n) * Real.exp (2 * s * (Real.pi + 2)) /
            (1 - 4 * s) := h_simp
    -- Simplify the integral expression further.
    suffices h_simp' : ∫ u in (Real.pi / n)..Real.pi, (Real.exp (2 * s * (Real.pi + 2))) * (n * u / Real.pi) ^ (4 * s) * (Real.pi ^ 2 / (n ^ 2 * u ^ 2)) ≤ (Real.pi / n) * Real.exp (2 * s * (Real.pi + 2)) / (1 - 4 * s) by
      convert h_simp' using 1
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [ ← Real.exp_nat_mul ]; ring_nf
      rw [ Real.rpow_def_of_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) (show 0 < u by cases Set.mem_uIcc.mp hu <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0) ])) (inv_pos.mpr Real.pi_pos)) ]; ring_nf
      rw [ Real.exp_add ]; ring
    -- Simplify the integral expression further by combining constants and powers of $u$.
    suffices h_simp'' : ∫ u in (Real.pi / n)..Real.pi, (Real.exp (2 * s * (Real.pi + 2))) * (n ^ (4 * s) / Real.pi ^ (4 * s)) * (Real.pi ^ 2 / n ^ 2) * u ^ (4 * s - 2) ≤ (Real.pi / n) * Real.exp (2 * s * (Real.pi + 2)) / (1 - 4 * s) by
      convert h_simp'' using 1
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Real.div_rpow (by exact mul_nonneg (Nat.cast_nonneg _) (by cases Set.mem_uIcc.mp hu <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0) ])) (by positivity),
          Real.mul_rpow (by positivity) (by cases Set.mem_uIcc.mp hu <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0) ])]
      rw [ Real.rpow_sub (by cases Set.mem_uIcc.mp hu <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi (by positivity : (n : ℝ) ≠ 0) ]) ]; norm_cast; ring
    rw [ intervalIntegral.integral_const_mul, integral_rpow ] <;> norm_num
    · rw [ Real.div_rpow (by positivity) (by positivity) ]; ring_nf
      norm_num [ Real.rpow_add (by positivity : 0 < (n : ℝ)), Real.rpow_neg_one ]; ring_nf
      norm_num [ Real.rpow_add (by positivity : 0 < Real.pi), Real.rpow_neg_one ]; ring_nf
      norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, hn.ne', Real.pi_ne_zero ]
      norm_num [mul_assoc, mul_left_comm (Real.pi ^ (s * 4)), mul_left_comm ((n : ℝ) ^ (s * 4)),
                ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _),
                ne_of_gt (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)]
      rw [ show (-1 + s * 4) = - (1 - s * 4) by ring, inv_neg ]; ring_nf; norm_num
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le (inv_nonneg.mpr (sq_nonneg _))) (inv_nonneg.mpr (by linarith))) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.exp_nonneg _)
    · exact Or.inr ⟨by linarith, Set.notMem_uIcc_of_lt (by positivity) (by positivity)⟩

lemma exp_h_integral_bound {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    {s : ℝ} (hs_pos : 0 < s) (hs_bound : s < 1 / 4)
    (hs_max : ∀ k : Fin n, ‖powerSum z (k.val + 1)‖ ≤ s) :
    ∫ θ in (-Real.pi)..Real.pi,
      (‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 : ℝ) <
      2 * Real.pi / (↑n : ℝ) * Real.exp (2 * Real.pi * s) *
        (1 + Real.exp (4 * s) / (1 - 4 * s)) := by
  by_contra h_contra
  push Not at h_contra
  have h_split : ∫ θ in (-Real.pi)..Real.pi, ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 = (∫ θ in (-Real.pi)..(-Real.pi / n), ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2) + (∫ θ in (-Real.pi / n)..(Real.pi / n), ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2) + (∫ θ in (Real.pi / n)..Real.pi, ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals,
        intervalIntegral.integral_add_adjacent_intervals] <;> apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ]
    · have h_integrable : IntervalIntegrable (fun θ => ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2) volume (-Real.pi) Real.pi := by
        apply_rules [ exp_g_h_sq_intervalIntegrable ]
      generalize_proofs at *; (
      rw [ intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [ Real.pi_pos, show (Real.pi : ℝ) / n ≥ 0 by positivity ]) ] at h_integrable; exact h_integrable.mono_set (by rw [ Set.uIcc_of_le (by linarith [ Real.pi_pos, show (Real.pi : ℝ) / n ≥ 0 by positivity ]) ]; exact Set.Icc_subset_Icc_right (by linarith [ Real.pi_pos, show (Real.pi : ℝ) / n ≤ Real.pi by exact div_le_self Real.pi_pos.le (mod_cast hn) ]));)
    · have h_integrable : IntervalIntegrable (fun θ => ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2) volume (-Real.pi) Real.pi := by
        apply_rules [ exp_g_h_sq_intervalIntegrable ]
      rw [ intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [ Real.pi_pos, show (Real.pi : ℝ) / n ≥ 0 by positivity ]) ] at h_integrable
      exact h_integrable.mono_set (by rw [ Set.uIcc_of_le (by rw [ div_le_iff₀ (by positivity) ]; nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast ]) ]; exact Set.Icc_subset_Icc (by linarith [ Real.pi_pos, show (Real.pi : ℝ) / n ≥ 0 by positivity ]) le_rfl)
    · refine MeasureTheory.IntegrableOn.mono_set
        (t := Set.Icc (-Real.pi) Real.pi) ?_ ?_
      · contrapose! h_contra
        rw [ intervalIntegral.integral_undef ]
        · exact mul_pos (mul_pos (by positivity) (Real.exp_pos _)) (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (Real.exp_nonneg _) (by linarith)))
        · rw [ intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [ Real.pi_pos ]) ]; aesop
      · exact fun x hx => ⟨by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, mul_div_cancel₀ (-Real.pi) (by positivity : (n : ℝ) ≠ 0) ], by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, mul_div_cancel₀ (-Real.pi) (by positivity : (n : ℝ) ≠ 0) ]⟩
    · refine MeasureTheory.IntegrableOn.mono_set
        (t := Set.Icc (-Real.pi) Real.pi) ?_ ?_
      · rw [ intervalIntegral.integral_of_le (by linarith [ Real.pi_pos ]) ] at h_contra
        exact (by rw [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ] at *; exact (by exact (by exact (by exact (by exact (by exact (by exact by { by_contra h; rw [ MeasureTheory.integral_undef h ] at h_contra; exact absurd h_contra (by exact not_le_of_gt (by exact mul_pos (mul_pos (by positivity) (Real.exp_pos _)) (by exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (Real.exp_nonneg _) (by linarith))))) })))))))
      · exact fun x hx => ⟨by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, mul_div_cancel₀ (-Real.pi) (by positivity : (n : ℝ) ≠ 0), mul_div_cancel₀ (Real.pi) (by positivity : (n : ℝ) ≠ 0) ], by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast, mul_div_cancel₀ (-Real.pi) (by positivity : (n : ℝ) ≠ 0), mul_div_cancel₀ (Real.pi) (by positivity : (n : ℝ) ≠ 0) ]⟩
  -- Apply the far_pos_integral_bound and far_neg_integral_bound lemmas to the respective integrals.
  have h_far_pos : ∫ θ in (Real.pi / n)..Real.pi, ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 ≤ (Real.pi / n) * Real.exp (2 * s * (Real.pi + 2)) / (1 - 4 * s) := by
    convert far_pos_integral_bound hn z hz hs_pos hs_bound hs_max using 1
  have h_far_neg : ∫ θ in (-Real.pi)..(-Real.pi / n), ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 ≤ (Real.pi / n) * Real.exp (2 * s * (Real.pi + 2)) / (1 - 4 * s) := by
    convert far_neg_integral_bound hn z hz hs_pos hs_bound hs_max using 1
    norm_num [ neg_div ]
  have h_near : ∫ θ in (-Real.pi / n)..(Real.pi / n), ‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 < Real.exp (2 * Real.pi * s) * (2 * Real.pi / n) := by
    convert near_integral_bound hn z hs_pos hs_max using 1; ring_nf
  rw [ show 2 * s * (Real.pi + 2) = 2 * Real.pi * s + 4 * s by ring, Real.exp_add ] at *
  ring_nf at *
  norm_num [ neg_add_eq_sub ] at *; linarith

/-! ## Key analytic inequality -/

/-- **Atkinson's Key Inequality**: For any configuration z₁ = 1, |zᵢ| ≤ 1,
if all power sums satisfy |sₖ| ≤ s with 0 < s < 1/4, then
1 < s²·exp(2πs)·(1+exp(4s)/(1-4s)).

Proved by chaining the Cauchy-Schwarz bound, Parseval bound, and integral estimate. -/
lemma atkinson_key_inequality {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    {s : ℝ} (hs_pos : 0 < s) (hs_bound : s < 1 / 4)
    (hs_max : ∀ k : Fin n, ‖powerSum z (k.val + 1)‖ ≤ s) :
    1 < atkinson_f s := by
  -- Obtain the three key bounds
  have hCS := atkinson_cs_bound hn z hz1 hz
  have hP := parseval_g_deriv_bound z hs_max
  have hE := exp_h_integral_bound hn z hz hs_pos hs_bound hs_max
  -- Name the integrals
  set P := ∫ θ in (-Real.pi)..Real.pi, (‖g_deriv_fun z θ‖ ^ 2 : ℝ) with hP_def
  set E := ∫ θ in (-Real.pi)..Real.pi,
    (‖Complex.exp (g_fun z θ - g_fun z 0) * h_fun n θ‖ ^ 2 : ℝ) with hE_def
  set B := 2 * Real.pi / (↑n : ℝ) * Real.exp (2 * Real.pi * s) *
    (1 + Real.exp (4 * s) / (1 - 4 * s)) with hB_def
  -- Key positivity facts
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hpi_pos := Real.pi_pos
  have hPub_pos : 0 < 2 * Real.pi * ↑n * s ^ 2 := by positivity
  -- P is non-negative (integral of non-negative function)
  have hP_nn : 0 ≤ P := by
    apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    intro θ _; positivity
  -- E must be positive (otherwise (2π)² ≤ P·E ≤ 0, contradiction)
  have hE_pos : 0 < E := by
    by_contra hle; push Not at hle
    have hE_nn : 0 ≤ E := by
      apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
      intro θ _; positivity
    have hE_zero : E = 0 := le_antisymm hle hE_nn
    have : P * E ≤ 0 := by rw [hE_zero]; simp
    nlinarith [sq_nonneg Real.pi]
  -- Chain: (2π)² ≤ P·E ≤ (2πns²)·E < (2πns²)·B
  have h1 : (2 * Real.pi) ^ 2 < (2 * Real.pi * ↑n * s ^ 2) * B :=
    calc (2 * Real.pi) ^ 2 ≤ P * E := hCS
      _ ≤ (2 * Real.pi * ↑n * s ^ 2) * E :=
          mul_le_mul_of_nonneg_right hP (le_of_lt hE_pos)
      _ < (2 * Real.pi * ↑n * s ^ 2) * B :=
          mul_lt_mul_of_pos_left hE hPub_pos
  -- Simplify: (2πns²)·B = (2π)²·atkinson_f(s)
  have hrhs : (2 * Real.pi * ↑n * s ^ 2) * B = (2 * Real.pi) ^ 2 * atkinson_f s := by
    unfold atkinson_f; rw [hB_def]
    have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have h14s : (1 : ℝ) - 4 * s ≠ 0 := by linarith
    field_simp
  -- Therefore 1 < atkinson_f(s)
  nlinarith [sq_nonneg Real.pi]

/-! ## Main theorem -/

/-- **Erdős Problem 519 (unit disk version)** (Turán's Power Sum Problem):
For complex numbers z₁, ..., zₙ with z₁ = 1 and |zᵢ| ≤ 1,
there exists k ∈ {1, ..., n} such that |∑ᵢ zᵢᵏ| > 1/6.

The proof proceeds by contradiction: assuming all power sums are ≤ 1/6,
Atkinson's key inequality gives 1 < f(1/6), but f(1/6) < 1 (numerical check). -/
theorem erdos519_unit_disk {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1)
    (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ k : Fin n, 1 / 6 < ‖powerSum z (k.val + 1)‖ := by
  by_contra h
  push Not at h
  have key := atkinson_key_inequality hn z hz1 hz
    (show (0 : ℝ) < 1 / 6 by norm_num) (show (1 : ℝ) / 6 < 1 / 4 by norm_num) h
  linarith [atkinson_f_sixth_lt_one]

/-- Power sum is invariant under permutation of the input sequence. -/
lemma powerSum_perm {n : ℕ} (z : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    powerSum (z ∘ σ) k = powerSum z k := by
  simp only [powerSum, Function.comp]
  exact Fintype.sum_equiv σ _ _ (fun i => rfl)

/-- Power sum scales as c^k when all terms are divided by c. -/
lemma powerSum_div {n : ℕ} (z : Fin n → ℂ) (c : ℂ) (k : ℕ) :
    powerSum (fun i => z i / c) k = powerSum z k / c ^ k := by
  simp [powerSum, div_pow, Finset.sum_div]

/-- **Erdős Problem 519** (Turán's Power Sum Problem):
For complex numbers z₁, ..., zₙ with z₁ = 1 (but no bound on |zᵢ|),
there exists k ∈ {1, ..., n} such that |∑ᵢ zᵢᵏ| > 1/6.

This generalizes `erdos519_unit_disk` by removing the |zᵢ| ≤ 1 hypothesis.
The proof reduces to the unit-disk case by swapping the largest-magnitude
term to index 0 and scaling all terms by its value. -/
theorem erdos519 {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1) :
    ∃ k : Fin n, 1 / 6 < ‖powerSum z (k.val + 1)‖ := by
  -- Find the index with maximum norm
  have ⟨i₀, _, hi₀_max⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  -- z i₀ has norm ≥ 1 since ‖z 0‖ = 1
  have hz0_norm : ‖z ⟨0, hn⟩‖ = 1 := by rw [hz1]; simp
  have hi₀_ge_one : 1 ≤ ‖z i₀‖ := by linarith [hi₀_max ⟨0, hn⟩ (Finset.mem_univ _)]
  have hzi₀_ne : z i₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hi₀_ge_one; linarith
  -- Swap i₀ to index 0 and scale by z i₀
  let σ := Equiv.swap (⟨0, hn⟩ : Fin n) i₀
  let w : Fin n → ℂ := fun i => z (σ i) / z i₀
  -- w 0 = z i₀ / z i₀ = 1
  have hw1 : w ⟨0, hn⟩ = 1 := by
    simp only [w, σ, Equiv.swap_apply_left]
    exact div_self hzi₀_ne
  -- ‖w i‖ ≤ 1 since i₀ has maximum norm
  have hw_bound : ∀ i, ‖w i‖ ≤ 1 := by
    intro i
    simp only [w, norm_div]
    rw [div_le_one (by positivity : 0 < ‖z i₀‖)]
    exact hi₀_max (σ i) (Finset.mem_univ _)
  -- Apply the unit-disk version
  obtain ⟨k, hk⟩ := erdos519_unit_disk hn w hw1 hw_bound
  refine ⟨k, ?_⟩
  -- powerSum w k = powerSum z k / (z i₀)^k (permutation-invariance + scaling)
  have hpw : powerSum w (k.val + 1) = powerSum z (k.val + 1) / (z i₀) ^ (k.val + 1) := by
    change powerSum (fun i => z (σ i) / z i₀) (k.val + 1) = _
    rw [show (fun i => z (σ i) / z i₀) = (fun i => (z ∘ σ) i / z i₀) from rfl]
    rw [powerSum_div, powerSum_perm]
  -- ‖powerSum z (k+1)‖ / ‖z i₀‖^(k+1) > 1/6 and ‖z i₀‖^(k+1) ≥ 1
  rw [hpw, norm_div, norm_pow] at hk
  calc 1 / 6 < ‖powerSum z (↑k + 1)‖ / ‖z i₀‖ ^ (↑k + 1) := hk
    _ ≤ ‖powerSum z (↑k + 1)‖ := div_le_self (norm_nonneg _) (one_le_pow₀ hi₀_ge_one)

end Erdos519

#print axioms Erdos519.erdos519
-- 'Erdos519.erdos519' depends on axioms: [propext, Classical.choice, Quot.sound]
