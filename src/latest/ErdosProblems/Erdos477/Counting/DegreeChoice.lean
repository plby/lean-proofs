/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A rational exponent with sufficient slack for the sextic determinant method.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.VanishingDeterminant

namespace Erdos477.Counting

lemma sextic_size_bounds (n : ℕ) (hn : 100000 ≤ n) :
    let s : ℝ := Fintype.card (SexticMonomial n)
    let t : ℝ := sexticWeight n
    3 * (n : ℝ) ^ 2 ≤ s ∧ s ≤ 4 * (n : ℝ) ^ 2 ∧
      t ≤ (2001 : ℝ) / 1000 * (n : ℝ) ^ 3 := by
  intro s t
  have hnR : (100000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : s = 3 * (n : ℝ) ^ 2 + 24 * n + 56 := by
    dsimp only [s]
    exact_mod_cast card_sexticMonomial n
  have ht : 2 * t = 4 * (n : ℝ) ^ 3 + 57 * (n : ℝ) ^ 2 + 263 * n + 420 := by
    dsimp only [t, sexticWeight]
    exact_mod_cast sum_sexticDegree n
  have hcubic : (100000 : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hnR (sq_nonneg (n : ℝ))
    nlinarith only [h]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  nlinarith

lemma scalar_sextic_size_inequality (x s t B C : ℝ)
    (hx : 100000 ≤ x) (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hsL : 3 * x ^ 2 ≤ s) (hsU : s ≤ 4 * x ^ 2)
    (ht : t ≤ (2001 : ℝ) / 1000 * x ^ 3)
    (hlogx : 1000 * (C + 1) ≤ Real.log x)
    (hlogB : Real.log B ≤ (100 : ℝ) / 41 * Real.log x) :
    s * Real.log s + t * Real.log B <
      Real.sqrt 2 / 3 * s * Real.sqrt s * Real.log s - C * s * Real.sqrt s := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := by nlinarith
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlogsL : 2 * Real.log x ≤ Real.log s := by
    have h := Real.log_le_log (pow_pos hx0 2) (show x ^ 2 ≤ s by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogsU : Real.log s ≤ 3 * Real.log x := by
    have h := Real.log_le_log hs0 hsU
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hx0.ne'), Real.log_pow] at h
    have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show 4 ≤ x by linarith)
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hrL : (1732 : ℝ) / 1000 * x ≤ Real.sqrt s := by
    apply (Real.le_sqrt (by positivity) hs0.le).mpr
    nlinarith
  have hrU : Real.sqrt s ≤ 2 * x := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith⟩
  have h2 : (1414 : ℝ) / 1000 ≤ Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hpos := Real.sqrt_nonneg 2
    nlinarith
  have hlead :
      (489 : ℝ) / 100 * x ^ 3 * Real.log x ≤
        Real.sqrt 2 / 3 * s * Real.sqrt s * Real.log s := by
    have hprod :
        ((1414 : ℝ) / 3000) * (3 * x ^ 2) *
          ((1732 : ℝ) / 1000 * x) * (2 * Real.log x) ≤
        Real.sqrt 2 / 3 * s * Real.sqrt s * Real.log s := by
      have hcoef : (1414 : ℝ) / 3000 ≤ Real.sqrt 2 / 3 := by linarith
      have hfirst := mul_le_mul hcoef hsL (by positivity) (by positivity)
      have hsecond := mul_le_mul hfirst hrL (by positivity) (by positivity)
      exact mul_le_mul hsecond hlogsL (by positivity) (by positivity)
    have hnonneg : 0 ≤ x ^ 3 * Real.log x := by positivity
    nlinarith only [hprod, hnonneg]
  have hroots : s * Real.sqrt s ≤ 8 * x ^ 3 := by
    have h := mul_le_mul hsU hrU (Real.sqrt_nonneg s) (by positivity)
    nlinarith only [h]
  have hlogs : s * Real.log s ≤ (1 : ℝ) / 1000 * x ^ 3 * Real.log x := by
    have hprod := mul_le_mul hsU hlogsU (by linarith : 0 ≤ Real.log s) (by positivity)
    have hmul := mul_le_mul_of_nonneg_right (show (12000 : ℝ) ≤ x by linarith)
      (show 0 ≤ x ^ 2 * Real.log x by positivity)
    nlinarith only [hprod, hmul]
  have htlog := mul_le_mul ht hlogB hlogB0 (by positivity)
  have hupper : s * Real.log s + t * Real.log B ≤
      ((489 : ℝ) / 100 - 1 / 125) * x ^ 3 * Real.log x := by
    have hnonneg : 0 ≤ x ^ 3 * Real.log x := by positivity
    nlinarith only [hlogs, htlog, hnonneg]
  have hCroots := mul_le_mul_of_nonneg_left hroots hC
  have hgap : 8 * C * x ^ 3 < (1 : ℝ) / 125 * x ^ 3 * Real.log x := by
    have hsmall : 8 * C < Real.log x / 125 := by linarith
    have h := mul_lt_mul_of_pos_left hsmall (pow_pos hx0 3)
    nlinarith only [h]
  nlinarith only [hupper, hlead, hCroots, hgap]

/-- Explicit sufficient numerical conditions for all the evaluation
determinants to vanish; no asymptotic estimate is left as a hypothesis. -/
theorem sextic_size_inequality (n : ℕ) (hn : 100000 ≤ n) (B C : ℝ)
    (hC : 0 ≤ C) (hB : 1 ≤ B) (hlogn : 1000 * (C + 1) ≤ Real.log (n : ℝ))
    (hlogB : Real.log B ≤ (100 : ℝ) / 41 * Real.log n) :
    let s := Fintype.card (SexticMonomial n)
    (s : ℝ) * Real.log s + sexticWeight n * Real.log B <
      Real.sqrt 2 / 3 * s * Real.sqrt s * Real.log s - C * s * Real.sqrt s := by
  intro s
  obtain ⟨hsL, hsU, ht⟩ := sextic_size_bounds n hn
  exact scalar_sextic_size_inequality n s (sexticWeight n) B C (by exact_mod_cast hn)
    hC hB hsL hsU ht hlogn hlogB

/-- The numerical threshold is met by a degree of order `B^(41/100)`.
The multiplicative constant can depend on the fixed surface. -/
theorem exists_sextic_degree_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 1 ≤ B → ∃ n : ℕ,
      100000 ≤ n ∧ (n : ℝ) + 5 ≤ K * B ^ ((41 : ℝ) / 100) ∧
      let s := Fintype.card (SexticMonomial n)
      (s : ℝ) * Real.log s + sexticWeight n * Real.log B <
        Real.sqrt 2 / 3 * s * Real.sqrt s * Real.log s - C * s * Real.sqrt s := by
  let K := max 100000 (Real.exp (1000 * (C + 1)))
  have hK : 100000 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  refine ⟨K + 6, by positivity, ?_⟩
  intro B hB
  have hB0 : 0 < B := by linarith
  let b := B ^ ((41 : ℝ) / 100)
  have hb : 1 ≤ b := Real.one_le_rpow hB (by norm_num)
  have hb0 : 0 < b := by linarith
  let n := ⌈K * b⌉₊
  have hceil : K * b ≤ (n : ℝ) := Nat.le_ceil _
  have hKle : K ≤ (n : ℝ) :=
    (le_mul_of_one_le_right hK0.le hb).trans hceil
  have hn : 100000 ≤ n := by exact_mod_cast hK.trans hKle
  have hdegree : (n : ℝ) + 5 ≤ (K + 6) * b := by
    have hu : (n : ℝ) < K * b + 1 := Nat.ceil_lt_add_one (by positivity)
    nlinarith only [hu, hb]
  refine ⟨n, hn, hdegree, sextic_size_inequality n hn B C hC hB ?_ ?_⟩
  · have he : Real.exp (1000 * (C + 1)) ≤ (n : ℝ) :=
      (le_max_right _ _).trans hKle
    have hlog := Real.log_le_log (Real.exp_pos _) he
    simpa only [Real.log_exp] using hlog
  · have hbn : b ≤ (n : ℝ) :=
      (le_mul_of_one_le_left hb0.le (by linarith : 1 ≤ K)).trans hceil
    have hlog := Real.log_le_log hb0 hbn
    dsimp only [b] at hlog
    rw [Real.log_rpow hB0] at hlog
    linarith

#print axioms sextic_size_inequality
-- 'Erdos477.Counting.sextic_size_inequality' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
