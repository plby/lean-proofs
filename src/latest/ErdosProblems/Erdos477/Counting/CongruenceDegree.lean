/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The degree of a sextic auxiliary polynomial decreases with its congruence modulus.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.DegreeChoice

namespace Erdos477.Counting

lemma sextic_log_coefficient_bound (n : ℕ) (hn : 100000 ≤ n) :
    let s : ℝ := Fintype.card (SexticMonomial n)
    (100 : ℝ) / 41 * sexticWeight n + 3 * s ≤
      2 * (Real.sqrt 2 / 3 * s * Real.sqrt s) := by
  intro s
  obtain ⟨hsL, hsU, ht⟩ := sextic_size_bounds n hn
  have hnR : (100000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < s := by dsimp only [s]; nlinarith
  have hrL : (1732 : ℝ) / 1000 * n ≤ Real.sqrt s := by
    apply (Real.le_sqrt (by positivity) hs0.le).mpr
    dsimp only [s]
    nlinarith
  have hcoef : (2828 : ℝ) / 3000 ≤ 2 * Real.sqrt 2 / 3 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hpos := Real.sqrt_nonneg 2
    nlinarith
  have hprod := mul_le_mul (mul_le_mul hcoef hsL (by positivity) (by positivity))
    hrL (by positivity) (by positivity)
  have hcubic : (100000 : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hnR (sq_nonneg (n : ℝ))
    nlinarith only [h]
  dsimp only [s] at hprod ⊢
  nlinarith only [hprod, hcubic, hsU, ht, pow_nonneg hn0.le 3]

/-- The global degree choice remains valid after dividing the degree by a
modulus `q`, as long as `1 <= q <= B^(41/100)`. -/
theorem exists_sextic_congruence_degree_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B q : ℝ), 1 ≤ B → 1 ≤ q →
      q ≤ B ^ ((41 : ℝ) / 100) → ∃ n : ℕ,
      (n : ℝ) + 5 ≤ K * B ^ ((41 : ℝ) / 100) / q ∧
      let s := Fintype.card (SexticMonomial n)
      (s : ℝ) * Real.log s + sexticWeight n * Real.log B <
        Real.sqrt 2 / 3 * s * Real.sqrt s * (Real.log s + 2 * Real.log q) -
          C * s * Real.sqrt s - 3 * s * Real.log q := by
  obtain ⟨K, hK, hdegree⟩ := exists_sextic_degree_bound C hC
  refine ⟨K, hK, ?_⟩
  intro B q hB hq hqB
  have hB0 : 0 < B := by linarith
  have hq0 : 0 < q := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hqlog : Real.log q ≤ (41 : ℝ) / 100 * Real.log B := by
    have h := Real.log_le_log hq0 hqB
    rwa [Real.log_rpow hB0] at h
  let b := Real.exp (Real.log B - (100 : ℝ) / 41 * Real.log q)
  have hb : 1 ≤ b := Real.one_le_exp_iff.mpr (by linarith)
  have hb0 : 0 < b := by linarith
  have hlogb : Real.log b = Real.log B - (100 : ℝ) / 41 * Real.log q := Real.log_exp _
  have heq : b ^ ((41 : ℝ) / 100) = B ^ ((41 : ℝ) / 100) / q := by
    apply Real.log_injOn_pos (Real.rpow_pos_of_pos hb0 _)
      (div_pos (Real.rpow_pos_of_pos hB0 _) hq0)
    rw [Real.log_rpow hb0, hlogb, Real.log_div (by positivity) hq0.ne',
      Real.log_rpow hB0]
    ring
  obtain ⟨n, hn, hd, hsmall⟩ := hdegree b hb
  refine ⟨n, ?_, ?_⟩
  · rw [heq] at hd
    simpa only [mul_div_assoc] using hd
  · have hcoef := mul_le_mul_of_nonneg_right (sextic_log_coefficient_bound n hn) hlogq
    rw [hlogb] at hsmall
    dsimp only at hcoef hsmall ⊢
    nlinarith only [hsmall, hcoef]

#print axioms exists_sextic_congruence_degree_bound
-- 'Erdos477.Counting.exists_sextic_congruence_degree_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
