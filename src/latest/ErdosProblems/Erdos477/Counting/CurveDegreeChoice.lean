/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Choosing a fixed auxiliary degree for the one-dimensional determinant estimate.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveMonomials

namespace Erdos477.Counting

open scoped BigOperators

lemma exists_curve_auxiliary_index (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 2 ≤ n ∧ 1 ≤ ε * ((n : ℝ) - 1) := by
  refine ⟨⌈1 / ε⌉₊ + 2, by omega, ?_⟩
  have hceil := Nat.le_ceil (1 / ε)
  have hmul := mul_le_mul_of_nonneg_left hceil hε.le
  rw [mul_one_div_cancel hε.ne'] at hmul
  push_cast
  nlinarith

/-- The local divisibility exponent exceeds the total monomial weight by
a fixed positive margin when the modulus grows as `B^(1/d+ε)`. -/
theorem curve_degree_coefficient_inequality (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hεn : 1 ≤ ε * ((n : ℝ) - 1)) :
    ((∑ a : CurveMonomial d n, curveDegree a : ℕ) : ℝ) + (d * n : ℕ) / 2 ≤
      ((d * n).choose 2 : ℝ) * (1 / d + ε) := by
  let s : ℝ := d * n
  let t : ℝ := (∑ a : CurveMonomial d n, curveDegree a : ℕ)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by linarith
  have hs0 : 0 ≤ s := by dsimp only [s]; positivity
  have hpart : (n : ℝ) - 1 ≤ (s - 1) / d := by
    apply (le_div_iff₀ hd0).mpr
    dsimp only [s]
    nlinarith
  have hdiff : (d : ℝ) * ((n : ℝ) - 1) ≤ s - 1 := by
    dsimp only [s]
    nlinarith
  have heps : (d : ℝ) ≤ ε * (s - 1) := by
    have h1 := mul_le_mul_of_nonneg_left hεn hd0.le
    have h2 := mul_le_mul_of_nonneg_left hdiff hε
    nlinarith only [h1, h2]
  have hlarge : (n : ℝ) + d - 1 ≤ (s - 1) / d + ε * (s - 1) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hlarge hs0
  have hsum : 2 * t + 2 * s = s * ((d : ℝ) + n) := by
    dsimp only [s, t]
    exact_mod_cast (show 2 * (∑ a : CurveMonomial d n, curveDegree a) + 2 * (d * n) =
      d * n * (d + n) by simpa only [mul_assoc] using sum_curveDegree d n)
  have hchoose : 2 * ((d * n).choose 2 : ℝ) * (1 / d + ε) =
      s * ((s - 1) / d + ε * (s - 1)) := by
    rw [Nat.cast_choose_two]
    dsimp only [s]
    push_cast
    ring
  change t + ((d * n : ℕ) : ℝ) / 2 ≤ _
  rw [Nat.cast_mul]
  change t + s / 2 ≤ _
  nlinarith only [hsum, hscaled, hchoose]

/-- Above a constant height threshold the determinant's local lower bound
strictly exceeds its archimedean upper bound. -/
theorem curve_log_determinant_inequality (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hεn : 1 ≤ ε * ((n : ℝ) - 1))
    (B q : ℝ) (hB : 1 ≤ B) (hlarge : 2 * Real.log (d * n : ℕ) < Real.log B)
    (hq : (1 / (d : ℝ) + ε) * Real.log B ≤ Real.log q) :
    (d * n : ℕ) * Real.log (d * n : ℕ) +
      (∑ a : CurveMonomial d n, curveDegree a : ℕ) * Real.log B <
      ((d * n).choose 2 : ℝ) * Real.log q := by
  have hs : (0 : ℝ) < (d * n : ℕ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hcoeff := curve_degree_coefficient_inequality d n hd hn ε hε hεn
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hscaled := mul_le_mul_of_nonneg_right hcoeff hlogB
  have hgap := mul_lt_mul_of_pos_left hlarge (show 0 < ((d * n : ℕ) : ℝ) / 2 by positivity)
  have hq' := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg ((d * n).choose 2))
  nlinarith only [hscaled, hgap, hq']

#print axioms curve_log_determinant_inequality
-- 'Erdos477.Counting.curve_log_determinant_inequality' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
