/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos569.Arithmetic
import Mathlib.Tactic.IntervalCases

/-! # Exact averaging estimates for the short cycles -/

namespace Erdos569

theorem sparse_half_margin {n m e : ℕ} (hn : 4 ≤ n) (hnm : n ≤ m)
    (havg : e * (n * (n - 1)) ≤
      m * ((n - (n / 2 + 1)) * (n - (n / 2 + 1) - 1))) :
    4 * e + 3 ≤ m := by
  let r := n - (n / 2 + 1)
  have hr : 2 * r ≤ n - 1 := by dsimp [r]; omega
  have hrp : 2 * (r - 1) ≤ n - 3 := by omega
  have hprod : 4 * (r * (r - 1)) ≤ (n - 1) * (n - 3) := by
    nlinarith only [Nat.mul_le_mul hr hrp]
  have hscaled := Nat.mul_le_mul_left 4 havg
  have hscaled' := Nat.mul_le_mul_left m hprod
  have hcancel : (4 * e * n) * (n - 1) ≤ (m * (n - 3)) * (n - 1) := by
    dsimp only [r] at hscaled'
    nlinarith only [hscaled, hscaled']
  have hmain := Nat.le_of_mul_le_mul_right hcancel (show 0 < n - 1 by omega)
  have heq : n - 3 + 3 = n := by omega
  nlinarith only [hmain, heq, hnm, hn]

theorem coloring_square_margin {m q : ℕ} (hm : 10 ≤ m) (hq : q * q ≤ 2 * m) :
    8 * q ≤ 3 * m + 4 := by
  by_cases hq4 : q ≤ 4
  · omega
  have hq5 : 5 ≤ q := by omega
  nlinarith only [hq, hq5, sq_nonneg (q - 5 : ℤ)]

theorem exact_partition_margin {n m q e : ℕ}
    (hn : 4 ≤ n) (hnm : n ≤ m) (hqhalf : 2 * q ≤ m)
    (hqsq : q * q ≤ 2 * m)
    (havg : e * (n * (n - 1)) ≤
      m * ((n - (n / 2 + 1)) * (n - (n / 2 + 1) - 1))) :
    4 * (q + e) + n + (n / 2 + 1) ≤ 4 * m := by
  have he := sparse_half_margin hn hnm havg
  by_cases hm10 : 10 ≤ m
  · have hq := coloring_square_margin hm10 hqsq
    omega
  have hm4 : 4 ≤ m := hn.trans hnm
  have hm9 : m ≤ 9 := by omega
  interval_cases m <;> try omega
  by_cases hn8 : n = 8
  · subst n
    norm_num at havg
    omega
  · omega

theorem remaining_region_exact_room {k n m a b g e q : ℕ}
    (hk : 5 ≤ k) (hn : 4 ≤ n) (hnm : n ≤ m)
    (ha : a = n / 2 + 1) (hqhalf : 2 * q ≤ m) (hqsq : q * q ≤ 2 * m)
    (hg : g + 1 ≤ n + (k - 1) * q)
    (hcounts : 1 + a + b + g = (k - 1) * m + 1)
    (havg : e * (n * (n - 1)) ≤
      m * ((n - (n / 2 + 1)) * (n - (n / 2 + 1) - 1))) :
    (k - 1) * e + 1 ≤ b ∧ n - a ≤ b := by
  have hmargin := exact_partition_margin hn hnm hqhalf hqsq havg
  have hsum : q + e ≤ m := by omega
  have hdiff : 4 * (m - (q + e)) ≥ n + a := by omega
  have hscale := Nat.mul_le_mul_right (m - (q + e))
    (show 4 ≤ k - 1 by omega)
  have hsplit : (k - 1) * m =
      (k - 1) * (q + e) + (k - 1) * (m - (q + e)) := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hsum]
  have hbudget : (k - 1) * e + 1 ≤ b := by
    rw [Nat.mul_add] at hsplit
    omega
  have hqm : 2 * (m - q) ≥ m := by omega
  have hscale' := Nat.mul_le_mul_right (m - q) (show 4 ≤ k - 1 by omega)
  have hsplit' : (k - 1) * m = (k - 1) * q + (k - 1) * (m - q) := by
    rw [← Nat.mul_add, Nat.add_sub_of_le (by omega : q ≤ m)]
  constructor
  · exact hbudget
  · omega

end Erdos569
