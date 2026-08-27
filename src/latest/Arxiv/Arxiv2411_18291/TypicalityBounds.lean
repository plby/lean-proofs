import Arxiv.Arxiv2411_18291.TypicalGraphExistence
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A polynomial times exponential bound for typicality failures

The number of neighborhood tests is polynomial in the vertex count for fixed
uniformity and typicality order. This estimate is suitable for probabilities
`p` and errors `c` that decay as small powers of the vertex count.
-/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291

theorem sub_le_choose_succ (n r : ℕ) : n - r ≤ n.choose (r + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hr : r ≤ n
    · rw [Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one]
      have hp := Nat.choose_pos hr
      omega
    · have hnr : n + 1 ≤ r := by omega
      simp only [Nat.sub_eq_zero_of_le hnr, Nat.zero_le]

theorem faceFamilies_count_le (n r h : ℕ) (hn : 1 ≤ n) :
    (∑ a ∈ range (h + 1), (n.choose r).choose a) ≤ (h + 1) * n ^ (r * h) := by
  calc
    _ ≤ ∑ _ ∈ range (h + 1), n ^ (r * h) := by
      apply sum_le_sum
      intro a ha
      calc
        _ ≤ (n.choose r) ^ a := Nat.choose_le_pow _ _
        _ ≤ (n ^ r) ^ a := Nat.pow_le_pow_left (Nat.choose_le_pow n r) a
        _ = n ^ (r * a) := (pow_mul _ _ _).symm
        _ ≤ n ^ (r * h) := pow_le_pow_right₀ hn (Nat.mul_le_mul_left r (Nat.le_of_lt_succ
          (mem_range.mp ha)))
    _ = _ := by simp

/-- A simpler explicit failure bound, with a polynomial prefactor. -/
theorem typicalFailureBound_le (n r h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h)
    {p c : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hsize : (2 * (h * r) : ℕ) ≤ n) :
    typicalFailureBound n r h p c ≤
      2 * (h + 2) * (n : ℝ) ^ (r * h) *
        Real.exp (-((n : ℝ) * p ^ h * c ^ 2 / 12)) := by
  have hr : r ≤ h * r := by simpa using Nat.mul_le_mul_right r hh
  have hnr : h * r ≤ n := by omega
  have hhalf : (n : ℝ) / 2 ≤ (n - h * r : ℕ) := by
    rw [Nat.cast_sub hnr, Nat.cast_mul]
    have hs : (2 : ℝ) * (h * r) ≤ n := by exact_mod_cast hsize
    nlinarith
  have hchoose : ((n - h * r : ℕ) : ℝ) ≤ (n.choose (r + 1) : ℝ) := by
    exact_mod_cast (Nat.sub_le_sub_left hr n).trans (sub_le_choose_succ n r)
  have hpow : p ^ h ≤ p := by simpa using pow_le_pow_of_le_one hp hp1 hh
  have hm : (n : ℝ) / 2 * p ^ h ≤ p * n.choose (r + 1) := by
    calc
      _ ≤ (n - h * r : ℕ) * p ^ h := mul_le_mul_of_nonneg_right hhalf (pow_nonneg hp _)
      _ ≤ (n.choose (r + 1) : ℝ) * p := mul_le_mul hchoose hpow (pow_nonneg hp _) (by positivity)
      _ = _ := mul_comm _ _
  have hden : 0 < 2 * (1 + 2 * c) := by positivity
  have hden6 : 2 * (1 + 2 * c) ≤ 6 := by linarith
  have htail (u : ℝ) (hu : (n : ℝ) / 2 * p ^ h ≤ u) :
      Real.exp (-(u * c ^ 2 / (2 * (1 + 2 * c)))) ≤
        Real.exp (-((n : ℝ) * p ^ h * c ^ 2 / 12)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    calc
      _ = ((n : ℝ) / 2 * p ^ h * c ^ 2) / 6 := by ring
      _ ≤ ((n : ℝ) / 2 * p ^ h * c ^ 2) / (2 * (1 + 2 * c)) :=
        div_le_div_of_nonneg_left (by positivity) hden hden6
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hu (sq_nonneg c)) hden.le
  have hcount : ((∑ a ∈ range (h + 1), (n.choose r).choose a : ℕ) : ℝ) ≤
      (h + 1) * (n : ℝ) ^ (r * h) := by exact_mod_cast faceFamilies_count_le n r h hn
  have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ (r * h) :=
    one_le_pow₀ (by exact_mod_cast hn)
  calc
    _ ≤ 2 * Real.exp (-((n : ℝ) * p ^ h * c ^ 2 / 12)) +
        ((∑ a ∈ range (h + 1), (n.choose r).choose a : ℕ) : ℝ) *
          (2 * Real.exp (-((n : ℝ) * p ^ h * c ^ 2 / 12))) := by
      unfold typicalFailureBound
      exact add_le_add
        (mul_le_mul_of_nonneg_left (htail _ hm) (by norm_num))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (htail _ (mul_le_mul_of_nonneg_right hhalf (pow_nonneg hp _))) (by norm_num))
          (Nat.cast_nonneg _))
    _ = (1 + ((∑ a ∈ range (h + 1), (n.choose r).choose a : ℕ) : ℝ)) *
        (2 * Real.exp (-((n : ℝ) * p ^ h * c ^ 2 / 12))) := by ring
    _ ≤ ((h + 2) * (n : ℝ) ^ (r * h)) *
        (2 * Real.exp (-((n : ℝ) * p ^ h * c ^ 2 / 12))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = _ := by ring

end Arxiv2411_18291
