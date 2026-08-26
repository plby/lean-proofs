/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Deterministic ingredients for Erdős Problem 521.

Informal proof: the cone criterion in Section 7 of the 29 April 2026
working note, recalled by Rob Sneiderman.
Formal proof: Codex.

https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_521_Kac.pdf
https://github.com/Robby955/erdos-521-zero-one
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- A finite power sum, with `n` terms. -/
def powerSum (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, a k * x ^ k

/-- Partial sums include the coefficient at index `r`. -/
def partialSum (a : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (r + 1), a k

/-- Finite Abel summation for a geometric weight. -/
theorem abel_identity (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    powerSum a (n + 1) x =
      (1 - x) * powerSum (partialSum a) n x + partialSum a n * x ^ n := by
  induction n with
  | zero => simp [powerSum, partialSum]
  | succ n ih =>
    simp only [powerSum, Finset.sum_range_succ] at ih ⊢
    simp only [partialSum, Finset.sum_range_succ, pow_succ] at ih ⊢
    nlinarith [ih]

/-- Nonnegative coefficient partial sums give a nonnegative power sum on `[0,1]`. -/
theorem powerSum_nonneg (a : ℕ → ℝ) (n : ℕ)
    (ha : ∀ r ≤ n, 0 ≤ partialSum a r) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ powerSum a (n + 1) x := by
  rw [abel_identity]
  apply add_nonneg
  · apply mul_nonneg (sub_nonneg.mpr hx1)
    exact Finset.sum_nonneg fun r hr ↦
      mul_nonneg (ha r (Nat.le_of_lt (Finset.mem_range.mp hr))) (pow_nonneg hx _)
  · exact mul_nonneg (ha n le_rfl) (pow_nonneg hx _)

/-- Strict positivity follows already from a positive constant coefficient. -/
theorem powerSum_pos (a : ℕ → ℝ) (n : ℕ)
    (ha : ∀ r ≤ n, 0 ≤ partialSum a r) (ha0 : 0 < a 0)
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < powerSum a (n + 1) x := by
  cases n with
  | zero => simpa [powerSum] using ha0
  | succ n =>
    rw [abel_identity]
    apply add_pos_of_pos_of_nonneg
    · apply mul_pos (sub_pos.mpr hx1)
      apply Finset.sum_pos'
      · intro r hr
        exact mul_nonneg (ha r (Nat.le_of_lt (Finset.mem_range.mp hr))) (pow_nonneg hx _)
      · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        simpa [partialSum] using ha0
    · exact mul_nonneg (ha (n + 1) le_rfl) (pow_nonneg hx _)

/-- The closed cone used for the even and odd coefficient sums. -/
def InCone (u v : ℝ) : Prop := |v| ≤ u

theorem inCone_iff (u v : ℝ) : InCone u v ↔ 0 ≤ u + v ∧ 0 ≤ u - v := by
  simp only [InCone, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem inCone_add {u v u' v' : ℝ} (h : InCone u v) (h' : InCone u' v') :
    InCone (u + u') (v + v') := by
  rw [inCone_iff] at h h' ⊢
  constructor <;> linarith [h.1, h.2, h'.1, h'.2]

theorem partialSum_add (a b : ℕ → ℝ) (r : ℕ) :
    partialSum (fun k ↦ a k + b k) r = partialSum a r + partialSum b r := by
  simp [partialSum, Finset.sum_add_distrib]

theorem partialSum_sub (a b : ℕ → ℝ) (r : ℕ) :
    partialSum (fun k ↦ a k - b k) r = partialSum a r - partialSum b r := by
  simp [partialSum, Finset.sum_sub_distrib]

theorem powerSum_add (a b : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    powerSum (fun k ↦ a k + b k) n x = powerSum a n x + powerSum b n x := by
  simp [powerSum, add_mul, Finset.sum_add_distrib]

theorem powerSum_sub (a b : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    powerSum (fun k ↦ a k - b k) n x = powerSum a n x - powerSum b n x := by
  simp [powerSum, sub_mul, Finset.sum_sub_distrib]

/-- Abel's cone criterion, with the nonzero constant coefficient available for
Littlewood polynomials. The endpoint values `x = ±1` are deliberately excluded. -/
theorem cone_powerSum_pos (a b : ℕ → ℝ) (n : ℕ)
    (hcone : ∀ r ≤ n, InCone (partialSum a r) (partialSum b r))
    (ha0 : 0 < a 0) (x : ℝ) (hx : |x| < 1) :
    0 < powerSum a (n + 1) (x ^ 2) + x * powerSum b (n + 1) (x ^ 2) := by
  have hplus : ∀ r ≤ n, 0 ≤ partialSum (fun k ↦ a k + b k) r := by
    intro r hr
    rw [partialSum_add]
    exact ((inCone_iff _ _).mp (hcone r hr)).1
  have hminus : ∀ r ≤ n, 0 ≤ partialSum (fun k ↦ a k - b k) r := by
    intro r hr
    rw [partialSum_sub]
    exact ((inCone_iff _ _).mp (hcone r hr)).2
  have hx' := abs_lt.mp hx
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hsumplus := powerSum_nonneg _ n hplus (x ^ 2) (sq_nonneg x) hx2.le
  have hsumminus := powerSum_nonneg _ n hminus (x ^ 2) (sq_nonneg x) hx2.le
  rw [powerSum_add] at hsumplus
  rw [powerSum_sub] at hsumminus
  have hstrict :
      0 < powerSum a (n + 1) (x ^ 2) + powerSum b (n + 1) (x ^ 2) ∨
      0 < powerSum a (n + 1) (x ^ 2) - powerSum b (n + 1) (x ^ 2) := by
    by_cases hab : 0 < a 0 + b 0
    · left
      simpa only [powerSum_add] using
        powerSum_pos _ n hplus hab (x ^ 2) (sq_nonneg x) hx2
    · right
      have hab' : 0 < a 0 - b 0 := by linarith
      simpa only [powerSum_sub] using
        powerSum_pos _ n hminus hab' (x ^ 2) (sq_nonneg x) hx2
  have hwplus : 0 < (1 + x) / 2 := by linarith [hx'.1]
  have hwminus : 0 < (1 - x) / 2 := by linarith [hx'.2]
  have hid :
      powerSum a (n + 1) (x ^ 2) + x * powerSum b (n + 1) (x ^ 2) =
        (1 + x) / 2 * (powerSum a (n + 1) (x ^ 2) + powerSum b (n + 1) (x ^ 2)) +
        (1 - x) / 2 * (powerSum a (n + 1) (x ^ 2) - powerSum b (n + 1) (x ^ 2)) := by
    ring
  rw [hid]
  rcases hstrict with hstrict | hstrict
  · exact add_pos_of_pos_of_nonneg (mul_pos hwplus hstrict)
      (mul_nonneg hwminus.le hsumminus)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hwplus.le hsumplus)
      (mul_pos hwminus hstrict)

/-- Splitting a power sum into its even and odd coefficients. -/
theorem powerSum_pair (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    powerSum a (2 * n) x =
      powerSum (fun k ↦ a (2 * k)) n (x ^ 2) +
        x * powerSum (fun k ↦ a (2 * k + 1)) n (x ^ 2) := by
  induction n with
  | zero => simp [powerSum]
  | succ n ih =>
    have hlen : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    simp only [hlen, powerSum, Finset.sum_range_succ] at ih ⊢
    rw [ih, pow_succ, pow_mul]
    ring

/-- Reversal of a finite coefficient list, evaluated at a reciprocal. -/
theorem reverse_powerSum_mul (a : ℕ → ℝ) (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    powerSum (fun k ↦ a (n - k)) (n + 1) x⁻¹ * x ^ n = powerSum a (n + 1) x := by
  unfold powerSum
  rw [Finset.sum_mul]
  conv_rhs => rw [← Finset.sum_range_reflect (fun k ↦ a k * x ^ k) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel, mul_assoc]
  congr 1
  have hpow : x ^ n = x ^ k * x ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hpow, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hx), one_mul]

end Erdos521
