import Mathlib

/-!
# Iterating the largest-prime recurrence

The recurrence for restricted moment sums is a finite Volterra inequality.
Its exact iterated weights are the tail Euler products. The proof reduces
it to Mathlib's product-form discrete Grönwall inequality.
-/

open scoped BigOperators

namespace Erdos587

theorem hooley_volterra_bound (T Q a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hrec : ∀ n, T n ≤ Q n + ∑ i ∈ Finset.range n, a i * T i) (n : ℕ) :
    T n ≤ Q n + ∑ i ∈ Finset.range n,
      a i * Q i * ∏ j ∈ Finset.Ico (i + 1) n, (1 + a j) := by
  let U (k : ℕ) := ∑ i ∈ Finset.range k, a i * T i
  have hstep (k : ℕ) : U (k + 1) ≤ (1 + a k) * U k + a k * Q k := by
    change (∑ i ∈ Finset.range (k + 1), a i * T i) ≤ _
    rw [Finset.sum_range_succ]
    have hTk : T k ≤ Q k + U k := hrec k
    calc
      _ ≤ U k + a k * (Q k + U k) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hTk (ha k))
      _ = _ := by ring
  have hiter := discrete_gronwall_prod_general
    (u := U) (b := fun i => a i * Q i) (c := fun i => 1 + a i)
    (n₀ := 0) (fun i _ => hstep i)
    (fun i _ => add_nonneg zero_le_one (ha i)) (Nat.zero_le n)
  have hzero : U 0 = 0 := by simp [U]
  rw [hzero, zero_mul, zero_add, Nat.Ico_zero_eq_range] at hiter
  exact (hrec n).trans (add_le_add le_rfl hiter)

end Erdos587
