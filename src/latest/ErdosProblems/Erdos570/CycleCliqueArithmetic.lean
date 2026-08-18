/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Arithmetic recurrence for the EFRS cycle--clique bound

The expansion argument produces maximum independent-set sizes `b i` on
successive BFS levels.  Its three-level inequality forces geometric growth.
This file records that integer argument without division or real powers.
-/

namespace Erdos570

/-- If each successive level satisfies the EFRS three-level inequality, then
the level sizes grow faster than powers of `a`. -/
theorem efrs_level_growth
    {a k : ℕ} (ha : 1 ≤ a) (b : ℕ → ℕ)
    (hb₀ : b 0 = 1) (hb₁ : a + 2 ≤ b 1)
    (hrec : ∀ i : ℕ, 1 ≤ i → i < k →
      (a + 1) * b i ≤ b (i - 1) + b (i + 1)) :
    ∀ i : ℕ, i ≤ k → a ^ i ≤ b i := by
  have hstep : ∀ i : ℕ, 1 ≤ i → i < k →
      a * b (i - 1) < b i → a * b i < b (i + 1) := by
    intro i hi hik hprev
    have hlt : b (i - 1) < b i := by
      have hmul : b (i - 1) ≤ a * b (i - 1) := by
        simpa using Nat.mul_le_mul_right (b (i - 1)) ha
      exact hmul.trans_lt hprev
    have hr := hrec i hi hik
    have hid : (a + 1) * b i = a * b i + b i := by ring
    rw [hid] at hr
    omega
  have hadj : ∀ i : ℕ, i < k → a * b i < b (i + 1) := by
    intro i hik
    induction i with
    | zero =>
        rw [hb₀]
        exact lt_of_lt_of_le (by omega) hb₁
    | succ i ih =>
        apply hstep (i + 1) (by omega) hik
        simpa using ih (by omega)
  intro i hik
  induction i with
  | zero => simp [hb₀]
  | succ i ih =>
      have hi : i < k := by omega
      have hpow : a ^ i ≤ b i := by
        exact ih (by omega)
      calc
        a ^ (i + 1) = a * a ^ i := by rw [pow_succ']
        _ ≤ a * b i := Nat.mul_le_mul_left a hpow
        _ ≤ b (i + 1) := (hadj i hi).le

/-- Hence a forbidden-independent-set bound contradicts the final BFS level
as soon as `n ≤ a^k`. -/
theorem efrs_level_growth_contradiction
    {a k n : ℕ} (ha : 1 ≤ a) (hn : n ≤ a ^ k)
    (b : ℕ → ℕ)
    (hb₀ : b 0 = 1) (hb₁ : a + 2 ≤ b 1)
    (hrec : ∀ i : ℕ, 1 ≤ i → i < k →
      (a + 1) * b i ≤ b (i - 1) + b (i + 1))
    (hsmall : b k < n) : False := by
  have hgrowth := efrs_level_growth ha b hb₀ hb₁ hrec k le_rfl
  omega

end Erdos570
