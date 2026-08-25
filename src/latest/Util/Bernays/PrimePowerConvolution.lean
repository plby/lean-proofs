import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Complex.Basic

/-!
# Local convolution identities for a square-root Euler factor
-/

open scoped Classical

namespace Bernays

theorem arithmetic_mul_primePower (f g : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (f * g) (p ^ e) = ∑ k ∈ Finset.range (e + 1), f (p ^ k) * g (p ^ (e - k)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => f i * g j), Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.pow_div (by have := Finset.mem_range.mp hk; omega) hp.pos]

theorem arithmetic_mul_primePower_geometric (f : ArithmeticFunction ℂ) {p : ℕ}
    (hp : p.Prime) (a : ℂ) (hf : ∀ k : ℕ, f (p ^ k) = a ^ k) (e : ℕ) :
    (f * f) (p ^ e) = (e + 1 : ℕ) * a ^ e := by
  rw [arithmetic_mul_primePower f f hp]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (e + 1)) : f (p ^ k) * f (p ^ (e - k)) = a ^ e := by
    rw [hf, hf, ← pow_add, Nat.add_sub_of_le (by have := Finset.mem_range.mp hk; omega)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem arithmetic_mul_primePower_delta (f g : ArithmeticFunction ℂ) {p : ℕ}
    (hp : p.Prime) (hg : ∀ k : ℕ, g (p ^ k) = if k = 0 then 1 else 0) (e : ℕ) :
    (f * g) (p ^ e) = f (p ^ e) := by
  rw [arithmetic_mul_primePower f g hp]
  rw [Finset.sum_eq_single e]
  · rw [Nat.sub_self, hg, if_pos rfl, mul_one]
  · intro k hk hke
    have hk₀ : e - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
    rw [hg, if_neg hk₀, mul_zero]
  · intro he
    exact False.elim (he (Finset.mem_range.mpr (Nat.lt_succ_self e)))

theorem pow_even_eq_one_of_sq_eq_one {a : ℂ} (ha : a ^ 2 = 1) {e : ℕ} (he : Even e) :
    a ^ e = 1 := by
  obtain ⟨k, hk⟩ := he
  rw [hk, ← two_mul, pow_mul, ha, one_pow]

end Bernays
