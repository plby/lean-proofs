import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimeCounting

/-! # The length-one case of the BFT conclusion -/

namespace MaynardBFT

theorem single_prime :
    ∃ C : ℕ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ a : ℤ,
      Int.gcd a (q : ℤ) = 1 →
      ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧
        (∀ j, j < 1 → (Nat.nth Nat.Prime (r + j) : ℤ) ≡ a [ZMOD (q : ℤ)]) ∧
        Nat.nth Nat.Prime (r + 1 - 1) - Nat.nth Nat.Prime r ≤ q * C := by
  refine ⟨1, Nat.zero_lt_one, ?_⟩
  intro q hq a ha N
  obtain ⟨p, hpN, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_zmodEq
    (Nat.nth Nat.Prime N) hq.ne' (Int.isCoprime_iff_gcd_eq_one.mpr ha)
  refine ⟨Nat.count Nat.Prime p, ?_, ?_, ?_⟩
  · have hc := Nat.count_monotone Nat.Prime hpN.le
    simpa only [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] using hc
  · intro j hj
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj
    simpa only [hj0, Nat.add_zero, Nat.nth_count hp] using hpa
  · simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.zero_le]

end MaynardBFT
