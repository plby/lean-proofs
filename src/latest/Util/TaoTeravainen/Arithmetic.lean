import ErdosProblems.Erdos248.Arithmetic

/-!
# Tao--Teräväinen: elementary multiplicity reductions

This file records the deterministic facts needed to pass from the exact
factorization expression in the Tao--Teräväinen statement to the usual
arithmetic function Ω. It also supplies the far-shift estimate used after
the finite weighted-sieve range has been exhausted.
-/

open scoped ArithmeticFunction.Omega

namespace TaoTeravainen

/-- Summing the multiplicities represented by a multiset's finsupp returns
its cardinality. -/
theorem toFinsupp_sum_counts (l : List ℕ) :
    (Multiset.toFinsupp (l : Multiset ℕ)).sum (fun _ k => k) =
      l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      change (Multiset.toFinsupp ({a} + (l : Multiset ℕ))).sum
          (fun _ k => k) = l.length + 1
      rw [Multiset.toFinsupp_add, Finsupp.sum_add_index']
      · simp [ih]
        omega
      · intro _; simp
      · intro _ b₁ b₂; simp

/-- The exponent sum of the natural factorization is the arithmetic function
Ω. -/
theorem factorization_sum_eq_Omega (n : ℕ) :
    n.factorization.sum (fun _ k => k) = Ω n := by
  rw [Nat.factorization_eq_primeFactorsList_multiset]
  rw [toFinsupp_sum_counts, ArithmeticFunction.cardFactors_apply]

/-- Every point in the factorization support has a positive exponent. -/
theorem support_card_le_factorization_sum (n : ℕ) :
    n.factorization.support.card ≤
      n.factorization.sum (fun _ k => k) := by
  classical
  rw [Finset.card_eq_sum_ones]
  unfold Finsupp.sum
  apply Finset.sum_le_sum
  intro p hp
  exact Nat.one_le_iff_ne_zero.mpr
    (Finsupp.mem_support_iff.mp hp)

/-- The total multiplicity beyond the first copy of each prime. -/
def factorizationExcess (n : ℕ) : ℕ :=
  n.factorization.sum (fun _ e => e - 1)

/-- The full exponent sum is the support cardinality plus the excess
multiplicity. -/
theorem factorization_sum_eq_support_card_add_excess (n : ℕ) :
    n.factorization.sum (fun _ e => e) =
      n.factorization.support.card + factorizationExcess n := by
  classical
  unfold factorizationExcess Finsupp.sum
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have he : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  change n.factorization p = 1 + (n.factorization p - 1)
  omega

/-- A list of integers all at least two has product at least two to its
length. -/
theorem two_pow_list_length_le_prod
    {l : List ℕ} (h : ∀ p ∈ l, 2 ≤ p) :
    2 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : 2 ≤ a := h a (by simp)
      have hl : ∀ p ∈ l, 2 ≤ p := by
        intro p hp
        exact h p (by simp [hp])
      simp only [List.length_cons, List.prod_cons]
      calc
        2 ^ (l.length + 1) = 2 * 2 ^ l.length := by rw [pow_succ]; omega
        _ ≤ 2 * l.prod := Nat.mul_le_mul_left 2 (ih hl)
        _ ≤ a * l.prod := Nat.mul_le_mul_right l.prod ha

/-- The full prime-factor count with multiplicity has the standard elementary
exponential bound. -/
theorem two_pow_Omega_le {m : ℕ} (hm : m ≠ 0) :
    2 ^ Ω m ≤ m := by
  rw [ArithmeticFunction.cardFactors_apply]
  calc
    2 ^ m.primeFactorsList.length ≤ m.primeFactorsList.prod := by
      apply two_pow_list_length_le_prod
      intro p hp
      exact (Nat.prime_of_mem_primeFactorsList hp).two_le
    _ = m := Nat.prod_primeFactorsList hm

/-- Exponent-comparison form of two_pow_Omega_le. -/
theorem Omega_le_of_le_two_pow {m a : ℕ} (hm : m ≠ 0)
    (hma : m ≤ 2 ^ a) :
    Ω m ≤ a := by
  rw [← Nat.pow_le_pow_iff_right (by decide : 1 < 2)]
  exact (two_pow_Omega_le hm).trans hma

/-- Once the shift is at least the binary scale containing n, the desired
linear Ω-bound is elementary. -/
theorem Omega_add_le_two_mul_of_le_pow {n L k : ℕ}
    (hn : n ≤ 2 ^ L) (hLk : L ≤ k) (hk : 1 ≤ k) :
    Ω (n + k) ≤ 2 * k := by
  apply Omega_le_of_le_two_pow (by omega)
  have hn_pow : n ≤ 2 ^ k :=
    hn.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hLk)
  have hk_pow : k ≤ 2 ^ k := k.lt_two_pow_self.le
  calc
    n + k ≤ 2 ^ k + 2 ^ k := Nat.add_le_add hn_pow hk_pow
    _ = 2 ^ (k + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ (2 * k) := by
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      omega

end TaoTeravainen
