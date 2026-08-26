import ErdosProblems.Erdos796.SemiprimeIdentity

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact evaluation of the finite baseline
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

/-- The baseline is exactly the large-prime count plus the corresponding
semiprime count, with the triangular small-prime contribution removed. -/
theorem baseline_eq_prime_add_semiprime (n : ℕ) :
    baseline n =
      (Nat.primeCounting n - Nat.primeCounting n.sqrt) +
      (semiprimeCount n -
        Nat.primeCounting n.sqrt *
          (Nat.primeCounting n.sqrt + 1) / 2) := by
  unfold baseline
  calc
    (∑ j ∈ Finset.Icc 1 n.sqrt,
        bucketCount n j * (1 + Nat.primeCounting j)) =
        ∑ j ∈ Finset.Icc 1 n.sqrt,
          (bucketCount n j +
            bucketCount n j * Nat.primeCounting j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.mul_add, Nat.mul_one]
    _ = (∑ j ∈ Finset.Icc 1 n.sqrt, bucketCount n j) +
        ∑ j ∈ Finset.Icc 1 n.sqrt,
          bucketCount n j * Nat.primeCounting j := by
      exact Finset.sum_add_distrib
    _ = _ := by
      rw [sum_bucketCount, sum_bucketCount_mul_primeCounting]

end Erdos796
