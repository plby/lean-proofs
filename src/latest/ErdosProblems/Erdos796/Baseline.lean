import ErdosProblems.Erdos796.Lift
import ErdosProblems.Erdos796.CanonicalExtension

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The prime and semiprime baseline

This file fixes the finite counting objects used in the last analytic stage
of the proof and proves the first exact bucket identity.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

/-- The constant singleton family, used only as a bookkeeping device. -/
def singletonFamily : ℕ → Finset ℕ := fun _ => {1}

/-- The baseline `B(n) = Σ_j N_j(n) (1 + π(j))`. -/
def baseline (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 n.sqrt,
    bucketCount n j * (1 + Nat.primeCounting j)

/-- Prime pairs `p ≤ q` whose product is at most `n`, including squares. -/
def semiprimePairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.primesLE n ×ˢ Nat.primesLE n).filter fun pq =>
    pq.1 ≤ pq.2 ∧ pq.1 * pq.2 ≤ n

/-- The semiprime-counting function `π₂(n)`. -/
def semiprimeCount (n : ℕ) : ℕ := (semiprimePairs n).card

theorem largePrimes_eq_newPrimes (n : ℕ) :
    largePrimes n = newPrimes n.sqrt n := rfl

theorem card_largePrimes (n : ℕ) :
    (largePrimes n).card =
      Nat.primeCounting n - Nat.primeCounting n.sqrt := by
  rw [largePrimes_eq_newPrimes]
  exact card_newPrimes (Nat.sqrt_le_self n)

/-- First exact baseline identity:
`Σ_j N_j(n) = π(n) - π(√n)`. -/
theorem sum_bucketCount (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n.sqrt, bucketCount n j) =
      Nat.primeCounting n - Nat.primeCounting n.sqrt := by
  have hregroup := sum_primes_eq_modelScore n singletonFamily
  have hleft :
      (∑ q ∈ largePrimes n, (singletonFamily (n / q)).card) =
        (largePrimes n).card := by
    simp [singletonFamily]
  have hright :
      modelScore n singletonFamily =
        ∑ j ∈ Finset.Icc 1 n.sqrt, bucketCount n j := by
    simp [modelScore, singletonFamily]
  rw [hleft, hright] at hregroup
  exact hregroup.symm.trans (card_largePrimes n)

end Erdos796
