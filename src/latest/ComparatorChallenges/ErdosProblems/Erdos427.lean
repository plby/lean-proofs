import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs

attribute [local instance] Classical.propDecidable

axiom shiu_consecutive_primes
    (l : ℕ) (hl : 1 ≤ l) (a q : ℕ) (hq : 1 ≤ q) (haq : Nat.Coprime a q) (N : ℕ) :
    ∃ m, N ≤ m ∧ ∀ i, i < l → Nat.nth Nat.Prime (m + i) ≡ a [MOD q]

namespace Erdos427

theorem erdos427 (n d : ℕ) (hd : 1 ≤ d) :
    ∃ k, 1 ≤ k ∧
      d ∣ (Finset.range k).sum (fun i => Nat.nth Nat.Prime (n + i)) := by
  sorry

end Erdos427
