import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos435

def generators (n : ℕ) : Set ℕ :=
  { m | ∃ i, 1 ≤ i ∧ i < n ∧ m = Nat.choose n i }
noncomputable def target (n : ℕ) : ℤ :=
  (Finset.sum n.factorization.support fun p =>
    (Finset.sum (Finset.Icc 1 (n.factorization p)) fun d =>
      (Nat.choose n (p ^ d) : ℤ)) * (p - 1)) - n
def generators_int (n : ℕ) : Set ℤ :=
  Int.ofNat '' (generators n)
def Representable (n : ℕ) : AddSubmonoid ℤ :=
  AddSubmonoid.closure (generators_int n)
end Erdos435

attribute [local instance] Classical.propDecidable

namespace Erdos435

theorem erdos_435 (n : ℕ)
    (hn : n ≠ 0)
    (h_not_prime_pow : ∀ p k, Nat.Prime p → n ≠ p ^ k) :
    target n ∉ Representable n ∧ ∀ x : ℤ, x > target n → x ∈ Representable n := by
  sorry

end Erdos435
