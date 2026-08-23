/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.deprecated false

namespace Erdos56

open scoped Real
open scoped Nat

set_option maxHeartbeats 50000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.style.cases false
set_option aesop.warn.nonterminal false

set_option relaxedAutoImplicit false
set_option autoImplicit false

section PrimeCertificates

syntax "prime_cert " num : command
syntax "not_prime_cert " num " divisor " num : command
end PrimeCertificates

def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
    ∀ s ∈ A.powersetCard (k + 1), ¬ Set.Pairwise s Nat.Coprime

noncomputable def MaxWeaklyDivisible (N k : ℕ) : ℕ :=
  sSup { n : ℕ |
    ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧
      WeaklyDivisible k A ∧
      A.card = n }

noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
    (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)
end Erdos56

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos56

open scoped Classical in
theorem erdos_56 :
  (∀ᵉ (N ≥ 2) (k > 0),
      N ≥ k.nth Nat.Prime →
      MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card) ↔
    False := by
  sorry

end Erdos56
