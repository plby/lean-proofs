import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

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

attribute [local instance] Classical.propDecidable

theorem Erdos56.erdos_56 :
    Iff
      (∀ (N : Nat),
        @GE.ge.{0} Nat instLENat N (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          ∀ (k : Nat),
            @GT.gt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @GE.ge.{0} Nat instLENat N (Nat.nth Nat.Prime k) →
                @Eq.{1} Nat (Erdos56.MaxWeaklyDivisible N k)
                  (@Finset.card.{0} Nat (Erdos56.FirstPrimesMultiples N k)))
      False
  := by
  sorry
