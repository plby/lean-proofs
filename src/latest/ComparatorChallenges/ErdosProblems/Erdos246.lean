import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Erdos246

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open BigOperators

def FS (A : Set ℕ) : Set ℕ :=
  {s | ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧ s = ∑ x ∈ F, x}
def IsCompleteSeq (A : Set ℕ) : Prop :=
  Set.Finite {n | n ∉ FS A}
def Gamma (a b : ℕ) : Set ℕ :=
  {x | ∃ k l : ℕ, x = a^k * b^l}
end Erdos246

attribute [local instance] Classical.propDecidable

theorem Erdos246.erdos_246 :
    ∀ (a b : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b →
          a.Coprime b → Erdos246.IsCompleteSeq (Erdos246.Gamma a b)
  := by
  sorry
