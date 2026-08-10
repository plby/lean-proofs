import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Defs

namespace Erdos16

open scoped Nat

def U : Set ℕ :=
  { n | Odd n ∧ ¬ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p + 2^k }

def density_zero (S : Set ℕ) : Prop :=
  ∀ m a : ℕ, m > 0 → ¬ {x | ∃ k, x = m * k + a} ⊆ S
end Erdos16

attribute [local instance] Classical.propDecidable

theorem Erdos16.ErdosProblem16 :
    Not
      (@Exists.{1} Nat fun (m_0 : Nat) ↦
        @Exists.{1} Nat fun (a_0 : Nat) ↦
          And
            (@GT.gt.{0} Nat instLTNat m_0 (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Exists.{1} (Set.{0} Nat) fun (W : Set.{0} Nat) ↦
              And (Erdos16.density_zero W)
                (@Eq.{1} (Set.{0} Nat) Erdos16.U
                  (@Union.union.{0} (Set.{0} Nat) (@Set.instUnion.{0} Nat)
                    (@setOf.{0} Nat fun (x : Nat) ↦
                      @Exists.{1} Nat fun (h : Nat) ↦
                        @Eq.{1} Nat x
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m_0 h)
                            a_0))
                    W))))
  := by
  sorry
