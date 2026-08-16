import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.PrimeFin

namespace Erdos649

def P (n : ℕ) : ℕ := (n.primeFactors).max.getD 0
def StrangePair (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p ≠ q ∧ ∀ n ≥ 2, P n * P (n + 1) ≠ p * q
end Erdos649

attribute [local instance] Classical.propDecidable

theorem Erdos649.infinite_strange_pairs :
    @Set.Infinite.{0} Nat
      (@Set.ofPred.{0} Nat fun (q : Nat) ↦
        Erdos649.StrangePair (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
  := by
  sorry
