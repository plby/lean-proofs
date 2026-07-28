import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos56.MaxWeaklyDivisible :
    Nat → Nat → Nat
  := by
  sorry

noncomputable def Erdos56.FirstPrimesMultiples :
    Nat → Nat → Finset.{0} Nat
  := by
  sorry

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
