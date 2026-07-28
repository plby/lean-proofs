import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Card

attribute [local instance] Classical.propDecidable

noncomputable def Erdos434.non_representable_count :
    Set.{0} Nat → Nat
  := by
  sorry

noncomputable def Erdos434.A_opt :
    Nat → Nat → Finset.{0} Nat
  := by
  sorry

theorem Erdos434.main_theorem_final :
    ∀ (n k : Nat),
      @LE.le.{0} Nat instLENat k n →
        @GE.ge.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          ∀ (A : Finset.{0} Nat),
            @LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
                (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) A)
                (@Set.Icc.{0} Nat Nat.instPreorder
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) →
              @Eq.{1} Nat (@Finset.card.{0} Nat A) k →
                @Eq.{1} Nat
                    (@Finset.gcd.{0, 0} Nat Nat Nat.instCommMonoidWithZero
                      (@instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid.{0} Nat
                        Nat.instCommMonoidWithZero instStrongNormalizedGCDMonoidNat)
                      A (@id.{1} Nat))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @LE.le.{0} Nat instLENat
                    (Erdos434.non_representable_count
                      (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) A))
                    (Erdos434.non_representable_count
                      (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)
                        (Erdos434.A_opt n k)))
  := by
  sorry
