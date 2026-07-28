import Mathlib.Data.Nat.Basic
import Mathlib.Order.Monotone.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos281.Erdos281Hyp :
    (n : Nat → Nat) →
      @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder n →
        (∀ (i : Nat),
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (n i)) →
          Prop
  := by
  sorry

noncomputable def Erdos281.Erdos281Concl :
    (n : Nat → Nat) →
      @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder n →
        (∀ (i : Nat),
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (n i)) →
          Prop
  := by
  sorry

theorem Erdos281.Erdos_281 :
    ∀ (n : Nat → Nat) (hmono : @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder n)
      (hnpos :
        ∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (n i)),
      Erdos281.Erdos281Hyp n hmono hnpos → Erdos281.Erdos281Concl n hmono hnpos
  := by
  sorry
