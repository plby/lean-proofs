import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

noncomputable def UnitFractions.upper_density :
    Set.{0} Nat → Real
  := by
  sorry

noncomputable def UnitFractions.has_density :
    Set.{0} Nat → Real → Prop
  := by
  sorry

noncomputable def UnitFractions.rec_sum :
    Finset.{0} Nat → Rat
  := by
  sorry

theorem Erdos298.erdos298 :
    ∀ (A : Set.{0} Nat),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (UnitFractions.upper_density A) →
        @Exists.{1} (Finset.{0} Nat) fun (S : Finset.{0} Nat) ↦
          And
            (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
              (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) S) A)
            (@Eq.{1} Rat (UnitFractions.rec_sum S)
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  := by
  sorry

theorem Erdos298.erdos298_density :
    ∀ (A : Set.{0} Nat) (d : Real),
      UnitFractions.has_density A d →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
          @Exists.{1} (Finset.{0} Nat) fun (S : Finset.{0} Nat) ↦
            And
              (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
                (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) S) A)
              (@Eq.{1} Rat (UnitFractions.rec_sum S)
                (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  := by
  sorry
