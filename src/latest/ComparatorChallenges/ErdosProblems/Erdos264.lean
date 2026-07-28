import Mathlib.Algebra.Group.Nat.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos264.IsIrrationalitySequence :
    (Nat → Nat) → Prop
  := by
  sorry

theorem Erdos264.erdos_264.parts.i :
    Not
      (Erdos264.IsIrrationalitySequence fun (x : Nat) ↦
        @HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x)
  := by
  sorry

theorem Erdos264.erdos_264.variants.example :
    Erdos264.IsIrrationalitySequence fun (n : Nat) ↦
      @HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
  := by
  sorry
