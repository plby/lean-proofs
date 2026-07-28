import Mathlib.Algebra.Polynomial.Degree.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos351.HasCompleteImage :
    @Polynomial.{0} Rat Rat.semiring → Prop
  := by
  sorry

theorem Erdos351.erdos_351 :
    Iff True
      (∀ (P : @Polynomial.{0} Rat Rat.semiring),
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Polynomial.natDegree.{0} Rat Rat.semiring P) →
          @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
              (@Polynomial.leadingCoeff.{0} Rat Rat.semiring P) →
            Erdos351.HasCompleteImage P)
  := by
  sorry
