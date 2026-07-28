import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

noncomputable def Pollack17.residuePrimesUpTo :
    (m : Nat) →
      @DirichletCharacter.{0} Complex
          (@CommGroupWithZero.toCommMonoidWithZero.{0} Complex
            (@Semifield.toCommGroupWithZero.{0} Complex
              (@Field.toSemifield.{0} Complex Complex.instField)))
          m →
        Real → Finset.{0} Nat
  := by
  sorry

axiom Pollack17.theorem_1_3 :
    ∀ (ε A : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A →
          @Exists.{1} Nat fun (m0 : Nat) ↦
            ∀ (m : Nat),
              @GT.gt.{0} Nat instLTNat m m0 →
                ∀
                  (χ :
                    @DirichletCharacter.{0} Complex
                      (@CommGroupWithZero.toCommMonoidWithZero.{0} Complex
                        (@Semifield.toCommGroupWithZero.{0} Complex
                          (@Field.toSemifield.{0} Complex Complex.instField)))
                      m),
                  @MulChar.IsQuadratic.{0, 0} (ZMod m)
                      (@CommRing.toCommMonoid.{0} (ZMod m) (ZMod.commRing m)) Complex Complex.commRing
                      χ →
                    @LE.le.{0} Real Real.instLE
                      ((Real.log (@Nat.cast.{0} Real Real.instNatCast m)).rpow A)
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Finset.card.{0} Nat (Pollack17.residuePrimesUpTo m χ ε)))

noncomputable def Erdos1141.Pa :
    Nat → Nat → Prop
  := by
  sorry

theorem Erdos1141.erdos_1141_variant :
    @Set.Finite.{0} Nat
      (@setOf.{0} Nat fun (n : Nat) ↦
        Erdos1141.Pa (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
  := by
  sorry

noncomputable def Erdos1141.Erdos1141Prop :
    Nat → Prop
  := by
  sorry

theorem Erdos1141.erdos_1141 :
    Not (Infinite.{1} (@Set.Elem.{0} Nat (@setOf.{0} Nat fun (n : Nat) ↦ Erdos1141.Erdos1141Prop n)))
  := by
  sorry
