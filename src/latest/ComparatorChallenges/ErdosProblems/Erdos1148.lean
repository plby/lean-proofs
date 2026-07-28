import Mathlib.Algebra.Group.Int.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1148.DukeTheoremStatement :
    Prop
  := by
  sorry

theorem Erdos1148.erdos_problem_1148 :
    Erdos1148.DukeTheoremStatement →
      @Exists.{1} Int fun (N : Int) ↦
        ∀ (n : Int),
          @GE.ge.{0} Int Int.instLEInt n N →
            @Exists.{1} Int fun (x : Int) ↦
              @Exists.{1} Int fun (y : Int) ↦
                @Exists.{1} Int fun (z : Int) ↦
                  And
                    (@Eq.{1} Int n
                      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                          (@HPow.hPow.{0, 0, 0} Int Nat Int
                            (@instHPow.{0, 0} Int Nat
                              (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                            x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@HPow.hPow.{0, 0, 0} Int Nat Int
                            (@instHPow.{0, 0} Int Nat
                              (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                            y (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@HPow.hPow.{0, 0, 0} Int Nat Int
                          (@instHPow.{0, 0} Int Nat
                            (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                          z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    (@LE.le.{0} Int Int.instLEInt
                      (@Max.max.{0} Int Int.instMax
                        (@HPow.hPow.{0, 0, 0} Int Nat Int
                          (@instHPow.{0, 0} Int Nat
                            (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                          x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Max.max.{0} Int Int.instMax
                          (@HPow.hPow.{0, 0, 0} Int Nat Int
                            (@instHPow.{0, 0} Int Nat
                              (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                            y (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@HPow.hPow.{0, 0, 0} Int Nat Int
                            (@instHPow.{0, 0} Int Nat
                              (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                            z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                      n)
  := by
  sorry
