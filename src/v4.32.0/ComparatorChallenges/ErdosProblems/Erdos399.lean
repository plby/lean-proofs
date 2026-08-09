import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Factorial.Basic

attribute [local instance] Classical.propDecidable

theorem Erdos399.erdos_399 :
    Iff False
      (Not
        (@Exists.{1} Nat fun (n : Nat) ↦
          @Exists.{1} Nat fun (x : Nat) ↦
            @Exists.{1} Nat fun (y : Nat) ↦
              @Exists.{1} Nat fun (k : Nat) ↦
                And
                  (@LT.lt.{0} Nat instLTNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) x y))
                  (And
                    (@LT.lt.{0} Nat instLTNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
                    (Or
                      (@Eq.{1} Nat n.factorial
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat
                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            x k)
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat
                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            y k)))
                      (@Eq.{1} Nat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n.factorial
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat
                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            y k))
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat
                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          x k))))))
  := by
  sorry
