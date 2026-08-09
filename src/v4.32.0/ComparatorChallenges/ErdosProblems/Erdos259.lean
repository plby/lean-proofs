import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Real.Irrational

attribute [local instance] Classical.propDecidable

theorem Erdos259.erdos_259 :
    Irrational
      (@tsum.{0, 0} Real Nat Real.instAddCommMonoid
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (fun (n : Nat) ↦
          @HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Int.cast.{0} Real Real.instIntCast
                (@HPow.hPow.{0, 0, 0} Int Nat Int
                  (@instHPow.{0, 0} Int Nat
                    (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                  (@DFunLike.coe.{1, 1, 1}
                    (@ArithmeticFunction.{0} Int
                      (@MulZeroClass.toZero.{0} Int
                        (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
                    Nat (fun (x : Nat) ↦ Int)
                    (@ArithmeticFunction.instFunLikeNat.{0} Int
                      (@MulZeroClass.toZero.{0} Int
                        (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
                    ArithmeticFunction.moebius n)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Nat.cast.{0} Real Real.instNatCast n))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat
                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              n))
        (SummationFilter.unconditional.{0} Nat))
  := by
  sorry
