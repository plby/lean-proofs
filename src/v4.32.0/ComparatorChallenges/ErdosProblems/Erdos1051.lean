import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

theorem Erdos1051.erdos_1051_irrational :
    ∀ (a : Nat → Nat),
      @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder a →
        (∀ (n : Nat),
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (a n)) →
          @LT.lt.{0} Real Real.instLT
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@Filter.liminf.{0, 0} Real Nat
                (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Real
                  Real.instConditionallyCompleteLinearOrder)
                (fun (n : Nat) ↦
                  @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                    (@Nat.cast.{0} Real Real.instNatCast (a n))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat
                          (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        n)))
                (@Filter.atTop.{0} Nat Nat.instPreorder)) →
            Irrational
              (@tsum.{0, 0} Real Nat Real.instAddCommMonoid
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (fun (n : Nat) ↦
                  @HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast (a n))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (a
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (SummationFilter.unconditional.{0} Nat))
  := by
  sorry
