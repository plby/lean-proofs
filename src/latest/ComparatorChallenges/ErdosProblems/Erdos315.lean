import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

noncomputable def Erdos315.sylvester :
    Nat → Nat
  := by
  sorry

noncomputable def Erdos315.vardi_constant :
    Real
  := by
  sorry

theorem Erdos315.erdos_315 :
    ∀ (a : Nat → Nat),
      (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (a i)) →
        @Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder a →
          @Eq.{1} Real
              (@tsum.{0, 0} Real Nat Real.instAddCommMonoid
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (fun (i : Nat) ↦
                  @HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@Nat.cast.{0} Real Real.instNatCast (a i)))
                (SummationFilter.unconditional.{0} Nat))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            (@Exists.{1} Nat fun (i : Nat) ↦ @Ne.{1} Nat (a i) (Erdos315.sylvester i)) →
              @LT.lt.{0} Real Real.instLT
                (@Filter.liminf.{0, 0} Real Nat
                  (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Real
                    Real.instConditionallyCompleteLinearOrder)
                  (fun (i : Nat) ↦
                    @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                      (@Nat.cast.{0} Real Real.instNatCast (a i))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat
                          (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Filter.atTop.{0} Nat Nat.instPreorder))
                Erdos315.vardi_constant
  := by
  sorry
