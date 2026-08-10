import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

attribute [local instance] Classical.propDecidable

axiom dusart_mertens_product :
    ∀ (x : Real),
      @GE.ge.{0} Real Real.instLE x
          (@OfNat.ofNat.{0} Real (nat_lit 2278382)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2278382) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 2278381) (instOfNatNat (nat_lit 2278381)))
                (@Nat.instNeZeroSucc
                  (@OfNat.ofNat.{0} Nat (nat_lit 2278380) (instOfNatNat (nat_lit 2278380))))))) →
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Finset.prod.{0, 0} Nat Real Real.instCommMonoid
                (@Finset.filter.{0} Nat Nat.Prime Nat.decidablePrime
                  (Finset.range
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                          Real.instFloorRing)
                        x)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                fun (p : Nat) ↦
                @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@Nat.cast.{0} Real Real.instNatCast p)))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (Real.exp Real.eulerMascheroniConstant) (Real.log x)))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 5)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                (Real.exp Real.eulerMascheroniConstant))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat
                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (Real.log x) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

axiom dusart_pi_lower :
    ∀ (x : Real),
      @GE.ge.{0} Real Real.instLE x
          (@OfNat.ofNat.{0} Real (nat_lit 88789)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 88789) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 88788) (instOfNatNat (nat_lit 88788)))
                (@Nat.instNeZeroSucc
                  (@OfNat.ofNat.{0} Nat (nat_lit 88787) (instOfNatNat (nat_lit 88787))))))) →
        @LE.le.{0} Real Real.instLE
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) x
                (Real.log x))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) x
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat
                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (Real.log x) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                x)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat
                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (Real.log x) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Nat.cast.{0} Real Real.instNatCast
            (@Finset.card.{0} Nat
              (@Finset.filter.{0} Nat Nat.Prime Nat.decidablePrime
                (Finset.range
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                        Real.instFloorRing)
                      x)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))

axiom dusart_pi_upper :
    ∀ (x : Real),
      @GT.gt.{0} Real Real.instLT x
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast
            (@Finset.card.{0} Nat
              (@Finset.filter.{0} Nat Nat.Prime Nat.decidablePrime
                (Finset.range
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                        Real.instFloorRing)
                      x)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) x
                (Real.log x))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) x
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat
                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (Real.log x) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfScientific.ofScientific.{0} Real
                  (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) (nat_lit 253816) Bool.true
                  (nat_lit 5))
                x)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat
                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (Real.log x) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

axiom dusart_chebyshev :
    ∀ (x : Real),
      @GE.ge.{0} Real Real.instLE x
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
        @LT.lt.{0} Real Real.instLT
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
                (Finset.range
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                        Real.instFloorRing)
                      x)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                fun (n : Nat) ↦
                @DFunLike.coe.{1, 1, 1} (@ArithmeticFunction.{0} Real Real.instZero) Nat
                  (fun (x : Nat) ↦ Real) (@ArithmeticFunction.instFunLikeNat.{0} Real Real.instZero)
                  ArithmeticFunction.vonMangoldt n)
              x))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfScientific.ofScientific.{0} Real
                (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) (nat_lit 166) Bool.true
                (nat_lit 2))
              x)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat
                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (Real.log x) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

theorem Erdos490.main_theorem :
    @Exists.{1} Nat fun (N₀ : Nat) ↦
      ∀ (n : Nat),
        @LE.le.{0} Nat instLENat N₀ n →
          ∀ (A B : Finset.{0} Nat),
            @LE.le.{0} (Finset.{0} Nat)
                (@Preorder.toLE.{0} (Finset.{0} Nat)
                  (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                A
                (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) →
              @LE.le.{0} (Finset.{0} Nat)
                  (@Preorder.toLE.{0} (Finset.{0} Nat)
                    (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                  B
                  (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) →
                (∀ (a₁ : Nat),
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                          (@Finset.instSetLike.{0} Nat))
                        A a₁ →
                      ∀ (b₁ : Nat),
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                              (@Finset.instSetLike.{0} Nat))
                            B b₁ →
                          ∀ (a₂ : Nat),
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                  (@Finset.instSetLike.{0} Nat))
                                A a₂ →
                              ∀ (b₂ : Nat),
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                      (@Finset.instSetLike.{0} Nat))
                                    B b₂ →
                                  @Eq.{1} Nat
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        a₁ b₁)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        a₂ b₂) →
                                    And (@Eq.{1} Nat a₁ a₂) (@Eq.{1} Nat b₁ b₂)) →
                  @LT.lt.{0} Real Real.instLT
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat A))
                      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat B)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 60)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 60) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 59) (instOfNatNat (nat_lit 59)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))))))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat
                            (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@Nat.cast.{0} Real Real.instNatCast n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  := by
  sorry
