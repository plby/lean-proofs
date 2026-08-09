import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

theorem Erdos485b.exists_complete_poly_with_sparse_square :
    ∀ (n : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
        @Exists.{1} (@Polynomial.{0} Int Int.instSemiring)
          fun (f : @Polynomial.{0} Int Int.instSemiring) ↦
          And (@Eq.{1} Nat (@Polynomial.natDegree.{0} Int Int.instSemiring f) n)
            (And
              (∀ (i : Nat),
                @LE.le.{0} Nat instLENat i n →
                  @Ne.{1} Int (@Polynomial.coeff.{0} Int Int.instSemiring f i)
                    (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (@LT.lt.{0} Real Real.instLT
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Finset.card.{0} Nat
                    (@Polynomial.support.{0} Int Int.instSemiring
                      (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Int Int.instSemiring) Nat
                        (@Polynomial.{0} Int Int.instSemiring)
                        (@instHPow.{0, 0} (@Polynomial.{0} Int Int.instSemiring) Nat
                          (@NPow.toPow.{0} (@Polynomial.{0} Int Int.instSemiring)
                            (@Monoid.toNPow.{0} (@Polynomial.{0} Int Int.instSemiring)
                              (@Semiring.toMonoid.{0} (@Polynomial.{0} Int Int.instSemiring)
                                (@Polynomial.semiring.{0} Int Int.instSemiring)))))
                        f (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 5)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 102)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 102) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 101) (instOfNatNat (nat_lit 101)))
                            (@Nat.instNeZeroSucc
                              (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))))))
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (Real.log
                            (@OfNat.ofNat.{0} Real (nat_lit 6)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
                          (Real.log
                            (@OfNat.ofNat.{0} Real (nat_lit 9)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                      (instOfNatNat (nat_lit 7)))))))))))
                    (@OfNat.ofNat.{0} Real (nat_lit 12)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))))))
  := by
  sorry

theorem Erdos485b.exists_complete_poly_with_sparse_square_improved :
    ∀ (n : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
        @Exists.{1} (@Polynomial.{0} Real Real.semiring) fun (f : @Polynomial.{0} Real Real.semiring) ↦
          And (@Eq.{1} Nat (@Polynomial.natDegree.{0} Real Real.semiring f) n)
            (And
              (∀ (i : Nat),
                @LE.le.{0} Nat instLENat i n →
                  @Ne.{1} Real (@Polynomial.coeff.{0} Real Real.semiring f i)
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
              (@LT.lt.{0} Real Real.instLT
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Finset.card.{0} Nat
                    (@Polynomial.support.{0} Real Real.semiring
                      (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                        (@Polynomial.{0} Real Real.semiring)
                        (@instHPow.{0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                          (@NPow.toPow.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Monoid.toNPow.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Semiring.toMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.semiring.{0} Real Real.semiring)))))
                        f (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 7)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 170)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 170) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 169) (instOfNatNat (nat_lit 169)))
                            (@Nat.instNeZeroSucc
                              (@OfNat.ofNat.{0} Nat (nat_lit 168) (instOfNatNat (nat_lit 168)))))))
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (Real.log
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
                          (Real.log
                            (@OfNat.ofNat.{0} Real (nat_lit 13)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 13) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 11)
                                      (instOfNatNat (nat_lit 11)))))))))))
                    (@OfNat.ofNat.{0} Real (nat_lit 14)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))))))))
  := by
  sorry
