import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1197.I_inf :
    Set.{0} Real
  := by
  sorry

axiom Erdos1197.bm_approx_data :
    @Exists.{1} Nat fun (K₀ : Nat) ↦
      ∀ (k : Nat),
        @LE.le.{0} Nat instLENat K₀ k →
          @Exists.{1} Nat fun (N_k : Nat) ↦
            ∀ (ν : Nat),
              @LE.le.{0} Nat instLENat N_k ν →
                @Exists.{1} Nat fun (q : Nat) ↦
                  And
                    (@LT.lt.{0} Nat instLTNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
                    (And
                      (∀ (y : Real),
                        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                            Erdos1197.I_inf y →
                          @Exists.{1} Nat fun (m : Nat) ↦
                            And
                              (@LT.lt.{0} Nat instLTNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
                              (And
                                (@Membership.mem.{0, 0} Real (Set.{0} Real)
                                  (@Set.instMembership.{0} Real)
                                  (@Set.Ioo.{0} Real Real.instPreorder
                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                      (@instHMul.{0} Real Real.instMul)
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real
                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (@OfNat.ofNat.{0} Real (nat_lit 8)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                (instOfNatNat (nat_lit 7)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                  (instOfNatNat (nat_lit 6)))))))
                                        (@OfNat.ofNat.{0} Real (nat_lit 9)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                (instOfNatNat (nat_lit 8)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                  (instOfNatNat (nat_lit 7))))))))
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat
                                          (@NPow.toPow.{0} Real
                                            (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                (instOfNatNat (nat_lit 1)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                  (instOfNatNat (nat_lit 0)))))))
                                        ν))
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat
                                        (@NPow.toPow.{0} Real
                                          (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                          (@Nat.instAtLeastTwoHAddOfNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                              (instOfNatNat (nat_lit 1)))
                                            (@Nat.instNeZeroSucc
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                (instOfNatNat (nat_lit 0)))))))
                                      ν))
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@Nat.cast.{0} Real Real.instNatCast m) y))
                                (@Exists.{1} Int fun (n : Int) ↦
                                  @LT.lt.{0} Real Real.instLT
                                    (@abs.{0} Real Real.lattice Real.instAddGroup
                                      (@HSub.hSub.{0, 0, 0} Real Real Real
                                        (@instHSub.{0} Real Real.instSub)
                                        (Real.logb
                                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                              (@Nat.instAtLeastTwoHAddOfNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                  (instOfNatNat (nat_lit 1)))
                                                (@Nat.instNeZeroSucc
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                    (instOfNatNat (nat_lit 0)))))))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                            (@instHMul.{0} Real Real.instMul)
                                            (@Nat.cast.{0} Real Real.instNatCast m) y))
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real
                                            (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@Int.cast.{0} Real Real.instIntCast n)
                                          (@Nat.cast.{0} Real Real.instNatCast q))))
                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                      (@instHDiv.{0} Real
                                        (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                      (@OfNat.ofNat.{0} Real (nat_lit 1)
                                        (@One.toOfNat1.{0} Real Real.instOne))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                        (@instHMul.{0} Real Real.instMul)
                                        (@Nat.cast.{0} Real Real.instNatCast q)
                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                          (@instHPow.{0, 0} Real Nat
                                            (@NPow.toPow.{0} Real
                                              (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                              (@Nat.instAtLeastTwoHAddOfNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                  (instOfNatNat (nat_lit 1)))
                                                (@Nat.instNeZeroSucc
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                    (instOfNatNat (nat_lit 0)))))))
                                          k))))))
                      (∀ (n : Nat),
                        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                            (@Set.Ioo.{0} Real Real.instPreorder
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real
                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat.{0} Real (nat_lit 7)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                            (instOfNatNat (nat_lit 5)))))))
                                  (@OfNat.ofNat.{0} Real (nat_lit 8)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                            (instOfNatNat (nat_lit 6))))))))
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                            (instOfNatNat (nat_lit 0)))))))
                                  ν))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real
                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat.{0} Real (nat_lit 9)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                            (instOfNatNat (nat_lit 7)))))))
                                  (@OfNat.ofNat.{0} Real (nat_lit 8)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                            (instOfNatNat (nat_lit 6))))))))
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                            (instOfNatNat (nat_lit 0)))))))
                                  ν)))
                            (@Nat.cast.{0} Real Real.instNatCast n) →
                          @Exists.{1} Int fun (m : Int) ↦
                            @LT.lt.{0} Real Real.instLT
                              (@abs.{0} Real Real.lattice Real.instAddGroup
                                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                  (Real.logb
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                              (instOfNatNat (nat_lit 0)))))))
                                    (@Nat.cast.{0} Real Real.instNatCast n))
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real
                                      (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@Int.cast.{0} Real Real.instIntCast m)
                                    (@Nat.cast.{0} Real Real.instNatCast q))))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real
                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                  (@One.toOfNat1.{0} Real Real.instOne))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                              (instOfNatNat (nat_lit 2)))))))
                                    (@Nat.cast.{0} Real Real.instNatCast q))
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat
                                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                              (instOfNatNat (nat_lit 0)))))))
                                    k)))))

theorem Erdos1197.negative_answer :
    @Exists.{1} (Set.{0} Real) fun (E : Set.{0} Real) ↦
      And (@MeasurableSet.{0} Real Real.measurableSpace E)
        (And
          (@LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) E
            (@Set.Ioi.{0} Real Real.instPreorder
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
          (And
            (@LT.lt.{0} ENNReal
              (@Preorder.toLT.{0} ENNReal
                (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
              (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
              (@DFunLike.coe.{1, 1, 1}
                (@MeasureTheory.Measure.{0} Real
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
                (Set.{0} Real) (fun (x : Set.{0} Real) ↦ ENNReal)
                (@MeasureTheory.Measure.instFunLike.{0} Real
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) E))
            (∀ (x : Real),
              @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) Erdos1197.I_inf
                  x →
                @Set.Infinite.{0} Nat
                  (@setOf.{0} Nat fun (n : Nat) ↦
                    And
                      (@LT.lt.{0} Nat instLTNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                      (∀ (r : Nat),
                        @LT.lt.{0} Nat instLTNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
                          Not
                            (@Exists.{1} Real fun (e : Real) ↦
                              And
                                (@Membership.mem.{0, 0} Real (Set.{0} Real)
                                  (@Set.instMembership.{0} Real) E e)
                                (@Eq.{1} Real x
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                      (@instHDiv.{0} Real
                                        (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                      (@Nat.cast.{0} Real Real.instNatCast r)
                                      (@Nat.cast.{0} Real Real.instNatCast n))
                                    e))))))))
  := by
  sorry
