import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos355.IsLambdaLacunary :
    Real → (Nat → Real) → Prop
  := by
  sorry

noncomputable def Erdos355.IsLacunary :
    (Nat → Nat) → Prop
  := by
  sorry

noncomputable def Erdos355.SubsetSums :
    (Nat → Real) → Set.{0} Real
  := by
  sorry

noncomputable def Erdos355.R_lambda :
    Real → Real
  := by
  sorry

noncomputable def Erdos355.S_cond :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos355.TargetInterval :
    (Nat → Real) → Set.{0} Real
  := by
  sorry

noncomputable def Erdos355.a_seq :
    Real → Nat → Nat
  := by
  sorry

theorem Erdos355.Theorem_1 :
    ∀ (lambda : Real),
      And
          (@LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lambda)
          (@LT.lt.{0} Real Real.instLT lambda
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
        @Exists.{1} (Nat → Nat) fun (n : Nat → Nat) ↦
          And
            (∀ (i : Nat),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (n i))
            (And
              (Erdos355.IsLambdaLacunary lambda fun (i : Nat) ↦
                @Nat.cast.{0} Real Real.instNatCast (n i))
              (And
                (@Filter.Tendsto.{0, 0} Nat Real
                  (fun (i : Nat) ↦
                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (n
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@Nat.cast.{0} Real Real.instNatCast (n i)))
                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                  (@nhds.{0} Real
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                (@LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real)
                  (@Inter.inter.{0} (Set.{0} Real) (@Set.instInter.{0} Real)
                    (@Set.Icc.{0} Real Real.instPreorder
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                    (@setOf.{0} Real fun (x : Real) ↦
                      @Exists.{1} Rat fun (q : Rat) ↦
                        @Eq.{1} Real x (@Rat.cast.{0} Real Real.instRatCast q)))
                  (Erdos355.SubsetSums fun (i : Nat) ↦
                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@Nat.cast.{0} Real Real.instNatCast (n i))))))
  := by
  sorry

theorem Erdos355.Theorem_2 :
    ∀ (lambda : Real),
      And
          (@LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lambda)
          (@LT.lt.{0} Real Real.instLT lambda
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
        @Eq.{1} Real (Erdos355.R_lambda lambda)
          (@tsum.{0, 0} Real Nat Real.instAddCommMonoid
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (fun (i : Nat) ↦
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@Nat.cast.{0} Real Real.instNatCast (Erdos355.a_seq lambda i)))
            (SummationFilter.unconditional.{0} Nat))
  := by
  sorry

theorem Erdos355.Theorem_3 :
    ∀ (Lambda lambda : Real),
      @GE.ge.{0} Real Real.instLE Lambda
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
        And
            (@LT.lt.{0} Real Real.instLT
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lambda)
            (@LT.lt.{0} Real Real.instLT lambda
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Lambda
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Lambda
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))) →
          @Exists.{1} (Nat → Nat) fun (n : Nat → Nat) ↦
            And
              (Erdos355.IsLambdaLacunary lambda fun (i : Nat) ↦
                @Nat.cast.{0} Real Real.instNatCast (n i))
              (And
                (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (n i))
                (And
                  (@Set.Infinite.{0} Nat
                    (@setOf.{0} Nat fun (i : Nat) ↦
                      @GT.gt.{0} Real Real.instLT
                        (@Nat.cast.{0} Real Real.instNatCast
                          (n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Lambda
                          (@Nat.cast.{0} Real Real.instNatCast (n i)))))
                  (@GE.ge.{0} (Set.{0} Real) (@Set.instLE.{0} Real)
                    (Erdos355.SubsetSums fun (i : Nat) ↦
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@Nat.cast.{0} Real Real.instNatCast (n i)))
                    (@Inter.inter.{0} (Set.{0} Real) (@Set.instInter.{0} Real)
                      (Erdos355.TargetInterval fun (i : Nat) ↦
                        @HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Nat.cast.{0} Real Real.instNatCast (n i)))
                      (@setOf.{0} Real fun (x : Real) ↦
                        @Exists.{1} Rat fun (q : Rat) ↦
                          @Eq.{1} Real x (@Rat.cast.{0} Real Real.instRatCast q))))))
  := by
  sorry

theorem Erdos355.Theorem_4 :
    ∀ (S : Set.{0} Nat),
      Erdos355.S_cond S →
        @Eq.{1} (Set.{0} Real)
          (Erdos355.SubsetSums fun (i : Nat) ↦
            @HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@Nat.cast.{0} Real Real.instNatCast
                (Nat.nth
                  (fun (x : Nat) ↦
                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S x)
                  i)))
          (@Inter.inter.{0} (Set.{0} Real) (@Set.instInter.{0} Real)
            (Erdos355.TargetInterval fun (i : Nat) ↦
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@Nat.cast.{0} Real Real.instNatCast
                  (Nat.nth
                    (fun (x : Nat) ↦
                      @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S x)
                    i)))
            (@setOf.{0} Real fun (x : Real) ↦
              @Exists.{1} Rat fun (q : Rat) ↦ @Eq.{1} Real x (@Rat.cast.{0} Real Real.instRatCast q)))
  := by
  sorry

theorem Erdos355.erdos_355 :
    @Exists.{1} (Nat → Nat) fun (A : Nat → Nat) ↦
      And (Erdos355.IsLacunary A)
        (@Exists.{1} Real fun (u : Real) ↦
          @Exists.{1} Real fun (v : Real) ↦
            And (@LT.lt.{0} Real Real.instLT u v)
              (∀ (q : Rat),
                @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                    (@Set.Ioo.{0} Real Real.instPreorder u v) (@Rat.cast.{0} Real Real.instRatCast q) →
                  @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat)
                    (@setOf.{0} Rat fun (x : Rat) ↦
                      @Exists.{1} (Finset.{0} Nat) fun (A' : Finset.{0} Nat) ↦
                        @Exists.{0}
                          (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
                            (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) A')
                            (@Set.range.{0, 1} Nat Nat A))
                          fun
                            (x_1 :
                              @LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
                                (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)
                                  A')
                                (@Set.range.{0, 1} Nat Nat A)) ↦
                          @Eq.{1} Rat
                            (@Finset.sum.{0, 0} Nat Rat Rat.addCommMonoid A' fun (a : Nat) ↦
                              @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                (@Nat.cast.{0} Rat Rat.instNatCast a))
                            x)
                    q))
  := by
  sorry
