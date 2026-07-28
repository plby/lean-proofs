import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

attribute [local instance] Classical.propDecidable

theorem Erdos967.main_theorem :
    ∀ (t : Real),
      @Ne.{1} Real t (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        ∀ (lambda_val : Complex),
          @Exists.{1} (Set.{0} Nat) fun (S : Set.{0} Nat) ↦
            And
              (∀ (n : Nat),
                @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S n →
                  @GE.ge.{0} Nat instLENat n
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (And
                (@Summable.{0, 0} Real Nat Real.instAddCommMonoid
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (fun (n : Nat) ↦
                    @ite.{1} Real
                      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S n)
                      (Classical.propDecidable
                        (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S n))
                      (@Inv.inv.{0} Real Real.instInv (@Nat.cast.{0} Real Real.instNatCast n))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                  (SummationFilter.unconditional.{0} Nat))
                (@Eq.{1} Complex
                  (@tsum.{0, 0} Complex Nat Complex.instAddCommMonoid
                    (@UniformSpace.toTopologicalSpace.{0} Complex
                      (@PseudoMetricSpace.toUniformSpace.{0} Complex
                        (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                          (@SeminormedCommRing.toSeminormedRing.{0} Complex
                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                instCommCStarAlgebraComplex))))))
                    (fun (n : Nat) ↦
                      @ite.{1} Complex
                        (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S n)
                        (Classical.propDecidable
                          (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S n))
                        (@HPow.hPow.{0, 0, 0} Complex Complex Complex
                          (@instHPow.{0, 0} Complex Complex Complex.instPow)
                          (@Nat.cast.{0} Complex Complex.instNatCast n)
                          (@Neg.neg.{0} Complex Complex.instNeg
                            (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex
                              (@instHAdd.{0} Complex Complex.instAdd)
                              (@OfNat.ofNat.{0} Complex (nat_lit 1)
                                (@One.toOfNat1.{0} Complex Complex.instOne))
                              (@HMul.hMul.{0, 0, 0} Complex Complex Complex
                                (@instHMul.{0} Complex Complex.instMul) Complex.I ↑t))))
                        (@OfNat.ofNat.{0} Complex (nat_lit 0)
                          (@Zero.toOfNat0.{0} Complex Complex.instZero)))
                    (SummationFilter.unconditional.{0} Nat))
                  lambda_val))
  := by
  sorry

noncomputable def Erdos967.question_1_1_statement :
    Prop
  := by
  sorry

theorem Erdos967.disproof_of_question_1_1 :
    Not Erdos967.question_1_1_statement
  := by
  sorry
