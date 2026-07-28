import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Group.AddTorsor

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos898.dist_to_line :
    {V : Type u_1} →
      [inst : NormedAddCommGroup.{u_1} V] →
        [@InnerProductSpace.{0, u_1} Real V Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)] →
          V → V → V → Real
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos898.erdos_mordell :
    ∀ {V : Type u_1} [inst : NormedAddCommGroup.{u_1} V]
      [inst_1 :
        @InnerProductSpace.{0, u_1} Real V Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)]
      [@FiniteDimensional.{0, u_1} Real V Real.instDivisionRing
          (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)
          (@NormedSpace.toModule.{0, u_1} Real V Real.normedField
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
            (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))]
      [hV :
        Fact
          (@Eq.{1} Nat
            (@Module.finrank.{0, u_1} Real V Real.semiring
              (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
              (@NormedSpace.toModule.{0, u_1} Real V Real.normedField
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))]
      {A B C P : V},
      Not
          (@Collinear.{0, u_1, u_1} Real V V Real.instDivisionRing
            (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)
            (@NormedSpace.toModule.{0, u_1} Real V Real.normedField
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
            (@NormedAddTorsor.toAddTorsor.{u_1, u_1} V V
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))
              (@SeminormedAddCommGroup.toNormedAddTorsor.{u_1} V
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)))
            (@Insert.insert.{u_1, u_1} V (Set.{u_1} V) (@Set.instInsert.{u_1} V) A
              (@Insert.insert.{u_1, u_1} V (Set.{u_1} V) (@Set.instInsert.{u_1} V) B
                (@Singleton.singleton.{u_1, u_1} V (Set.{u_1} V) (@Set.instSingletonSet.{u_1} V) C)))) →
        @Membership.mem.{u_1, u_1} V (Set.{u_1} V) (@Set.instMembership.{u_1} V)
            (@interior.{u_1} V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (@ClosureOperator.{u_1} (Set.{u_1} V)
                  (@PartialOrder.toPreorder.{u_1} (Set.{u_1} V)
                    (@ChainCompletePartialOrder.toPartialOrder.{u_1} (Set.{u_1} V)
                      (@ChainCompletePartialOrder.instOfCompleteLattice.{u_1} (Set.{u_1} V)
                        (@CompleteBooleanAlgebra.toCompleteLattice.{u_1} (Set.{u_1} V)
                          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{u_1} (Set.{u_1} V)
                            (@Set.instCompleteAtomicBooleanAlgebra.{u_1} V)))))))
                (Set.{u_1} V) (fun (x : Set.{u_1} V) ↦ Set.{u_1} V)
                (@ClosureOperator.instFunLike.{u_1} (Set.{u_1} V)
                  (@PartialOrder.toPreorder.{u_1} (Set.{u_1} V)
                    (@ChainCompletePartialOrder.toPartialOrder.{u_1} (Set.{u_1} V)
                      (@ChainCompletePartialOrder.instOfCompleteLattice.{u_1} (Set.{u_1} V)
                        (@CompleteBooleanAlgebra.toCompleteLattice.{u_1} (Set.{u_1} V)
                          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{u_1} (Set.{u_1} V)
                            (@Set.instCompleteAtomicBooleanAlgebra.{u_1} V)))))))
                (@convexHull.{0, u_1} Real V Real.semiring Real.partialOrder
                  (@AddCommGroup.toAddCommMonoid.{u_1} V
                    (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                  (@NormedSpace.toModule.{0, u_1} Real V Real.normedField
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                    (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))
                (@Insert.insert.{u_1, u_1} V (Set.{u_1} V) (@Set.instInsert.{u_1} V) A
                  (@Insert.insert.{u_1, u_1} V (Set.{u_1} V) (@Set.instInsert.{u_1} V) B
                    (@Singleton.singleton.{u_1, u_1} V (Set.{u_1} V) (@Set.instSingletonSet.{u_1} V)
                      C)))))
            P →
          @GE.ge.{0} Real Real.instLE
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@Dist.dist.{u_1} V
                  (@PseudoMetricSpace.toDist.{u_1} V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)))
                  P A)
                (@Dist.dist.{u_1} V
                  (@PseudoMetricSpace.toDist.{u_1} V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)))
                  P B))
              (@Dist.dist.{u_1} V
                (@PseudoMetricSpace.toDist.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)))
                P C))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Erdos898.dist_to_line.{u_1} V inst inst_1 P B C)
                  (@Erdos898.dist_to_line.{u_1} V inst inst_1 P A C))
                (@Erdos898.dist_to_line.{u_1} V inst inst_1 P A B)))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
