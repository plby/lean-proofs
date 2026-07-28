import Mathlib.Analysis.CStarAlgebra.Classes

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1048b.my_r :
    Real
  := by
  sorry

noncomputable def Erdos1048b.my_S :
    Set.{0} Complex
  := by
  sorry

theorem Erdos1048b.components_small_final :
    ∀ (z : Complex),
      @Membership.mem.{0, 0} Complex (Set.{0} Complex) (@Set.instMembership.{0} Complex) Erdos1048b.my_S
          z →
        @LT.lt.{0} ENNReal
          (@Preorder.toLT.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
          (@Metric.ediam.{0} Complex
            (@EMetricSpace.toPseudoEMetricSpace.{0} Complex
              (@MetricSpace.toEMetricSpace.{0} Complex
                (@NormedField.toMetricSpace.{0} Complex Complex.instNormedField)))
            (@connectedComponentIn.{0} Complex
              (@UniformSpace.toTopologicalSpace.{0} Complex
                (@PseudoMetricSpace.toUniformSpace.{0} Complex
                  (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                    (@SeminormedCommRing.toSeminormedRing.{0} Complex
                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                          instCommCStarAlgebraComplex))))))
              Erdos1048b.my_S z))
          (ENNReal.ofReal
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              Erdos1048b.my_r))
  := by
  sorry
