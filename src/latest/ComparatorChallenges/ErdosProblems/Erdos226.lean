import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.FDeriv.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos226.IsAffine :
    (Real → Real) → Prop
  := by
  sorry

noncomputable def Erdos226.PreservesRationality :
    (Real → Real) → Prop
  := by
  sorry

theorem Erdos226.erdos_226 :
    @Exists.{1} (Complex → Complex) fun (F : Complex → Complex) ↦
      And
        (@Differentiable.{0, 0, 0} Complex
          (@DenselyNormedField.toNontriviallyNormedField.{0} Complex Complex.instDenselyNormedField)
          Complex Complex.addCommGroup
          (@Semiring.toModule.{0} Complex
            (@DivisionSemiring.toSemiring.{0} Complex
              (@Semifield.toDivisionSemiring.{0} Complex
                (@Field.toSemifield.{0} Complex
                  (@NormedField.toField.{0} Complex
                    (@NontriviallyNormedField.toNormedField.{0} Complex
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Complex
                        Complex.instDenselyNormedField)))))))
          (@UniformSpace.toTopologicalSpace.{0} Complex
            (@PseudoMetricSpace.toUniformSpace.{0} Complex
              (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                (@SeminormedCommRing.toSeminormedRing.{0} Complex
                  (@NormedCommRing.toSeminormedCommRing.{0} Complex
                    (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
          Complex Complex.addCommGroup
          (@Semiring.toModule.{0} Complex
            (@DivisionSemiring.toSemiring.{0} Complex
              (@Semifield.toDivisionSemiring.{0} Complex
                (@Field.toSemifield.{0} Complex
                  (@NormedField.toField.{0} Complex
                    (@NontriviallyNormedField.toNormedField.{0} Complex
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Complex
                        Complex.instDenselyNormedField)))))))
          (@UniformSpace.toTopologicalSpace.{0} Complex
            (@PseudoMetricSpace.toUniformSpace.{0} Complex
              (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                (@SeminormedCommRing.toSeminormedRing.{0} Complex
                  (@NormedCommRing.toSeminormedCommRing.{0} Complex
                    (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
          F)
        (And
          (∀ (x : Real),
            @Eq.{1} Real (F ↑x).im
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (And (Not (Erdos226.IsAffine fun (x : Real) ↦ (F ↑x).re))
            (Erdos226.PreservesRationality fun (x : Real) ↦ (F ↑x).re)))
  := by
  sorry
