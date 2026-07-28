import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1043.levelSet :
    @Polynomial.{0} Complex Complex.instSemiring → Set.{0} Complex
  := by
  sorry

noncomputable def Erdos1043.instMeasureSpaceRealSpan :
    (u : Complex) →
      MeasureTheory.MeasureSpace.{0}
        (@Subtype.{1} Complex fun (x : Complex) ↦
          @Membership.mem.{0, 0} Complex
            (@Submodule.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
              (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                            instCommCStarAlgebraComplex)))))
                  instInnerProductSpaceRealComplex)))
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                            instCommCStarAlgebraComplex)))))
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                              instCommCStarAlgebraComplex)))))
                    instInnerProductSpaceRealComplex)))
              Complex
              (@Submodule.setLike.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                            instCommCStarAlgebraComplex)))))
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                              instCommCStarAlgebraComplex)))))
                    instInnerProductSpaceRealComplex))))
            (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
              (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                            instCommCStarAlgebraComplex)))))
                  instInnerProductSpaceRealComplex))
              (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex) (@Set.instSingletonSet.{0} Complex)
                u))
            x)
  := by
  sorry

theorem Erdos1043.erdos_1043 :
    Not
      (∀ (f : @Polynomial.{0} Complex Complex.instSemiring),
        @Polynomial.Monic.{0} Complex Complex.instSemiring f →
          @GE.ge.{0} (WithBot.{0} Nat)
              (@Preorder.toLE.{0} (WithBot.{0} Nat) (@WithBot.instPreorder.{0} Nat Nat.instPreorder))
              (@Polynomial.degree.{0} Complex Complex.instSemiring f)
              (@OfNat.ofNat.{0} (WithBot.{0} Nat) (nat_lit 1)
                (@One.toOfNat1.{0} (WithBot.{0} Nat) (@WithBot.one.{0} Nat Nat.instOne))) →
            @Exists.{1} Complex fun (u : Complex) ↦
              And
                (@Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm u)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                (@LE.le.{0} ENNReal ENNReal.instLE
                  (@DFunLike.coe.{1, 1, 1}
                    (@MeasureTheory.Measure.{0}
                      (@Subtype.{1} Complex fun (x : Complex) ↦
                        @Membership.mem.{0, 0} Complex
                          (@Submodule.{0, 0} Real Complex
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                            (@AddCommGroup.toAddCommMonoid.{0} Complex
                              (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup))
                            (@NormedSpace.toModule.{0, 0} Real Complex
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                instInnerProductSpaceRealComplex)))
                          (@SetLike.instMembership.{0, 0}
                            (@Submodule.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)))
                            Complex
                            (@Submodule.setLike.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex))))
                          (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                            (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex)))))
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                instInnerProductSpaceRealComplex))
                            (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                              (@Set.instSingletonSet.{0} Complex) u))
                          x)
                      (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0}
                        (@Subtype.{1} Complex fun (x : Complex) ↦
                          @Membership.mem.{0, 0} Complex
                            (@Submodule.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)))
                            (@SetLike.instMembership.{0, 0}
                              (@Submodule.{0, 0} Real Complex
                                (@DivisionSemiring.toSemiring.{0} Real
                                  (@Semifield.toDivisionSemiring.{0} Real
                                    (@Field.toSemifield.{0} Real
                                      (@NormedField.toField.{0} Real
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                (@AddCommGroup.toAddCommMonoid.{0} Complex
                                  (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup))
                                (@NormedSpace.toModule.{0, 0} Real Complex
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)))
                              Complex
                              (@Submodule.setLike.{0, 0} Real Complex
                                (@DivisionSemiring.toSemiring.{0} Real
                                  (@Semifield.toDivisionSemiring.{0} Real
                                    (@Field.toSemifield.{0} Real
                                      (@NormedField.toField.{0} Real
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                (@AddCommGroup.toAddCommMonoid.{0} Complex
                                  (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup))
                                (@NormedSpace.toModule.{0, 0} Real Complex
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex))))
                            (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                              (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))
                              (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                (@Set.instSingletonSet.{0} Complex) u))
                            x)
                        (Erdos1043.instMeasureSpaceRealSpan u)))
                    (Set.{0}
                      (@Subtype.{1} Complex fun (x : Complex) ↦
                        @Membership.mem.{0, 0} Complex
                          (@Submodule.{0, 0} Real Complex
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                            (@AddCommGroup.toAddCommMonoid.{0} Complex
                              (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup))
                            (@NormedSpace.toModule.{0, 0} Real Complex
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                instInnerProductSpaceRealComplex)))
                          (@SetLike.instMembership.{0, 0}
                            (@Submodule.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)))
                            Complex
                            (@Submodule.setLike.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex))))
                          (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                            (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex)))))
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                instInnerProductSpaceRealComplex))
                            (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                              (@Set.instSingletonSet.{0} Complex) u))
                          x))
                    (fun
                        (x :
                          Set.{0}
                            (@Subtype.{1} Complex fun (x : Complex) ↦
                              @Membership.mem.{0, 0} Complex
                                (@Submodule.{0, 0} Real Complex
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@DenselyNormedField.toNormedField.{0} Real
                                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                  (@AddCommGroup.toAddCommMonoid.{0} Complex
                                    (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup))
                                  (@NormedSpace.toModule.{0, 0} Real Complex
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex)))
                                (@SetLike.instMembership.{0, 0}
                                  (@Submodule.{0, 0} Real Complex
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@DenselyNormedField.toNormedField.{0} Real
                                              (@RCLike.toDenselyNormedField.{0} Real
                                                Real.instRCLike))))))
                                    (@AddCommGroup.toAddCommMonoid.{0} Complex
                                      (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup))
                                    (@NormedSpace.toModule.{0, 0} Real Complex
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        instInnerProductSpaceRealComplex)))
                                  Complex
                                  (@Submodule.setLike.{0, 0} Real Complex
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@DenselyNormedField.toNormedField.{0} Real
                                              (@RCLike.toDenselyNormedField.{0} Real
                                                Real.instRCLike))))))
                                    (@AddCommGroup.toAddCommMonoid.{0} Complex
                                      (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup))
                                    (@NormedSpace.toModule.{0, 0} Real Complex
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        instInnerProductSpaceRealComplex))))
                                (@Submodule.span.{0, 0} Real Complex Real.semiring
                                  Complex.instAddCommMonoid
                                  (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                        Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                          Complex
                                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                instCommCStarAlgebraComplex)))))
                                      instInnerProductSpaceRealComplex))
                                  (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                    (@Set.instSingletonSet.{0} Complex) u))
                                x)) ↦
                      ENNReal)
                    (@MeasureTheory.Measure.instFunLike.{0}
                      (@Subtype.{1} Complex fun (x : Complex) ↦
                        @Membership.mem.{0, 0} Complex
                          (@Submodule.{0, 0} Real Complex
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                            (@AddCommGroup.toAddCommMonoid.{0} Complex
                              (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup))
                            (@NormedSpace.toModule.{0, 0} Real Complex
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                instInnerProductSpaceRealComplex)))
                          (@SetLike.instMembership.{0, 0}
                            (@Submodule.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)))
                            Complex
                            (@Submodule.setLike.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex))))
                          (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                            (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex)))))
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                instInnerProductSpaceRealComplex))
                            (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                              (@Set.instSingletonSet.{0} Complex) u))
                          x)
                      (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0}
                        (@Subtype.{1} Complex fun (x : Complex) ↦
                          @Membership.mem.{0, 0} Complex
                            (@Submodule.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)))
                            (@SetLike.instMembership.{0, 0}
                              (@Submodule.{0, 0} Real Complex
                                (@DivisionSemiring.toSemiring.{0} Real
                                  (@Semifield.toDivisionSemiring.{0} Real
                                    (@Field.toSemifield.{0} Real
                                      (@NormedField.toField.{0} Real
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                (@AddCommGroup.toAddCommMonoid.{0} Complex
                                  (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup))
                                (@NormedSpace.toModule.{0, 0} Real Complex
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)))
                              Complex
                              (@Submodule.setLike.{0, 0} Real Complex
                                (@DivisionSemiring.toSemiring.{0} Real
                                  (@Semifield.toDivisionSemiring.{0} Real
                                    (@Field.toSemifield.{0} Real
                                      (@NormedField.toField.{0} Real
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                (@AddCommGroup.toAddCommMonoid.{0} Complex
                                  (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup))
                                (@NormedSpace.toModule.{0, 0} Real Complex
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex))))
                            (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                              (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))
                              (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                (@Set.instSingletonSet.{0} Complex) u))
                            x)
                        (Erdos1043.instMeasureSpaceRealSpan u)))
                    (@MeasureTheory.MeasureSpace.volume.{0}
                      (@Subtype.{1} Complex fun (x : Complex) ↦
                        @Membership.mem.{0, 0} Complex
                          (@Submodule.{0, 0} Real Complex
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                            (@AddCommGroup.toAddCommMonoid.{0} Complex
                              (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup))
                            (@NormedSpace.toModule.{0, 0} Real Complex
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                instInnerProductSpaceRealComplex)))
                          (@SetLike.instMembership.{0, 0}
                            (@Submodule.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)))
                            Complex
                            (@Submodule.setLike.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex))))
                          (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                            (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex)))))
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                instInnerProductSpaceRealComplex))
                            (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                              (@Set.instSingletonSet.{0} Complex) u))
                          x)
                      (Erdos1043.instMeasureSpaceRealSpan u))
                    (@Set.image.{0, 0} Complex
                      (@Subtype.{1} Complex fun (x : Complex) ↦
                        @Membership.mem.{0, 0} Complex
                          (@Submodule.{0, 0} Real Complex
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                            (@AddCommGroup.toAddCommMonoid.{0} Complex
                              (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup))
                            (@NormedSpace.toModule.{0, 0} Real Complex
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                instInnerProductSpaceRealComplex)))
                          (@SetLike.instMembership.{0, 0}
                            (@Submodule.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)))
                            Complex
                            (@Submodule.setLike.{0, 0} Real Complex
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid.{0} Complex
                                (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))
                              (@NormedSpace.toModule.{0, 0} Real Complex
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex))))
                          (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                            (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex)))))
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                instInnerProductSpaceRealComplex))
                            (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                              (@Set.instSingletonSet.{0} Complex) u))
                          x)
                      (@DFunLike.coe.{1, 1, 1}
                        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                          (@RingHom.id.{0} Real
                            (@Semiring.toNonAssocSemiring.{0} Real
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
                          Complex
                          (@UniformSpace.toTopologicalSpace.{0} Complex
                            (@PseudoMetricSpace.toUniformSpace.{0} Complex
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Complex
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))))
                          (@AddCommGroup.toAddCommMonoid.{0} Complex
                            (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                              Complex.instNormedAddCommGroup))
                          (@Subtype.{1} Complex fun (x : Complex) ↦
                            @Membership.mem.{0, 0} Complex
                              (@Submodule.{0, 0} Real Complex
                                (@DivisionSemiring.toSemiring.{0} Real
                                  (@Semifield.toDivisionSemiring.{0} Real
                                    (@Field.toSemifield.{0} Real
                                      (@NormedField.toField.{0} Real
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                (@AddCommGroup.toAddCommMonoid.{0} Complex
                                  (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup))
                                (@NormedSpace.toModule.{0, 0} Real Complex
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)))
                              (@SetLike.instMembership.{0, 0}
                                (@Submodule.{0, 0} Real Complex
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@DenselyNormedField.toNormedField.{0} Real
                                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                  (@AddCommGroup.toAddCommMonoid.{0} Complex
                                    (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup))
                                  (@NormedSpace.toModule.{0, 0} Real Complex
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex)))
                                Complex
                                (@Submodule.setLike.{0, 0} Real Complex
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@DenselyNormedField.toNormedField.{0} Real
                                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                  (@AddCommGroup.toAddCommMonoid.{0} Complex
                                    (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup))
                                  (@NormedSpace.toModule.{0, 0} Real Complex
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex))))
                              (@Submodule.span.{0, 0} Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                        Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex))
                                (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                  (@Set.instSingletonSet.{0} Complex) u))
                              x)
                          (@instTopologicalSpaceSubtype.{0} Complex
                            (fun (x : Complex) ↦
                              @Membership.mem.{0, 0} Complex
                                (@Submodule.{0, 0} Real Complex
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@DenselyNormedField.toNormedField.{0} Real
                                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                  (@AddCommGroup.toAddCommMonoid.{0} Complex
                                    (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup))
                                  (@NormedSpace.toModule.{0, 0} Real Complex
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex)))
                                (@SetLike.instMembership.{0, 0}
                                  (@Submodule.{0, 0} Real Complex
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@DenselyNormedField.toNormedField.{0} Real
                                              (@RCLike.toDenselyNormedField.{0} Real
                                                Real.instRCLike))))))
                                    (@AddCommGroup.toAddCommMonoid.{0} Complex
                                      (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup))
                                    (@NormedSpace.toModule.{0, 0} Real Complex
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        instInnerProductSpaceRealComplex)))
                                  Complex
                                  (@Submodule.setLike.{0, 0} Real Complex
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@DenselyNormedField.toNormedField.{0} Real
                                              (@RCLike.toDenselyNormedField.{0} Real
                                                Real.instRCLike))))))
                                    (@AddCommGroup.toAddCommMonoid.{0} Complex
                                      (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup))
                                    (@NormedSpace.toModule.{0, 0} Real Complex
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        instInnerProductSpaceRealComplex))))
                                (@Submodule.span.{0, 0} Real Complex Real.semiring
                                  Complex.instAddCommMonoid
                                  (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                        Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                          Complex
                                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                instCommCStarAlgebraComplex)))))
                                      instInnerProductSpaceRealComplex))
                                  (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                    (@Set.instSingletonSet.{0} Complex) u))
                                x)
                            (@UniformSpace.toTopologicalSpace.{0} Complex
                              (@PseudoMetricSpace.toUniformSpace.{0} Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)))))
                          (@Submodule.addCommMonoid.{0, 0} Real Complex
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                            (@AddCommGroup.toAddCommMonoid.{0} Complex
                              (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup))
                            (@NormedSpace.toModule.{0, 0} Real Complex
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                instInnerProductSpaceRealComplex))
                            (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                              (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))
                              (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                (@Set.instSingletonSet.{0} Complex) u)))
                          (@NormedSpace.toModule.{0, 0} Real Complex
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                              Complex.instNormedAddCommGroup)
                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              instInnerProductSpaceRealComplex))
                          (@Submodule.module.{0, 0} Real Complex
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                            (@AddCommGroup.toAddCommMonoid.{0} Complex
                              (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup))
                            (@NormedSpace.toModule.{0, 0} Real Complex
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                instInnerProductSpaceRealComplex))
                            (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                              (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))
                              (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                (@Set.instSingletonSet.{0} Complex) u))))
                        Complex
                        (fun (x : Complex) ↦
                          @Subtype.{1} Complex fun (x : Complex) ↦
                            @Membership.mem.{0, 0} Complex
                              (@Submodule.{0, 0} Real Complex
                                (@DivisionSemiring.toSemiring.{0} Real
                                  (@Semifield.toDivisionSemiring.{0} Real
                                    (@Field.toSemifield.{0} Real
                                      (@NormedField.toField.{0} Real
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                (@AddCommGroup.toAddCommMonoid.{0} Complex
                                  (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup))
                                (@NormedSpace.toModule.{0, 0} Real Complex
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)))
                              (@SetLike.instMembership.{0, 0}
                                (@Submodule.{0, 0} Real Complex
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@DenselyNormedField.toNormedField.{0} Real
                                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                  (@AddCommGroup.toAddCommMonoid.{0} Complex
                                    (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup))
                                  (@NormedSpace.toModule.{0, 0} Real Complex
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex)))
                                Complex
                                (@Submodule.setLike.{0, 0} Real Complex
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@DenselyNormedField.toNormedField.{0} Real
                                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                  (@AddCommGroup.toAddCommMonoid.{0} Complex
                                    (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup))
                                  (@NormedSpace.toModule.{0, 0} Real Complex
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex))))
                              (@Submodule.span.{0, 0} Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                        Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex))
                                (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                  (@Set.instSingletonSet.{0} Complex) u))
                              x)
                        (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                          (@RingHom.id.{0} Real
                            (@Semiring.toNonAssocSemiring.{0} Real
                              (@DivisionSemiring.toSemiring.{0} Real
                                (@Semifield.toDivisionSemiring.{0} Real
                                  (@Field.toSemifield.{0} Real
                                    (@NormedField.toField.{0} Real
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
                          Complex
                          (@UniformSpace.toTopologicalSpace.{0} Complex
                            (@PseudoMetricSpace.toUniformSpace.{0} Complex
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Complex
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup))))
                          (@AddCommGroup.toAddCommMonoid.{0} Complex
                            (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                              Complex.instNormedAddCommGroup))
                          (@Subtype.{1} Complex fun (x : Complex) ↦
                            @Membership.mem.{0, 0} Complex
                              (@Submodule.{0, 0} Real Complex
                                (@DivisionSemiring.toSemiring.{0} Real
                                  (@Semifield.toDivisionSemiring.{0} Real
                                    (@Field.toSemifield.{0} Real
                                      (@NormedField.toField.{0} Real
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                (@AddCommGroup.toAddCommMonoid.{0} Complex
                                  (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup))
                                (@NormedSpace.toModule.{0, 0} Real Complex
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)))
                              (@SetLike.instMembership.{0, 0}
                                (@Submodule.{0, 0} Real Complex
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@DenselyNormedField.toNormedField.{0} Real
                                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                  (@AddCommGroup.toAddCommMonoid.{0} Complex
                                    (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup))
                                  (@NormedSpace.toModule.{0, 0} Real Complex
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex)))
                                Complex
                                (@Submodule.setLike.{0, 0} Real Complex
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@DenselyNormedField.toNormedField.{0} Real
                                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                  (@AddCommGroup.toAddCommMonoid.{0} Complex
                                    (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup))
                                  (@NormedSpace.toModule.{0, 0} Real Complex
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex))))
                              (@Submodule.span.{0, 0} Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                        Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex))
                                (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                  (@Set.instSingletonSet.{0} Complex) u))
                              x)
                          (@instTopologicalSpaceSubtype.{0} Complex
                            (fun (x : Complex) ↦
                              @Membership.mem.{0, 0} Complex
                                (@Submodule.{0, 0} Real Complex
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@DenselyNormedField.toNormedField.{0} Real
                                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                                  (@AddCommGroup.toAddCommMonoid.{0} Complex
                                    (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup))
                                  (@NormedSpace.toModule.{0, 0} Real Complex
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex)))
                                (@SetLike.instMembership.{0, 0}
                                  (@Submodule.{0, 0} Real Complex
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@DenselyNormedField.toNormedField.{0} Real
                                              (@RCLike.toDenselyNormedField.{0} Real
                                                Real.instRCLike))))))
                                    (@AddCommGroup.toAddCommMonoid.{0} Complex
                                      (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup))
                                    (@NormedSpace.toModule.{0, 0} Real Complex
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        instInnerProductSpaceRealComplex)))
                                  Complex
                                  (@Submodule.setLike.{0, 0} Real Complex
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@DenselyNormedField.toNormedField.{0} Real
                                              (@RCLike.toDenselyNormedField.{0} Real
                                                Real.instRCLike))))))
                                    (@AddCommGroup.toAddCommMonoid.{0} Complex
                                      (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup))
                                    (@NormedSpace.toModule.{0, 0} Real Complex
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        instInnerProductSpaceRealComplex))))
                                (@Submodule.span.{0, 0} Real Complex Real.semiring
                                  Complex.instAddCommMonoid
                                  (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                        Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                          Complex
                                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                instCommCStarAlgebraComplex)))))
                                      instInnerProductSpaceRealComplex))
                                  (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                    (@Set.instSingletonSet.{0} Complex) u))
                                x)
                            (@UniformSpace.toTopologicalSpace.{0} Complex
                              (@PseudoMetricSpace.toUniformSpace.{0} Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)))))
                          (@Submodule.addCommMonoid.{0, 0} Real Complex
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                            (@AddCommGroup.toAddCommMonoid.{0} Complex
                              (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup))
                            (@NormedSpace.toModule.{0, 0} Real Complex
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                instInnerProductSpaceRealComplex))
                            (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                              (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))
                              (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                (@Set.instSingletonSet.{0} Complex) u)))
                          (@NormedSpace.toModule.{0, 0} Real Complex
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                              Complex.instNormedAddCommGroup)
                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              instInnerProductSpaceRealComplex))
                          (@Submodule.module.{0, 0} Real Complex
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                            (@AddCommGroup.toAddCommMonoid.{0} Complex
                              (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup))
                            (@NormedSpace.toModule.{0, 0} Real Complex
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                Complex.instNormedAddCommGroup)
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                  Complex.instNormedAddCommGroup)
                                instInnerProductSpaceRealComplex))
                            (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                              (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))
                              (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                (@Set.instSingletonSet.{0} Complex) u))))
                        (@Submodule.orthogonalProjectionOnto.{0, 0} Real Complex Real.instRCLike
                          Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
                          (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                            (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex)))))
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                instInnerProductSpaceRealComplex))
                            (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                              (@Set.instSingletonSet.{0} Complex) u))
                          (@Submodule.HasOrthogonalProjection.ofCompleteSpace.{0, 0} Real Complex
                            Real.instRCLike Complex.instNormedAddCommGroup
                            instInnerProductSpaceRealComplex
                            (@Submodule.span.{0, 0} Real Complex Real.semiring Complex.instAddCommMonoid
                              (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))
                              (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                (@Set.instSingletonSet.{0} Complex) u))
                            (@complete_of_proper.{0}
                              (@Subtype.{1} Complex fun (x : Complex) ↦
                                @Membership.mem.{0, 0} Complex
                                  (@Submodule.{0, 0} Real Complex
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@DenselyNormedField.toNormedField.{0} Real
                                              (@RCLike.toDenselyNormedField.{0} Real
                                                Real.instRCLike))))))
                                    (@AddCommGroup.toAddCommMonoid.{0} Complex
                                      (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup))
                                    (@NormedSpace.toModule.{0, 0} Real Complex
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        instInnerProductSpaceRealComplex)))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Submodule.{0, 0} Real Complex
                                      (@DivisionSemiring.toSemiring.{0} Real
                                        (@Semifield.toDivisionSemiring.{0} Real
                                          (@Field.toSemifield.{0} Real
                                            (@NormedField.toField.{0} Real
                                              (@DenselyNormedField.toNormedField.{0} Real
                                                (@RCLike.toDenselyNormedField.{0} Real
                                                  Real.instRCLike))))))
                                      (@AddCommGroup.toAddCommMonoid.{0} Complex
                                        (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup))
                                      (@NormedSpace.toModule.{0, 0} Real Complex
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                          Real.instRCLike
                                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                            Complex.instNormedAddCommGroup)
                                          instInnerProductSpaceRealComplex)))
                                    Complex
                                    (@Submodule.setLike.{0, 0} Real Complex
                                      (@DivisionSemiring.toSemiring.{0} Real
                                        (@Semifield.toDivisionSemiring.{0} Real
                                          (@Field.toSemifield.{0} Real
                                            (@NormedField.toField.{0} Real
                                              (@DenselyNormedField.toNormedField.{0} Real
                                                (@RCLike.toDenselyNormedField.{0} Real
                                                  Real.instRCLike))))))
                                      (@AddCommGroup.toAddCommMonoid.{0} Complex
                                        (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup))
                                      (@NormedSpace.toModule.{0, 0} Real Complex
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                          Real.instRCLike
                                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                            Complex.instNormedAddCommGroup)
                                          instInnerProductSpaceRealComplex))))
                                  (@Submodule.span.{0, 0} Real Complex Real.semiring
                                    Complex.instAddCommMonoid
                                    (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                          Complex
                                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                instCommCStarAlgebraComplex)))))
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                            Complex
                                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0}
                                              Complex
                                              (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                                (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                  instCommCStarAlgebraComplex)))))
                                        instInnerProductSpaceRealComplex))
                                    (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                      (@Set.instSingletonSet.{0} Complex) u))
                                  x)
                              (@Subtype.pseudoMetricSpace.{0} Complex
                                (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                                  (@SeminormedCommRing.toSeminormedRing.{0} Complex
                                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex))))
                                fun (x : Complex) ↦
                                @Membership.mem.{0, 0} Complex
                                  (@Submodule.{0, 0} Real Complex
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@DenselyNormedField.toNormedField.{0} Real
                                              (@RCLike.toDenselyNormedField.{0} Real
                                                Real.instRCLike))))))
                                    (@AddCommGroup.toAddCommMonoid.{0} Complex
                                      (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup))
                                    (@NormedSpace.toModule.{0, 0} Real Complex
                                      (@DenselyNormedField.toNormedField.{0} Real
                                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        instInnerProductSpaceRealComplex)))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Submodule.{0, 0} Real Complex
                                      (@DivisionSemiring.toSemiring.{0} Real
                                        (@Semifield.toDivisionSemiring.{0} Real
                                          (@Field.toSemifield.{0} Real
                                            (@NormedField.toField.{0} Real
                                              (@DenselyNormedField.toNormedField.{0} Real
                                                (@RCLike.toDenselyNormedField.{0} Real
                                                  Real.instRCLike))))))
                                      (@AddCommGroup.toAddCommMonoid.{0} Complex
                                        (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup))
                                      (@NormedSpace.toModule.{0, 0} Real Complex
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                          Real.instRCLike
                                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                            Complex.instNormedAddCommGroup)
                                          instInnerProductSpaceRealComplex)))
                                    Complex
                                    (@Submodule.setLike.{0, 0} Real Complex
                                      (@DivisionSemiring.toSemiring.{0} Real
                                        (@Semifield.toDivisionSemiring.{0} Real
                                          (@Field.toSemifield.{0} Real
                                            (@NormedField.toField.{0} Real
                                              (@DenselyNormedField.toNormedField.{0} Real
                                                (@RCLike.toDenselyNormedField.{0} Real
                                                  Real.instRCLike))))))
                                      (@AddCommGroup.toAddCommMonoid.{0} Complex
                                        (@NormedAddCommGroup.toAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup))
                                      (@NormedSpace.toModule.{0, 0} Real Complex
                                        (@DenselyNormedField.toNormedField.{0} Real
                                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                          Complex.instNormedAddCommGroup)
                                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                          Real.instRCLike
                                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                            Complex.instNormedAddCommGroup)
                                          instInnerProductSpaceRealComplex))))
                                  (@Submodule.span.{0, 0} Real Complex Real.semiring
                                    Complex.instAddCommMonoid
                                    (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                          Complex
                                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                instCommCStarAlgebraComplex)))))
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                        Real.instRCLike
                                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                            Complex
                                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0}
                                              Complex
                                              (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                                (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                  instCommCStarAlgebraComplex)))))
                                        instInnerProductSpaceRealComplex))
                                    (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                      (@Set.instSingletonSet.{0} Complex) u))
                                  x)
                              (@FiniteDimensional.RCLike.properSpace_submodule.{0, 0} Real Complex
                                Real.instRCLike Complex.instNormedAddCommGroup
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)
                                (@Submodule.span.{0, 0} Real Complex Real.semiring
                                  Complex.instAddCommMonoid
                                  (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                        Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                          Complex
                                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                instCommCStarAlgebraComplex)))))
                                      instInnerProductSpaceRealComplex))
                                  (@Singleton.singleton.{0, 0} Complex (Set.{0} Complex)
                                    (@Set.instSingletonSet.{0} Complex) u))
                                (@FiniteDimensional.span_singleton.{0, 0} Real Complex
                                  Real.instDivisionRing Complex.addCommGroup
                                  (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                        Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                      Real.instRCLike
                                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0}
                                          Complex
                                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                instCommCStarAlgebraComplex)))))
                                      instInnerProductSpaceRealComplex))
                                  u))))))
                      (Erdos1043.levelSet f)))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                          ENNReal.instAddCommMonoidWithOne))
                      (@Nat.instAtLeastTwoHAddOfNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
  := by
  sorry
