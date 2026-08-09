import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

attribute [local instance] Classical.propDecidable

theorem Erdos1090.exists_set_with_strict_monochromatic_line_property :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k →
        @Exists.{1}
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
          fun
            (A :
              Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)) ↦
          ∀
            (C :
              (@Subtype.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                  fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real) ↦
                  @Membership.mem.{0, 0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                    (@SetLike.instMembership.{0, 0}
                      (Finset.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                      (@Finset.instSetLike.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)))
                    A x) →
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
            @Exists.{1}
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
              fun
                (S :
                  Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)) ↦
              @Exists.{0}
                (@LE.le.{0}
                  (Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                  (@Preorder.toLE.{0}
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                    (@PartialOrder.toPreorder.{0}
                      (Finset.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                      (@Finset.instPartialOrder.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))))
                  S A)
                fun
                  (hSA :
                    @LE.le.{0}
                      (Finset.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                      (@Preorder.toLE.{0}
                        (Finset.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                        (@PartialOrder.toPreorder.{0}
                          (Finset.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                          (@Finset.instPartialOrder.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                              Real))))
                      S A) ↦
                And
                  (@Collinear.{0, 0, 0} Real
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                    Real.instDivisionRing
                    (@Pi.addCommGroup.{0, 0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                        Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                      Real.instAddCommGroup)
                    (@Pi.Function.module.{0, 0, 0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@DivisionRing.toDivisionSemiring.{0} Real Real.instDivisionRing))
                      (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                      (@Semiring.toModule.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@DivisionRing.toDivisionSemiring.{0} Real Real.instDivisionRing))))
                    (@Finset.instAddTorsorForall.{0, 0} Real Real.instRing
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@SetLike.coe.{0, 0}
                      (Finset.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                      (@Finset.instSetLike.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real))
                      S))
                  (And
                    (@GE.ge.{0} Nat instLENat
                      (@Finset.card.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real) S)
                      k)
                    (And
                      (∀ (y : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real),
                        @Membership.mem.{0, 0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                            (Finset.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                Real))
                            (@SetLike.instMembership.{0, 0}
                              (Finset.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                              (@Finset.instSetLike.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real)))
                            A y →
                          @Membership.mem.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                              (@AffineSubspace.{0, 0, 0} Real
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real)
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real)
                                Real.instRing
                                (@Pi.addCommGroup.{0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (fun
                                      (a :
                                        Fin
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                            (instOfNatNat (nat_lit 2)))) ↦
                                    Real)
                                  fun
                                    (i :
                                      Fin
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                                  Real.instAddCommGroup)
                                (@Pi.Function.module.{0, 0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  Real Real (@Ring.toSemiring.{0} Real Real.instRing)
                                  (@Semiring.toAddCommMonoid.{0} Real
                                    (@Ring.toSemiring.{0} Real Real.instRing))
                                  (@Semiring.toModule.{0} Real
                                    (@Ring.toSemiring.{0} Real Real.instRing)))
                                (@Finset.instAddTorsorForall.{0, 0} Real Real.instRing
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                              (@SetLike.instMembership.{0, 0}
                                (@AffineSubspace.{0, 0, 0} Real
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Real)
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Real)
                                  Real.instRing
                                  (@Pi.addCommGroup.{0, 0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (fun
                                        (a :
                                          Fin
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                              (instOfNatNat (nat_lit 2)))) ↦
                                      Real)
                                    fun
                                      (i :
                                        Fin
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                            (instOfNatNat (nat_lit 2)))) ↦
                                    Real.instAddCommGroup)
                                  (@Pi.Function.module.{0, 0, 0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    Real Real (@Ring.toSemiring.{0} Real Real.instRing)
                                    (@Semiring.toAddCommMonoid.{0} Real
                                      (@Ring.toSemiring.{0} Real Real.instRing))
                                    (@Semiring.toModule.{0} Real
                                      (@Ring.toSemiring.{0} Real Real.instRing)))
                                  (@Finset.instAddTorsorForall.{0, 0} Real Real.instRing
                                    (Fin
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real)
                                (@AffineSubspace.instSetLike.{0, 0, 0} Real
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Real)
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Real)
                                  Real.instRing
                                  (@Pi.addCommGroup.{0, 0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (fun
                                        (a :
                                          Fin
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                              (instOfNatNat (nat_lit 2)))) ↦
                                      Real)
                                    fun
                                      (i :
                                        Fin
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                            (instOfNatNat (nat_lit 2)))) ↦
                                    Real.instAddCommGroup)
                                  (@Pi.Function.module.{0, 0, 0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    Real Real (@Ring.toSemiring.{0} Real Real.instRing)
                                    (@Semiring.toAddCommMonoid.{0} Real
                                      (@Ring.toSemiring.{0} Real Real.instRing))
                                    (@Semiring.toModule.{0} Real
                                      (@Ring.toSemiring.{0} Real Real.instRing)))
                                  (@Finset.instAddTorsorForall.{0, 0} Real Real.instRing
                                    (Fin
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                              (@affineSpan.{0, 0, 0} Real
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real)
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real)
                                Real.instRing
                                (@Pi.addCommGroup.{0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (fun
                                      (a :
                                        Fin
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                            (instOfNatNat (nat_lit 2)))) ↦
                                    Real)
                                  fun
                                    (i :
                                      Fin
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                                  Real.instAddCommGroup)
                                (@Pi.Function.module.{0, 0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  Real Real (@Ring.toSemiring.{0} Real Real.instRing)
                                  (@Semiring.toAddCommMonoid.{0} Real
                                    (@Ring.toSemiring.{0} Real Real.instRing))
                                  (@Semiring.toModule.{0} Real
                                    (@Ring.toSemiring.{0} Real Real.instRing)))
                                (@Finset.instAddTorsorForall.{0, 0} Real Real.instRing
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@SetLike.coe.{0, 0}
                                  (Finset.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Real))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Real)
                                  (@Finset.instSetLike.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Real))
                                  S))
                              y →
                            @Membership.mem.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                              (Finset.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real))
                              (@SetLike.instMembership.{0, 0}
                                (Finset.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Real))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real)
                                (@Finset.instSetLike.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Real)))
                              S y)
                      (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        fun (c : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                        ∀ (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                          (hx :
                            @Membership.mem.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
                              (Finset.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real))
                              (@SetLike.instMembership.{0, 0}
                                (Finset.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Real))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real)
                                (@Finset.instSetLike.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Real)))
                              S x),
                          @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (C
                              (@Subtype.mk.{1}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Real)
                                (fun
                                    (x :
                                      Fin
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                            (instOfNatNat (nat_lit 2))) →
                                        Real) ↦
                                  @Membership.mem.{0, 0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Real)
                                    (Finset.{0}
                                      (Fin
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                            (instOfNatNat (nat_lit 2))) →
                                        Real))
                                    (@SetLike.instMembership.{0, 0}
                                      (Finset.{0}
                                        (Fin
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                              (instOfNatNat (nat_lit 2))) →
                                          Real))
                                      (Fin
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                            (instOfNatNat (nat_lit 2))) →
                                        Real)
                                      (@Finset.instSetLike.{0}
                                        (Fin
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                              (instOfNatNat (nat_lit 2))) →
                                          Real)))
                                    A x)
                                x (@hSA x hx)))
                            c)))
  := by
  sorry
