import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Erdos115

noncomputable def eremenko_bound (n : ℕ) : ℝ := (2 : ℝ) ^ ((1 : ℝ) / n - 1) * (n : ℝ) ^ 2
noncomputable def extremal_polynomial (n : ℕ) : Polynomial ℂ :=
  (Polynomial.Chebyshev.T ℂ n).comp (Polynomial.C ((2 : ℂ) ^ ((1 : ℂ) / n - 1)) * Polynomial.X + 1)
end Erdos115

attribute [local instance] Classical.propDecidable

theorem Erdos115.eremenko_lempert_1999 :
    ∀ (n : Nat),
      And
        (@Ne.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          ∀ (p : @Polynomial.{0} Complex Complex.instSemiring),
            @Polynomial.Monic.{0} Complex Complex.instSemiring p →
              @Eq.{1} (WithBot.{0} Nat) (@Polynomial.degree.{0} Complex Complex.instSemiring p)
                  (@Nat.cast.{0} (WithBot.{0} Nat) (@WithBot.instNatCast.{0} Nat instNatCastNat) n) →
                @IsConnected.{0} Complex
                    (@UniformSpace.toTopologicalSpace.{0} Complex
                      (@PseudoMetricSpace.toUniformSpace.{0} Complex
                        (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                          (@SeminormedCommRing.toSeminormedRing.{0} Complex
                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                instCommCStarAlgebraComplex))))))
                    (@Set.ofPred.{0} Complex fun (z : Complex) ↦
                      @LE.le.{0} Real Real.instLE
                        (@Norm.norm.{0} Complex Complex.instNorm
                          (@Polynomial.eval.{0} Complex Complex.instSemiring z p))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                  ∀ (z : Complex),
                    @LE.le.{0} Real Real.instLE
                        (@Norm.norm.{0} Complex Complex.instNorm
                          (@Polynomial.eval.{0} Complex Complex.instSemiring z p))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                      @LE.le.{0} Real Real.instLE
                        (@Norm.norm.{0} Complex Complex.instNorm
                          (@Polynomial.eval.{0} Complex Complex.instSemiring z
                            (@DFunLike.coe.{1, 1, 1}
                              (@LinearMap.{0, 0, 0, 0} Complex Complex Complex.instSemiring
                                Complex.instSemiring
                                (@RingHom.id.{0} Complex
                                  (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring))
                                (@Polynomial.{0} Complex Complex.instSemiring)
                                (@Polynomial.{0} Complex Complex.instSemiring)
                                (@Semiring.toAddCommMonoid.{0}
                                  (@Polynomial.{0} Complex Complex.instSemiring)
                                  (@Polynomial.semiring.{0} Complex Complex.instSemiring))
                                (@Semiring.toAddCommMonoid.{0}
                                  (@Polynomial.{0} Complex Complex.instSemiring)
                                  (@Polynomial.semiring.{0} Complex Complex.instSemiring))
                                (@Polynomial.module.{0, 0} Complex Complex.instSemiring Complex
                                  Complex.instSemiring
                                  (@Semiring.toModule.{0} Complex Complex.instSemiring))
                                (@Polynomial.module.{0, 0} Complex Complex.instSemiring Complex
                                  Complex.instSemiring
                                  (@Semiring.toModule.{0} Complex Complex.instSemiring)))
                              (@Polynomial.{0} Complex Complex.instSemiring)
                              (fun (x : @Polynomial.{0} Complex Complex.instSemiring) ↦
                                @Polynomial.{0} Complex Complex.instSemiring)
                              (@LinearMap.instFunLike.{0, 0, 0, 0} Complex Complex
                                (@Polynomial.{0} Complex Complex.instSemiring)
                                (@Polynomial.{0} Complex Complex.instSemiring) Complex.instSemiring
                                Complex.instSemiring
                                (@Semiring.toAddCommMonoid.{0}
                                  (@Polynomial.{0} Complex Complex.instSemiring)
                                  (@Polynomial.semiring.{0} Complex Complex.instSemiring))
                                (@Semiring.toAddCommMonoid.{0}
                                  (@Polynomial.{0} Complex Complex.instSemiring)
                                  (@Polynomial.semiring.{0} Complex Complex.instSemiring))
                                (@Polynomial.module.{0, 0} Complex Complex.instSemiring Complex
                                  Complex.instSemiring
                                  (@Semiring.toModule.{0} Complex Complex.instSemiring))
                                (@Polynomial.module.{0, 0} Complex Complex.instSemiring Complex
                                  Complex.instSemiring
                                  (@Semiring.toModule.{0} Complex Complex.instSemiring))
                                (@RingHom.id.{0} Complex
                                  (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring)))
                              (@Polynomial.derivative.{0} Complex Complex.instSemiring) p)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real
                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                  (@One.toOfNat1.{0} Real Real.instOne))
                                (@Nat.cast.{0} Real Real.instNatCast n))
                              (@OfNat.ofNat.{0} Real (nat_lit 1)
                                (@One.toOfNat1.{0} Real Real.instOne))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat
                              (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@Nat.cast.{0} Real Real.instNatCast n)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@Ne.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Eq.{1} Real
            (@Norm.norm.{0} Complex Complex.instNorm
              (@Polynomial.eval.{0} Complex Complex.instSemiring
                (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))
                (@DFunLike.coe.{1, 1, 1}
                  (@LinearMap.{0, 0, 0, 0} Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id.{0} Complex
                      (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring))
                    (@Polynomial.{0} Complex Complex.instSemiring)
                    (@Polynomial.{0} Complex Complex.instSemiring)
                    (@Semiring.toAddCommMonoid.{0} (@Polynomial.{0} Complex Complex.instSemiring)
                      (@Polynomial.semiring.{0} Complex Complex.instSemiring))
                    (@Semiring.toAddCommMonoid.{0} (@Polynomial.{0} Complex Complex.instSemiring)
                      (@Polynomial.semiring.{0} Complex Complex.instSemiring))
                    (@Polynomial.module.{0, 0} Complex Complex.instSemiring Complex Complex.instSemiring
                      (@Semiring.toModule.{0} Complex Complex.instSemiring))
                    (@Polynomial.module.{0, 0} Complex Complex.instSemiring Complex Complex.instSemiring
                      (@Semiring.toModule.{0} Complex Complex.instSemiring)))
                  (@Polynomial.{0} Complex Complex.instSemiring)
                  (fun (x : @Polynomial.{0} Complex Complex.instSemiring) ↦
                    @Polynomial.{0} Complex Complex.instSemiring)
                  (@LinearMap.instFunLike.{0, 0, 0, 0} Complex Complex
                    (@Polynomial.{0} Complex Complex.instSemiring)
                    (@Polynomial.{0} Complex Complex.instSemiring) Complex.instSemiring
                    Complex.instSemiring
                    (@Semiring.toAddCommMonoid.{0} (@Polynomial.{0} Complex Complex.instSemiring)
                      (@Polynomial.semiring.{0} Complex Complex.instSemiring))
                    (@Semiring.toAddCommMonoid.{0} (@Polynomial.{0} Complex Complex.instSemiring)
                      (@Polynomial.semiring.{0} Complex Complex.instSemiring))
                    (@Polynomial.module.{0, 0} Complex Complex.instSemiring Complex Complex.instSemiring
                      (@Semiring.toModule.{0} Complex Complex.instSemiring))
                    (@Polynomial.module.{0, 0} Complex Complex.instSemiring Complex Complex.instSemiring
                      (@Semiring.toModule.{0} Complex Complex.instSemiring))
                    (@RingHom.id.{0} Complex
                      (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring)))
                  (@Polynomial.derivative.{0} Complex Complex.instSemiring)
                  (Erdos115.extremal_polynomial n))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@Nat.cast.{0} Real Real.instNatCast n))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat
                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@Nat.cast.{0} Real Real.instNatCast n)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  := by
  sorry
