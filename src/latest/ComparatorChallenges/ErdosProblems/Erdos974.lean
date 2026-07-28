import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.SimpleRing.Principal

attribute [local instance] Classical.propDecidable

namespace Erdos974

structure ProblemData (n : ℕ) [NeZero n] where
  z : Fin n → ℂ
  (a b : ℤ)
  z0 : z 0 = 1
  hab : a < b
  sums_a : ∀ k < n - 1, ∑ i, z i ^ (a + k) = 0
  sums_b : ∀ k < n - 1, ∑ i, z i ^ (b + k) = 0

end Erdos974

noncomputable def Erdos974.ProblemData.oddIndices :
    {n : Nat} →
      [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
        @Erdos974.ProblemData
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
            (@instNeZeroNatHMul (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              inst) →
          Finset.{0}
            (Fin
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
  := by
  sorry

theorem Erdos974.ProblemData.erdos974_even :
    ∀ {n : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n]
      (PD :
        @Erdos974.ProblemData
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
          (@instNeZeroNatHMul (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) inst)),
      @Eq.{1} (Finset.{0} Complex)
        (@Finset.image.{0, 0}
          (Fin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
          Complex Complex.instDecidableEq
          (@Erdos974.ProblemData.z
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
            (@instNeZeroNatHMul (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) inst)
            PD)
          (@Finset.univ.{0}
            (Fin
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
            (Fin.fintype
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))))
        (@Union.union.{0} (Finset.{0} Complex) (@Finset.instUnion.{0} Complex Complex.instDecidableEq)
          (@Polynomial.nthRootsFinset.{0} n Complex
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
            Complex.commRing
            (@IsDomain.of_isSimpleRing.{0} Complex Complex.commRing
              (@DivisionRing.isSimpleRing.{0} Complex
                (@Field.toDivisionRing.{0} Complex Complex.instField))))
          (@Polynomial.nthRootsFinset.{0} n Complex
            (@Neg.neg.{0} Complex Complex.instNeg
              (@Finset.prod.{0, 0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing)
                (@Erdos974.ProblemData.oddIndices n inst PD)
                fun
                  (i :
                    Fin
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)) ↦
                @Neg.neg.{0} Complex Complex.instNeg
                  (@Erdos974.ProblemData.z
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                    (@instNeZeroNatHMul (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      inst)
                    PD i)))
            Complex.commRing
            (@IsDomain.of_isSimpleRing.{0} Complex Complex.commRing
              (@DivisionRing.isSimpleRing.{0} Complex
                (@Field.toDivisionRing.{0} Complex Complex.instField)))))
  := by
  sorry
