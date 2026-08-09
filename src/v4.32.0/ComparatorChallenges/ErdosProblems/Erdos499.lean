import Mathlib.Analysis.Convex.DoublyStochasticMatrix

attribute [local instance] Classical.propDecidable

theorem Erdos499.erdos_499 :
    ∀ (n : Nat) (M : Matrix.{0, 0, 0} (Fin n) (Fin n) Real),
      @Membership.mem.{0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
          (@Submonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
            (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
              (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                (@Matrix.semiring.{0, 0} (Fin n) Real Real.semiring (Fin.fintype n)
                  (instDecidableEqFin n)))))
          (@SetLike.instMembership.{0, 0}
            (@Submonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
              (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                  (@Matrix.semiring.{0, 0} (Fin n) Real Real.semiring (Fin.fintype n)
                    (instDecidableEqFin n)))))
            (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
            (@Submonoid.instSetLike.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
              (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                  (@Matrix.semiring.{0, 0} (Fin n) Real Real.semiring (Fin.fintype n)
                    (instDecidableEqFin n))))))
          (@doublyStochastic.{0, 0} Real (Fin n) (Fin.fintype n) (instDecidableEqFin n) Real.semiring
            Real.partialOrder Real.instIsOrderedRing)
          M →
        @Exists.{1} (Equiv.Perm.{1} (Fin n)) fun (σ : Equiv.Perm.{1} (Fin n)) ↦
          @LE.le.{0} Real Real.instLE
            (@HPow.hPow.{0, 0, 0} Real Int Real
              (@instHPow.{0, 0} Real Int
                (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast n)
              (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt n)))
            (@Finset.prod.{0, 0} (Fin n) Real Real.instCommMonoid
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) fun (i : Fin n) ↦
              M i
                (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (x : Fin n) ↦ Fin n)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (Fin n)
                    (@Equiv.instEquivLike.{1, 1} (Fin n) (Fin n)))
                  σ i))
  := by
  sorry
