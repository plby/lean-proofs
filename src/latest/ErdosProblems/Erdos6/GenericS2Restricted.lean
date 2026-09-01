import ErdosProblems.Erdos6.GenericS2
import BoundedGaps.Maynard.ImprovedGPY.S2RestrictedMainReindex
import BoundedGaps.Maynard.MaynardS2TotientFactorization
import BoundedGaps.Maynard.MaynardS2GDivisorExpansion
import BoundedGaps.Maynard.MaynardS2RestrictedReindex
import BoundedGaps.Maynard.MaynardS2RestrictedYDiagonal
import BoundedGaps.Maynard.MaynardS2YFaceSupport

/-!
# Candidate-generic restricted `S₂` reindexing

This file exposes the exact distinguished-coordinate quadratic kernel in the
generic tuple main term.  All statements are finite identities.
-/

namespace Erdos6.Maynard

open scoped BigOperators

noncomputable section

def tupleShiftedPrimeIntervalCount (N : ℕ) {H : Finset ℕ} (h : H) : ℝ :=
  (BoundedGaps.Maynard.primeCountTotal (2 * N + h.1 - 1) : ℝ) -
    (BoundedGaps.Maynard.primeCountTotal (N + h.1 - 1) : ℝ)

def tupleRestrictedMainCoefficient (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) (m : H) : ℝ :=
  BoundedGaps.Maynard.restrictedMainArithmeticCoefficient H
    (tupleMaynardSupport H alpha N) (maynardModulus N)
    (tupleMaynardCoefficient H alpha F N) m

theorem tupleMaynardS2Main_eq_shift_sum
    (H : Finset ℕ) (alpha : ℝ) (v : ℕ → ℕ)
    (F : (H → ℝ) → ℝ) (N : ℕ) :
    tupleMaynardS2Main H alpha v F N =
      ∑ m ∈ H.attach,
        tupleShiftedPrimeIntervalCount N m *
          tupleRestrictedMainCoefficient H alpha F N m := by
  unfold tupleMaynardS2Main tupleRestrictedMainCoefficient
    tupleShiftedPrimeIntervalCount
  exact BoundedGaps.Maynard.compatiblePairRestrictedMainOuter_eq_shift_sum
    (tupleMaynardS2SupportProof H alpha N)

def tupleRestrictedTotientKernel (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) (m : H) : ℝ :=
  BoundedGaps.Maynard.compatibleDivisorPairRestrictedTotientKernel H
    (tupleMaynardSupport H alpha N)
    (tupleMaynardCoefficient H alpha F N) m

def tupleRestrictedGKernel (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) (m : H) : ℝ :=
  BoundedGaps.Maynard.compatibleDivisorPairRestrictedS2CommonDivisorTupleSum H
    (tupleMaynardSupport H alpha N)
    (tupleMaynardCoefficient H alpha F N) m

def tupleRestrictedQuadratic (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) (m : H) : ℝ :=
  BoundedGaps.Maynard.maynardS2RestrictedQuadraticTransform H
    (maynardRadius alpha N) (tupleMaynardSupport H alpha N)
    (tupleMaynardCoefficient H alpha F N) m

def tupleRestrictedCross (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) (m : H) : ℝ :=
  BoundedGaps.Maynard.incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H
    (tupleMaynardSupport H alpha N)
    (tupleMaynardCoefficient H alpha F N) m

def tupleRestrictedYDiagonal (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) (m : H) : ℝ :=
  BoundedGaps.Maynard.maynardS2RestrictedYDiagonalSum H
    (maynardRadius alpha N) (maynardModulus N)
    (tupleMaynardCoefficient H alpha F N) m

def tupleCoordinateOneYDiagonal (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) (m : H) : ℝ :=
  BoundedGaps.Maynard.maynardS2RestrictedYCoordinateOneDiagonalSum H
    (maynardRadius alpha N) (maynardModulus N)
    (tupleMaynardCoefficient H alpha F N) m

theorem tupleRestrictedMainCoefficient_eq_invTotient_mul_GKernel
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ)
    (N : ℕ) (m : H) :
    tupleRestrictedMainCoefficient H alpha F N m =
      (Nat.totient (maynardModulus N) : ℝ)⁻¹ *
        tupleRestrictedGKernel H alpha F N m := by
  classical
  unfold tupleRestrictedMainCoefficient tupleRestrictedGKernel
    BoundedGaps.Maynard.restrictedMainArithmeticCoefficient
  rw [BoundedGaps.Maynard.restrictedDivisorPairModulusTotientSum_eq_invTotient_mul]
  · congr 1
    · apply
        BoundedGaps.Maynard.compatibleDivisorPairRestrictedTotientKernel_eq_commonDivisorS2TupleSum
      · intro d hd
        exact tupleMaynardS2SupportProof H alpha N d hd
  · intro d hd
    exact tupleMaynardS2SupportProof H alpha N d hd

theorem tupleRestrictedGKernel_eq_quadratic_sub_cross
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ)
    (N : ℕ) (m : H) :
    tupleRestrictedGKernel H alpha F N m =
      tupleRestrictedQuadratic H alpha F N m -
        tupleRestrictedCross H alpha F N m := by
  unfold tupleRestrictedGKernel tupleRestrictedQuadratic tupleRestrictedCross
  rw [BoundedGaps.Maynard.compatibleRestrictedS2SubtypeSum_eq_membershipSum]
  rw [BoundedGaps.Maynard.compatibleRestrictedS2_eq_unrestricted_sub_incompatible]
  rw [BoundedGaps.Maynard.unrestrictedRestrictedS2_eq_quadraticTransform]
  · intro d hd
    exact tupleMaynardS2SupportProof H alpha N d hd

theorem tupleRestrictedQuadratic_eq_yDiagonal
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ)
    (N : ℕ) (m : H) :
    tupleRestrictedQuadratic H alpha F N m =
      tupleRestrictedYDiagonal H alpha F N m := by
  unfold tupleRestrictedQuadratic tupleRestrictedYDiagonal tupleMaynardSupport
  exact BoundedGaps.Maynard.maynardS2RestrictedQuadraticTransform_eq_yDiagonal m

theorem tupleRestrictedYDiagonal_eq_coordinateOne
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ)
    (N : ℕ) (m : H) :
    tupleRestrictedYDiagonal H alpha F N m =
      tupleCoordinateOneYDiagonal H alpha F N m := by
  unfold tupleRestrictedYDiagonal tupleCoordinateOneYDiagonal
  exact BoundedGaps.Maynard.maynardS2RestrictedYDiagonalSum_eq_coordinateOne
    H (maynardRadius alpha N) (maynardModulus N) _ m

theorem tupleMaynardS2Main_eq_coordinateOne_sub_cross_sum
    (H : Finset ℕ) (alpha : ℝ) (v : ℕ → ℕ)
    (F : (H → ℝ) → ℝ) (N : ℕ) :
    tupleMaynardS2Main H alpha v F N =
      ∑ m ∈ H.attach,
        tupleShiftedPrimeIntervalCount N m *
          ((Nat.totient (maynardModulus N) : ℝ)⁻¹ *
            (tupleCoordinateOneYDiagonal H alpha F N m -
              tupleRestrictedCross H alpha F N m)) := by
  rw [tupleMaynardS2Main_eq_shift_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [tupleRestrictedMainCoefficient_eq_invTotient_mul_GKernel,
    tupleRestrictedGKernel_eq_quadratic_sub_cross,
    tupleRestrictedQuadratic_eq_yDiagonal,
    tupleRestrictedYDiagonal_eq_coordinateOne]

end

end Erdos6.Maynard
