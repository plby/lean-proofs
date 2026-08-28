import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseCharactersMarking
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusDegreeOne
import Wikipedia.HopfProblem.EllipticFixedPeriods

/-!
# Positive period loops in the actual marked base torus

The ordered degree-one marking of the two-torus is the integral sum of
its actual positive coordinate loops.  Projecting the already marked
four-torus onto its first two coordinates proves that an arbitrary
integral vector is represented by the corresponding straight period loop.
This fixes the base-cycle marking used by the geometric theta calculation.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

/-- The original integral base marking is represented by its actual
positive straight period loop, including arbitrary signed coefficients. -/
theorem coordinateH1_two_apply (v : Fin 2 → ℤ) :
    coordinateH1 2 v = loopHomologyClass (coordinatePeriodLoop 2 v) := by
  let A : Matrix (Fin 2) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0]
  let w : Fin 4 → ℤ := ![v 0, v 1, 0, 0]
  have hAw : A *ᵥ w = v := by
    funext i
    fin_cases i <;> simp [A, w, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have hA0 : A *ᵥ (Pi.single 0 1 : Fin 4 → ℤ) = (Pi.single 0 1 : Fin 2 → ℤ) := by
    decide
  have hA1 : A *ᵥ (Pi.single 1 1 : Fin 4 → ℤ) = (Pi.single 1 1 : Fin 2 → ℤ) := by
    decide
  have hw : w = v 0 • (Pi.single 0 1 : Fin 4 → ℤ) + v 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp [w]
  have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → ℤ) + v 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  have hleft : inducedHomology (torusMatrixMap A) (coordinateH1 4 w) = coordinateH1 2 v := by
    rw [hw, map_add, map_zsmul, map_zsmul, coordinateH1_single, coordinateH1_single,
      map_add, map_zsmul, map_zsmul, torusMatrixMap_coordinatePeriodHomology,
      torusMatrixMap_coordinatePeriodHomology, hA0, hA1]
    conv_rhs => rw [hv, map_add, map_zsmul, map_zsmul, coordinateH1_single, coordinateH1_single]
  have h := congrArg (inducedHomology (torusMatrixMap A))
    (coordinateH1_four_apply (Elliptic.examplePeriod .four) w)
  rw [torusMatrixMap_coordinatePeriodHomology, hAw] at h
  exact hleft.symm.trans h

/-- The same positive marking after passage to actual one-chains modulo
two-boundaries; this also applies to nonclosed edge-chain comparisons. -/
theorem coordinatePeriodLoop_pathClass (v : Fin 2 → ℤ) :
    pathClass (coordinatePeriodLoop 2 v) =
      homologyToChainClass (ProductTorus 2) (coordinateH1 2 v) := by
  rw [coordinateH1_two_apply, homologyToChainClass_loopHomologyClass]

end Wikipedia.HopfProblem.CuspCentralHomology
