import Wikipedia.HopfProblem.PeriodTorusLineBundleChernEta
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupSquare

/-!
# The actual cup square of the realized native Chern class

The native bundle for the negative Hermitian form realizes `η` as its
positive-winding first Chern class.  Its genuine Alexander--Whitney
singular cup square evaluates to twelve on the actual positive product
of the four original period loops.
The reference orientation is that real period order, not an assumed
identification with the complex orientation or Poincaré duality.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open SingularCohomologyCup PeriodTorusCohomology PeriodTorusCohomologyCup
open PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The genuine cup square of the actual distinguished native first Chern class. -/
theorem firstChernClass_etaChernFactor_one_cup_square (p : PeriodDomain) :
    cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p 1))
      (firstChernClass (etaChernFactor p 1)) =
        (12 : ℤ) • positivePeriodTopCohomologyClass p := by
  rw [firstChernClass_etaChernFactor_one]
  exact etaCupSquare_eq_twelve p

/-- Exact evaluation on every actual top-degree singular homology class. -/
theorem firstChernClass_etaChernFactor_one_cup_square_evaluate (p : PeriodDomain)
    (a : SingularHomology p.Torus 4) :
    singularEvaluation p.Torus 4
      (cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p 1))
        (firstChernClass (etaChernFactor p 1))) a =
      periodTorusH4Equiv p a * 12 := by
  rw [firstChernClass_etaChernFactor_one]
  exact etaCupSquare_evaluate p a

/-- In particular the actual distinguished line bundle has Chern square twelve. -/
theorem firstChernClass_etaChernFactor_one_cup_square_positivePeriodTop (p : PeriodDomain) :
    singularEvaluation p.Torus 4
      (cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p 1))
        (firstChernClass (etaChernFactor p 1))) (positivePeriodTopClass p) = 12 := by
  rw [firstChernClass_etaChernFactor_one]
  exact etaCupSquare_evaluate_positivePeriodTop p

theorem firstChernClass_etaChernFactor_one_cup_square_ne_zero (p : PeriodDomain) :
    cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p 1))
      (firstChernClass (etaChernFactor p 1)) ≠ 0 := by
  rw [firstChernClass_etaChernFactor_one]
  exact etaCupSquare_ne_zero p

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
