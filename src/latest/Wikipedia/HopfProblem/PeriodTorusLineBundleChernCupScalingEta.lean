import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCupScaling
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernEtaCupSquare

/-!
# Cup products of the actual native η Chern classes

The genuine Alexander--Whitney cup product of the winding-defined first
Chern classes of the realized native bundles is bilinear in their integer
parameters. Its evaluation uses the original positive real period order
`(γ, u, w, δ)`; no comparison with the complex orientation is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open SingularCohomologyCup PeriodTorusCohomology PeriodTorusCohomologyCup
open PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The genuine mixed cup product of the actual native Chern classes. -/
theorem firstChernClass_etaChernFactor_cup_product (p : PeriodDomain) (m n : ℤ) :
    cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p m))
      (firstChernClass (etaChernFactor p n)) =
        (12 * m * n) • positivePeriodTopCohomologyClass p := by
  rw [firstChernClass_etaChernFactor, firstChernClass_etaChernFactor,
    cupProduct_smul_smul, etaCupSquare_eq_twelve, ← mul_zsmul]
  congr 1
  ring

/-- Exact mixed Chern number on every genuine top-degree homology class. -/
theorem firstChernClass_etaChernFactor_cup_product_evaluate (p : PeriodDomain)
    (m n : ℤ) (a : SingularHomology p.Torus 4) :
    singularEvaluation p.Torus 4
      (cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p m))
        (firstChernClass (etaChernFactor p n))) a =
      periodTorusH4Equiv p a * (12 * m * n) := by
  rw [firstChernClass_etaChernFactor_cup_product, map_zsmul,
    LinearMap.smul_apply, positivePeriodTopCohomologyClass_evaluate,
    zsmul_eq_mul, Int.cast_id]
  exact mul_comm _ _

/-- The original positive four-period product measures the mixed Chern number. -/
theorem firstChernClass_etaChernFactor_cup_product_positivePeriodTop
    (p : PeriodDomain) (m n : ℤ) :
    singularEvaluation p.Torus 4
      (cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p m))
        (firstChernClass (etaChernFactor p n))) (positivePeriodTopClass p) =
      12 * m * n := by
  rw [firstChernClass_etaChernFactor_cup_product_evaluate,
    positivePeriodTopClass_marking, one_mul]

/-- The genuine cup square of the native bundle realizing the class `nη`. -/
theorem firstChernClass_etaChernFactor_cup_square (p : PeriodDomain) (n : ℤ) :
    cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p n))
      (firstChernClass (etaChernFactor p n)) =
        (12 * n ^ 2) • positivePeriodTopCohomologyClass p := by
  simpa only [pow_two, mul_assoc] using
    firstChernClass_etaChernFactor_cup_product p n n

/-- Exact evaluation of every native η Chern square on genuine top homology. -/
theorem firstChernClass_etaChernFactor_cup_square_evaluate (p : PeriodDomain)
    (n : ℤ) (a : SingularHomology p.Torus 4) :
    singularEvaluation p.Torus 4
      (cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p n))
        (firstChernClass (etaChernFactor p n))) a =
      periodTorusH4Equiv p a * (12 * n ^ 2) := by
  simpa only [pow_two, mul_assoc] using
    firstChernClass_etaChernFactor_cup_product_evaluate p n n a

/-- Every realized native multiple has Chern square `12n²` in the period orientation. -/
theorem firstChernClass_etaChernFactor_cup_square_positivePeriodTop
    (p : PeriodDomain) (n : ℤ) :
    singularEvaluation p.Torus 4
      (cupProduct p.Torus 2 2 (firstChernClass (etaChernFactor p n))
        (firstChernClass (etaChernFactor p n))) (positivePeriodTopClass p) =
      12 * n ^ 2 := by
  simpa only [pow_two, mul_assoc] using
    firstChernClass_etaChernFactor_cup_product_positivePeriodTop p n n

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
