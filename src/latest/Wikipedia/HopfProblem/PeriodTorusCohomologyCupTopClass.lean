import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingBasic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusProductDecomposition
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusHomomorphisms

/-!
# The actual positive period-product top generator

The generator here is the genuine ordered product of the four positive
period loops, in their declared real lattice order.  Its normalization
agrees with the already constructed recursive Mayer--Vietoris marking.
No comparison with a complex orientation is made.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The recursive positive four-torus class is the literal ordered product
of its four positive coordinate loops. -/
theorem productTorusTopClass_four :
    productTorusTopClass 4 = product (ProductTorus 4) 3
      (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 0 1)))
      (tripleProduct (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 1 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 2 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 3 1)))) := by
  rw [productTorusTopClass_succ_product, productTorusTopClass_three,
    tripleProduct_natural (torusTailMap 3) (torusTailMap_add 3),
    torusTailMap_coordinatePeriodHomology, torusTailMap_coordinatePeriodHomology,
    torusTailMap_coordinatePeriodHomology]
  have h₁ : Fin.cons 0 (Pi.single 0 1 : Fin 3 → ℤ) = (Pi.single 1 1 : Fin 4 → ℤ) := by
    decide
  have h₂ : Fin.cons 0 (Pi.single 1 1 : Fin 3 → ℤ) = (Pi.single 2 1 : Fin 4 → ℤ) := by
    decide
  have h₃ : Fin.cons 0 (Pi.single 2 1 : Fin 3 → ℤ) = (Pi.single 3 1 : Fin 4 → ℤ) := by
    decide
  rw [h₁, h₂, h₃]

/-- The genuine period-torus top class, with its specified positive real marking. -/
def positivePeriodTopClass (p : PeriodDomain) : SingularHomology p.Torus 4 :=
  (homeomorphHomologyEquiv (periodTorusCircleHomeomorph p) 4).symm (productTorusTopClass 4)

@[simp] theorem positivePeriodTopClass_coordinate_image (p : PeriodDomain) :
    singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 4
      (positivePeriodTopClass p) = productTorusTopClass 4 :=
  (homeomorphHomologyEquiv (periodTorusCircleHomeomorph p) 4).apply_symm_apply _

/-- The marking sends every actual positive period loop to the matching positive circle class. -/
theorem positivePeriodLoop_coordinate_image (p : PeriodDomain) (v : Lattice) :
    singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 1
      (loopHomologyClass (p.periodLoop v)) = loopHomologyClass (coordinatePeriodLoop 4 v) :=
  periodTorusCircle_inducedHomology_periodLoop p v

/-- Naturality of the actual product under the original period-coordinate homeomorphism. -/
theorem periodProduct_coordinate_image (p : PeriodDomain) (n : ℕ)
    (a : SingularHomology p.Torus 1) (b : SingularHomology p.Torus n) :
    singularHomologyMap (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) (n + 1)
        (product p.Torus n a b) =
      product (ProductTorus 4) n
        (singularHomologyMap (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) 1 a)
        (singularHomologyMap (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) n b) :=
  product_natural (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4))
    (periodTorusCircleHomeomorph_add p) n a b

/-- The actual positive fourfold period product, before comparing its top normalization. -/
def positivePeriodFourProduct (p : PeriodDomain) : SingularHomology p.Torus 4 :=
  product p.Torus 3 (loopHomologyClass (p.periodLoop (Pi.single 0 1)))
    (tripleProduct p.Torus
      (loopHomologyClass (p.periodLoop (Pi.single 1 1)))
      (loopHomologyClass (p.periodLoop (Pi.single 2 1)))
      (loopHomologyClass (p.periodLoop (Pi.single 3 1))))

theorem positivePeriodFourProduct_coordinate_image (p : PeriodDomain) :
    singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 4
      (positivePeriodFourProduct p) = productTorusTopClass 4 := by
  rw [positivePeriodFourProduct, periodProduct_coordinate_image,
    tripleProduct_natural _ (periodTorusCircleHomeomorph_add p),
    positivePeriodLoop_coordinate_image, positivePeriodLoop_coordinate_image,
    positivePeriodLoop_coordinate_image, positivePeriodLoop_coordinate_image]
  exact productTorusTopClass_four.symm

/-- This is a product of genuine singular classes of the original period loops. -/
theorem positivePeriodTopClass_period_product (p : PeriodDomain) :
    positivePeriodTopClass p = product p.Torus 3
      (loopHomologyClass (p.periodLoop (Pi.single 0 1)))
      (tripleProduct p.Torus
        (loopHomologyClass (p.periodLoop (Pi.single 1 1)))
        (loopHomologyClass (p.periodLoop (Pi.single 2 1)))
        (loopHomologyClass (p.periodLoop (Pi.single 3 1)))) := by
  change positivePeriodTopClass p = positivePeriodFourProduct p
  let e := homeomorphHomologyEquiv (periodTorusCircleHomeomorph p) 4
  have h : e (positivePeriodFourProduct p) = productTorusTopClass 4 :=
    positivePeriodFourProduct_coordinate_image p
  exact (congrArg e.symm h.symm).trans (e.symm_apply_apply _)

/-- The positive real period product has coefficient one in the actual top marking. -/
@[simp] theorem positivePeriodTopClass_marking (p : PeriodDomain) :
    periodTorusH4Equiv p (positivePeriodTopClass p) = 1 := by
  change (integerBinomialZeroEquiv 4).symm
    (periodTorusHomologyEquiv p 4 (positivePeriodTopClass p)) = 1
  rw [periodTorusHomologyEquiv_apply, positivePeriodTopClass_coordinate_image,
    productTorusHomologyEquiv_topClass]
  exact (integerBinomialZeroEquiv 4).symm_apply_apply 1

/-- Every genuine top homology class is its integral marked multiple of this generator. -/
theorem positivePeriodTopClass_spans (p : PeriodDomain) (a : SingularHomology p.Torus 4) :
    a = periodTorusH4Equiv p a • positivePeriodTopClass p := by
  apply (periodTorusH4Equiv p).injective
  rw [map_zsmul, positivePeriodTopClass_marking, zsmul_eq_mul, mul_one, Int.cast_id]

/-- The native singular-cohomology class dual to the actual positive period product. -/
def positivePeriodTopCohomologyClass (p : PeriodDomain) : SingularCohomology p.Torus 4 :=
  (PeriodTorusCohomology.evaluationEquiv p 4).symm (periodTorusH4Equiv p).toLinearMap

/-- Its normalization refers to the genuine evaluation pairing and the genuine top cycle. -/
@[simp] theorem positivePeriodTopCohomologyClass_evaluate (p : PeriodDomain)
    (a : SingularHomology p.Torus 4) :
    singularEvaluation p.Torus 4 (positivePeriodTopCohomologyClass p) a =
      periodTorusH4Equiv p a :=
  LinearMap.congr_fun ((PeriodTorusCohomology.evaluationEquiv p 4).apply_symm_apply
    (periodTorusH4Equiv p).toLinearMap) a

@[simp] theorem positivePeriodTop_pairing (p : PeriodDomain) :
    singularEvaluation p.Torus 4 (positivePeriodTopCohomologyClass p)
      (positivePeriodTopClass p) = 1 := by
  rw [positivePeriodTopCohomologyClass_evaluate, positivePeriodTopClass_marking]

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
