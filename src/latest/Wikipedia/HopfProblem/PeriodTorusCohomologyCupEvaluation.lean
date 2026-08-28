import Wikipedia.HopfProblem.PeriodTorusCohomologyCupEtaCochain
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupCycles

/-!
# Native cup evaluation on the genuine positive period cycles

The native cocycle evaluations are identified with the finite formal
prism functionals by the proved equality of actual chain representatives.
The original period-coordinate homeomorphism preserves both the actual
cup product and the positive period-product generator.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin SingularCohomologyCup

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Evaluation on an actual ordered pair of loops is the corresponding formal prism value. -/
theorem coordinateEtaClass_pair_evaluation (x y : Lattice) :
    singularEvaluation (ProductTorus 4) 2 coordinateEtaClass
        (product11 (ProductTorus 4) (loopHomologyClass (coordinatePeriodLoop 4 x))
          (loopHomologyClass (coordinatePeriodLoop 4 y))) =
      formalEtaEvaluation (formalPeriodProduct 1 (formalPeriodEdge x) (formalPeriodEdge y)) := by
  rw [← coordinatePairCycle_class, coordinateEtaClass, singularEvaluation_cocycle_cycle,
    coordinateEtaCocycle_val, coordinatePairCycle_val, coordinateEtaCochain_affineChain]

/-- The genuine cup square pairs with the genuine positive top class by the formal square. -/
theorem coordinateEtaSquare_top_evaluation :
    singularEvaluation (ProductTorus 4) 4
        (cupProduct (ProductTorus 4) 2 2 coordinateEtaClass coordinateEtaClass)
        (productTorusTopClass 4) = formalEtaSquareEvaluation formalPositiveTop := by
  rw [← coordinateTopCycle_class]
  refine (cupProduct_evaluate_cocycles (ProductTorus 4) 2 2
    coordinateEtaCocycle coordinateEtaCocycle coordinateTopCycle).trans ?_
  rw [coordinateEtaCocycle_val, coordinateTopCycle_val, coordinateEtaSquare_affineChain]

/-- The original period-coordinate pullback retains evaluation on every positive period pair. -/
theorem coordinateEtaPullback_pair_evaluation (p : PeriodDomain) (x y : Lattice) :
    singularEvaluation p.Torus 2
        (singularCohomologyPullback (periodTorusCircleHomeomorph p : C(_, _)) 2
          coordinateEtaClass)
        (product11 p.Torus (loopHomologyClass (p.periodLoop x))
          (loopHomologyClass (p.periodLoop y))) =
      formalEtaEvaluation (formalPeriodProduct 1 (formalPeriodEdge x) (formalPeriodEdge y)) := by
  rw [singularEvaluation_naturality, periodProduct_coordinate_image,
    positivePeriodLoop_coordinate_image, positivePeriodLoop_coordinate_image,
    coordinateEtaClass_pair_evaluation]

/-- Naturality compares the period-torus cup square with the same exact prism value. -/
theorem coordinateEtaPullback_square_top_evaluation (p : PeriodDomain) :
    singularEvaluation p.Torus 4
        (cupProduct p.Torus 2 2
          (singularCohomologyPullback (periodTorusCircleHomeomorph p : C(_, _)) 2
            coordinateEtaClass)
          (singularCohomologyPullback (periodTorusCircleHomeomorph p : C(_, _)) 2
            coordinateEtaClass))
        (positivePeriodTopClass p) = formalEtaSquareEvaluation formalPositiveTop := by
  rw [← cupProduct_pullback, singularEvaluation_naturality,
    positivePeriodTopClass_coordinate_image, coordinateEtaSquare_top_evaluation]

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
