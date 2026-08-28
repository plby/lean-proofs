import Wikipedia.HopfProblem.PeriodTorusCohomologyCupEtaCochain
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupOne

/-!
# The actual degree-one cup decomposition of the distinguished class

These equalities hold first for native cocycle representatives and then
for their actual cohomology classes, including the original period-torus
pullback.  They do not impose an exterior-algebra multiplication on the
cohomology groups.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open SingularCohomologyFree SingularCohomologyCup PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The equality already holds between the actual cocycle representatives. -/
theorem coordinateEtaCocycle_eq_cups :
    coordinateEtaCocycle =
      cupCocycles (ProductTorus 4) 1 1 (coordinateOneCocycle 4 1) (coordinateOneCocycle 4 2) +
        (6 : ℤ) • cupCocycles (ProductTorus 4) 1 1
          (coordinateOneCocycle 4 0) (coordinateOneCocycle 4 3) := Subtype.ext rfl

/-- The native class is the displayed sum of actual degree-one cup products. -/
theorem coordinateEtaClass_eq_cups :
    coordinateEtaClass =
      cupProduct (ProductTorus 4) 1 1 (coordinateOneClass 4 1) (coordinateOneClass 4 2) +
        (6 : ℤ) • cupProduct (ProductTorus 4) 1 1
          (coordinateOneClass 4 0) (coordinateOneClass 4 3) := by
  rw [coordinateEtaClass, coordinateEtaCocycle_eq_cups, map_add, map_zsmul]
  exact congrArg₂ (fun a b : SingularCohomology (ProductTorus 4) 2 => a + (6 : ℤ) • b)
    (cupProduct_cocycleClass (ProductTorus 4) 1 1
      (coordinateOneCocycle 4 1) (coordinateOneCocycle 4 2)).symm
    (cupProduct_cocycleClass (ProductTorus 4) 1 1
      (coordinateOneCocycle 4 0) (coordinateOneCocycle 4 3)).symm

/-- Naturality for an individual pair of the actual positive coordinate classes. -/
theorem coordinateOneCup_pullback (p : PeriodDomain) (i j : Fin 4) :
    singularCohomologyPullback
        (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) 2
        (cupProduct (ProductTorus 4) 1 1 (coordinateOneClass 4 i) (coordinateOneClass 4 j)) =
      cupProduct p.Torus 1 1 (periodOneClass p i) (periodOneClass p j) :=
  cupProduct_pullback (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) 1 1
    (coordinateOneClass 4 i) (coordinateOneClass 4 j)

/-- The same decomposition is retained by the original period-coordinate pullback. -/
theorem coordinateEtaPullback_eq_cups (p : PeriodDomain) :
    singularCohomologyPullback (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) 2
        coordinateEtaClass =
      cupProduct p.Torus 1 1 (periodOneClass p 1) (periodOneClass p 2) +
        (6 : ℤ) • cupProduct p.Torus 1 1 (periodOneClass p 0) (periodOneClass p 3) := by
  rw [coordinateEtaClass_eq_cups, map_add, map_zsmul]
  exact congrArg₂ (fun a b : SingularCohomology p.Torus 2 => a + (6 : ℤ) • b)
    (coordinateOneCup_pullback p 1 2) (coordinateOneCup_pullback p 0 3)

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
