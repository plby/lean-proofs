import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkBaseActionBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreNaturality
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageBaseScalar

/-!
# Genuine fibre evaluation preserves the original derived-stalk actions

The source actions are the native right-derived images of original
coefficient multipliers, followed by the native stalk functor. The
proved coefficient-natural comparison identifies their fibre values
with the original complex actions on the actual fibre cohomology.

Global base functions act on the fibre through evaluation at the
original base point. No local generation or base-change isomorphism
is asserted.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction

open PeriodFamilyHolomorphicCohomology.BaseFunctionAction
open FibreGeometry

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- Actual fibre evaluation commutes with the native derived-stalk map
of every original holomorphic base-function multiplier. -/
theorem fibreEvaluation_baseMultiply (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (g : BaseFunction V B) (x : higherDirectImageStalk P b q) :
    fibreEvaluation P b q
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map
          (((SheafHigherDirectImage.functor (Zero.projectionMap P) q).map
            (baseMultiplyEnd P g)).hom) x) =
      g b • fibreEvaluation P b q x :=
  FibreNeighborhood.derivedStalkEvaluation_naturality_apply
    (fibreMap P b) (fibreMap_isClosedMap P b) (fibreMap_finite_fibres P b)
    (coefficientPullback P b) (coefficientPullback P b)
    (baseMultiplyEnd P g) (fibreScalarEnd P b (g b))
    (BaseScalar.coefficientPullback_baseMultiply P b g)
    (Zero.projectionMap P) b (projection_fibreMap_apply P b) q x

/-- The genuine global-base-module action becomes the original scalar
action by the literal base-point value on every actual fibre class. -/
theorem fibreEvaluation_base_smul (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (g : BaseFunction V B) (x : higherDirectImageStalk P b q) :
    letI := stalkBaseModule P b q
    fibreEvaluation P b q (g • x) = g b • fibreEvaluation P b q x :=
  fibreEvaluation_baseMultiply P b q g x

/-- Original complex coefficient multiplication is preserved by
the genuine all-degree derived-stalk-to-fibre evaluation. -/
theorem fibreEvaluation_complex_smul (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (c : ℂ) (x : higherDirectImageStalk P b q) :
    letI := stalkComplexModule P b q
    fibreEvaluation P b q (c • x) = c • fibreEvaluation P b q x :=
  FibreNeighborhood.derivedStalkEvaluation_naturality_apply
    (fibreMap P b) (fibreMap_isClosedMap P b) (fibreMap_finite_fibres P b)
    (coefficientPullback P b) (coefficientPullback P b)
    (Zero.totalScalarEnd P c) (fibreScalarEnd P b c)
    (coefficientPullback_scalar P b c)
    (Zero.projectionMap P) b (projection_fibreMap_apply P b) q x

/-- The original evaluation map is complex-linear for the independently
coefficient-induced module structures on the actual source and target. -/
def fibreEvaluationLinearMap (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ) :
    letI := stalkComplexModule P b q
    higherDirectImageStalk P b q →ₗ[ℂ] PeriodTorusHolomorphicCohomology.H (P.point b) q := by
  letI := stalkComplexModule P b q
  exact { (fibreEvaluation P b q).hom with map_smul' := fibreEvaluation_complex_smul P b q }

@[simp] theorem fibreEvaluationLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (q : ℕ) (x : higherDirectImageStalk P b q) :
    letI := stalkComplexModule P b q
    fibreEvaluationLinearMap P b q x = fibreEvaluation P b q x := rfl

/-- The original degree-one Haar-mean fibre coordinates, now as an
actual complex-linear map from the genuine derived stalk. -/
def oneFibreCoordinatesLinearMap (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkComplexModule P b 1
    higherDirectImageStalk P b 1 →ₗ[ℂ] (Fin 2 → ℂ) := by
  letI := stalkComplexModule P b 1
  exact (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b)).toLinearMap.comp
    (fibreEvaluationLinearMap P b 1)

@[simp] theorem oneFibreCoordinatesLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (x : higherDirectImageStalk P b 1) :
    letI := stalkComplexModule P b 1
    oneFibreCoordinatesLinearMap P b x = oneFibreCoordinates P b x := rfl

/-- The original top Haar-mean fibre coordinate, with the actual
complex coefficient actions on source and target. -/
def twoFibreCoordinateLinearMap (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkComplexModule P b 2
    higherDirectImageStalk P b 2 →ₗ[ℂ] ℂ := by
  letI := stalkComplexModule P b 2
  exact (PeriodTorusHolomorphicCohomology.h2Equiv (P.point b)).toLinearMap.comp
    (fibreEvaluationLinearMap P b 2)

@[simp] theorem twoFibreCoordinateLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (x : higherDirectImageStalk P b 2) :
    letI := stalkComplexModule P b 2
    twoFibreCoordinateLinearMap P b x = twoFibreCoordinate P b x := rfl

/-- A global holomorphic base multiplier vanishing at the point sends
every actual stalk element into the genuine fibre-evaluation kernel. -/
theorem fibreEvaluation_base_smul_eq_zero (P : HolomorphicPeriodMap V B)
    (b : B) (q : ℕ) (g : BaseFunction V B) (hg : g b = 0)
    (x : higherDirectImageStalk P b q) :
    letI := stalkBaseModule P b q
    fibreEvaluation P b q (g • x) = 0 := by
  let := stalkBaseModule P b q
  exact (fibreEvaluation_base_smul P b q g x).trans (by rw [hg, zero_smul])

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction
