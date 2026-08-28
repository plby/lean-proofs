import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageGlobalStalk
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreComparison
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyBaseFunctionAction

/-!
# Genuine base-function multiplication under actual fibre evaluation

Multiplication by an original holomorphic base function restricts on
the actual fibre to multiplication by its value at the base point.
The canonical all-degree finite-pushforward comparison preserves this
coefficient square. Thus the genuine global cohomology restriction is
compatible with the original holomorphic base-module action and the
original complex action on fibre cohomology.

This file does not define or transport a module structure on the raw
higher-direct-image stalk, and asserts no base-change isomorphism.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.BaseScalar

open PeriodFamilyHolomorphicCohomology.BaseFunctionAction
open CuspNormalization.SheafCohomologyFinitePushforward
open FibreGeometry

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual coefficient restriction turns a genuine base-function
multiplier into the original fibre scalar endomorphism. -/
@[reassoc] theorem coefficientPullback_baseMultiply (P : HolomorphicPeriodMap V B)
    (b : B) (g : BaseFunction V B) :
    baseMultiplyEnd P g ≫ coefficientPullback P b =
      coefficientPullback P b ≫
        (pushforward (fibreMap P b)).map (fibreScalarEnd P b (g b)) := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro t
  rfl

variable [T2Space B]

/-- Genuine global restriction to the original fibre in every native Ext degree. -/
def globalFibreEvaluation (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ) :
    CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q →+
      PeriodTorusHolomorphicCohomology.H (P.point b) q :=
  (cohomologyEquiv (fibreMap P b) (fibreMap_isClosedMap P b) (fibreMap_finite_fibres P b)
    (PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b)) q).toAddMonoidHom.comp
      (CategoryTheory.Sheaf.H.map (coefficientPullback P b) q)

/-- Evaluation of the genuine derived-stalk germ is precisely this
original all-degree global restriction map. -/
theorem fibreEvaluation_globalStalkClass (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) :
    fibreEvaluation P b q
        (GlobalRestriction.globalStalkClass (Zero.projectionMap P)
          (Zero.totalAdditiveSheaf P) b q a) = globalFibreEvaluation P b q a :=
  GlobalRestriction.derivedStalkEvaluation_global (Zero.projectionMap P) (Zero.totalAdditiveSheaf P)
    b q (fibreMap P b) (fibreMap_isClosedMap P b) (fibreMap_finite_fibres P b)
    (coefficientPullback P b) (projection_fibreMap_apply P b) a

omit [T2Space B] in
/-- The original cohomology maps preserve the actual base-multiplier
coefficient square, before applying the finite-pushforward equivalence. -/
theorem map_coefficientPullback_baseMultiply (P : HolomorphicPeriodMap V B) (b : B)
    (q : ℕ) (g : BaseFunction V B)
    (a : CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) :
    CategoryTheory.Sheaf.H.map (coefficientPullback P b) q
        (CategoryTheory.Sheaf.H.map (baseMultiplyEnd P g) q a) =
      CategoryTheory.Sheaf.H.map
        ((pushforward (fibreMap P b)).map (fibreScalarEnd P b (g b))) q
        (CategoryTheory.Sheaf.H.map (coefficientPullback P b) q a) :=
  (CategoryTheory.Sheaf.H.map_comp_apply
    (baseMultiplyEnd P g) (coefficientPullback P b) a).symm.trans
    ((congrArg (fun k => CategoryTheory.Sheaf.H.map k q a)
      (coefficientPullback_baseMultiply P b g)).trans
        (CategoryTheory.Sheaf.H.map_comp_apply (coefficientPullback P b)
          ((pushforward (fibreMap P b)).map (fibreScalarEnd P b (g b))) a))

/-- Original base multiplication restricts to multiplication by the
actual base-point value on the original fibre cohomology group. -/
theorem globalFibreEvaluation_baseMultiply (P : HolomorphicPeriodMap V B) (b : B)
    (q : ℕ) (g : BaseFunction V B)
    (a : CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) :
    globalFibreEvaluation P b q (CategoryTheory.Sheaf.H.map (baseMultiplyEnd P g) q a) =
      g b • globalFibreEvaluation P b q a :=
  (congrArg (cohomologyEquiv (fibreMap P b) (fibreMap_isClosedMap P b)
    (fibreMap_finite_fibres P b)
    (PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b)) q)
    (map_coefficientPullback_baseMultiply P b q g a)).trans
      (cohomologyEquiv_naturality (fibreMap P b) (fibreMap_isClosedMap P b)
        (fibreMap_finite_fibres P b) (fibreScalarEnd P b (g b)) q
        (CategoryTheory.Sheaf.H.map (coefficientPullback P b) q a))

/-- The same equality for the genuine coefficient-induced holomorphic
base-module action, retaining the original complex action on the fibre. -/
theorem globalFibreEvaluation_base_smul (P : HolomorphicPeriodMap V B) (b : B)
    (q : ℕ) (g : BaseFunction V B)
    (a : CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) :
    letI := baseCohomologyModule P q
    globalFibreEvaluation P b q (g • a) = g b • globalFibreEvaluation P b q a :=
  globalFibreEvaluation_baseMultiply P b q g a

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.BaseScalar
