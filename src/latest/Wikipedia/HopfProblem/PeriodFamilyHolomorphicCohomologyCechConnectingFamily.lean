import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingKernel
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibre
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycle
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleFibre

/-!
# The actual fibre marking of the original period-character class

The genuine negative local primitives compare the restricted family
cocycle with its original native Dolbeault class. Literal restriction
of the original total-space Ext class therefore has the negative marked
antiholomorphic coefficients as its actual fibre coordinates. This is
a comparison of the given classes, not a higher-direct-image base-change
isomorphism or a local-generation assertion.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

open HolomorphicPicard.CechExtension PeriodTorusHolomorphicCohomology
open CuspNormalization.SheafCohomologyFinitePushforward
open PeriodFamilyHigherDirectImage.FibreGeometry

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual restricted cocycle has the native Dolbeault class of its
actual constant pair, with the negative sign forced by the original lifts. -/
theorem fibreCocycle_classOf (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    classOf (CocycleFibre.fibreCocycle P b a) (CocycleFibre.fibreCover_covers P b) =
      nativeH1Class (P.point b) (CocycleFibre.fibreConstantPair P b a)
        (CocycleFibre.fibreConstantPair_closed P b a) :=
  classOf_eq_nativeH1Class_of_differential (P.point b)
    (CocycleFibre.fibreCocycle P b a) (CocycleFibre.fibreCover_covers P b)
    (CocycleFibre.fibreConstantPair P b a) (CocycleFibre.fibreConstantPair_closed P b a)
    (CocycleFibre.fibreNegativeSection P b a)
    (CocycleFibre.fibreNegativeSection_differential_sheaf P b a)
    (CocycleFibre.fibreNegativeSection_difference_sheaf P b a)

/-- The coordinates of the actual fibre Čech class use the unchanged
native Haar marking and the original negative primitive sign. -/
theorem fibreCocycle_h1Equiv (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    h1Equiv (P.point b)
        (classOf (CocycleFibre.fibreCocycle P b a) (CocycleFibre.fibreCover_covers P b)) =
      -MarkedLinear.dbarLinear (P.point b) (fun j => a j b) :=
  (h1Equiv_classOf_of_differential (P.point b)
    (CocycleFibre.fibreCocycle P b a) (CocycleFibre.fibreCover_covers P b)
    (CocycleFibre.fibreConstantPair P b a) (CocycleFibre.fibreConstantPair_closed P b a)
    (CocycleFibre.fibreNegativeSection P b a)
    (CocycleFibre.fibreNegativeSection_differential_sheaf P b a)
    (CocycleFibre.fibreNegativeSection_difference_sheaf P b a)).trans
      (CocycleFibre.fibreConstantPair_mean P b a)

variable [T2Space B]

/-- The original coefficient restriction followed by the canonical
finite-pushforward comparison is the literal restricted Čech class. -/
theorem periodClass_fibre_restriction (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    cohomologyEquiv (fibreMap P b) (fibreMap_isClosedMap P b) (fibreMap_finite_fibres P b)
        (holomorphicSheaf (P.point b)) 1
        (CategoryTheory.Sheaf.H.map (coefficientPullback P b) 1 (Cocycle.periodClass P a)) =
      classOf (CocycleFibre.fibreCocycle P b a) (CocycleFibre.fibreCover_covers P b) :=
  CechFibre.cohomologyEquiv_map_classOf (fibreMap P b) (fibreMap_isClosedMap P b)
    (fibreMap_finite_fibres P b) (coefficientPullback P b)
    (Cocycle.cocycle P a) (Cocycle.coverOpen_covers P)

/-- The native class of the actual restricted period character is
the class of its genuine negative marked constant pair. -/
theorem periodClass_fibre_nativeH1Class (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    cohomologyEquiv (fibreMap P b) (fibreMap_isClosedMap P b) (fibreMap_finite_fibres P b)
        (holomorphicSheaf (P.point b)) 1
        (CategoryTheory.Sheaf.H.map (coefficientPullback P b) 1 (Cocycle.periodClass P a)) =
      nativeH1Class (P.point b) (CocycleFibre.fibreConstantPair P b a)
        (CocycleFibre.fibreConstantPair_closed P b a) :=
  (periodClass_fibre_restriction P b a).trans (fibreCocycle_classOf P b a)

/-- The actual total-space period class restricts to precisely its
negative marked antiholomorphic coordinates under the original fibre comparison. -/
theorem periodClass_fibre_coordinates (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    h1Equiv (P.point b)
        (cohomologyEquiv (fibreMap P b) (fibreMap_isClosedMap P b)
          (fibreMap_finite_fibres P b) (holomorphicSheaf (P.point b)) 1
          (CategoryTheory.Sheaf.H.map (coefficientPullback P b) 1 (Cocycle.periodClass P a))) =
      -MarkedLinear.dbarLinear (P.point b) (fun j => a j b) :=
  (congrArg (h1Equiv (P.point b)) (periodClass_fibre_restriction P b a)).trans
    (fibreCocycle_h1Equiv P b a)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting
