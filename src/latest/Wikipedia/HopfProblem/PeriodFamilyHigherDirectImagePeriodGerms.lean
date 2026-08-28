import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImagePeriodClasses
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageGlobalStalkVanishing
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearReduction

/-!
# Vanishing period-class germs force vanishing nearby fibre coordinates

The actual stalk is a filtered colimit of original neighborhood
cohomology groups. A zero period-class germ therefore vanishes on one
actual neighborhood, and its original fibre coordinates vanish at every
base point of that neighborhood. This criterion does not assume local
freeness or finite generation of the higher direct image.
-/

noncomputable section

open TopologicalSpace CategoryTheory Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage

open PeriodFamilyHolomorphicCohomology
open FibreGeometry

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [IsManifold (modelWithCornersSelf ℂ V) ω B]
  [T2Space B]

/-- Original restriction of the global period class has the same actual
marked fibre formula on every genuine base neighborhood. -/
theorem neighborhood_period_coordinates (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) (U : Opens B) (b : B) (hb : b ∈ U) :
    PeriodTorusHolomorphicCohomology.h1Equiv (P.point b)
        (neighborhoodFibreEvaluation P b 1 U hb
          (GlobalRestriction.restrictionMap (Zero.totalAdditiveSheaf P)
            ((Opens.map (Zero.projectionMap P)).obj U) 1 (Cocycle.periodClass P a))) =
      -MarkedLinear.dbarLinear (P.point b) (fun j => a j b) :=
  (congrArg (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b))
    (GlobalRestriction.cohomologyEvaluation_restriction
      (fibreMap P b) (fibreMap_isClosedMap P b) (fibreMap_finite_fibres P b)
      ((Opens.map (Zero.projectionMap P)).obj U) (fibreMap_mem_fullPreimage P b hb)
      (coefficientPullback P b) 1 (Cocycle.periodClass P a))).trans
        (CechConnecting.periodClass_fibre_coordinates P b a)

/-- If the original neighborhood class is zero, all its literal fibre
antiholomorphic coordinates vanish throughout that same neighborhood. -/
theorem dbar_eq_zero_of_neighborhood_period_zero (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) (U : Opens B)
    (hU : GlobalRestriction.restrictionMap (Zero.totalAdditiveSheaf P)
      ((Opens.map (Zero.projectionMap P)).obj U) 1 (Cocycle.periodClass P a) = 0)
    (b : B) (hb : b ∈ U) :
    MarkedLinear.dbarLinear (P.point b) (fun j => a j b) = 0 := by
  have hzero := (congrArg (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b))
    ((congrArg (neighborhoodFibreEvaluation P b 1 U hb) hU).trans
      (map_zero (neighborhoodFibreEvaluation P b 1 U hb)))).trans
        (map_zero (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b)))
  exact neg_eq_zero.mp ((neighborhood_period_coordinates P a U b hb).symm.trans hzero)

/-- A zero genuine period germ forces its actual marked fibre values
to vanish on a whole neighborhood of the original base point. -/
theorem periodStalkClass_eventually_dbar_zero (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (ha : periodStalkClass P b a = 0) :
    ∀ᶠ b' in 𝓝 b, MarkedLinear.dbarLinear (P.point b') (fun j => a j b') = 0 := by
  obtain ⟨U, hbU, hU⟩ :=
    (GlobalRestriction.globalStalkClass_eq_zero_iff (Zero.projectionMap P)
      (Zero.totalAdditiveSheaf P) b 1 (Cocycle.periodClass P a)).mp ha
  filter_upwards [U.isOpen.mem_nhds hbU] with b' hb'
  exact dbar_eq_zero_of_neighborhood_period_zero P a U hU b' hb'

/-- Equivalently, the original holomorphic period reduction vanishes
near the base point whenever the actual period-class germ vanishes. -/
theorem periodStalkClass_eventually_reduction_zero (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (ha : periodStalkClass P b a = 0) :
    ∀ᶠ b' in 𝓝 b, MarkedLinear.reduction (P.point b') (fun j => a j b') = 0 := by
  filter_upwards [periodStalkClass_eventually_dbar_zero P b a ha] with b' hb'
  apply (MarkedLinear.firstDbarEquiv (P.point b')).injective
  exact (MarkedLinear.dbarLinear_eq_firstDbar_reduction (P.point b') (fun j => a j b')).symm.trans
    (hb'.trans (map_zero (MarkedLinear.firstDbarEquiv (P.point b'))).symm)

/-- Nonvanishing of the actual reduction as a germ proves nonvanishing
in the original higher-direct-image stalk. -/
theorem periodStalkClass_ne_zero_of_reduction (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B)
    (ha : ¬ ∀ᶠ b' in 𝓝 b, MarkedLinear.reduction (P.point b') (fun j => a j b') = 0) :
    periodStalkClass P b a ≠ 0 :=
  fun h => ha (periodStalkClass_eventually_reduction_zero P b a h)

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage
