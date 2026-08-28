import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassInjectivityGlobal
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleVanishing

/-!
# The exact kernel of the original global period-character class map

Pointwise vanishing of the genuine fibre coordinates forces the four
holomorphic coefficient functions to be the original period values of
the holomorphic linear form given by their last two coefficients. Its
actual cocycle is already proved to be a coboundary. Thus the kernel is
identified without a generation assertion about all global cohomology.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassInjectivity

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- Evaluating the actual holomorphic linear period character gives
the original marked period-column values on each original fibre. -/
theorem linearCoefficients_values (P : HolomorphicPeriodMap V B)
    (l : Cocycle.LinearCoefficients V B) (b : B) :
    (fun j => Cocycle.linearCoefficients P l j b) =
      MarkedLinear.linearValues (P.point b) (fun k => l k b) := by
  funext j
  rw [Cocycle.linearCoefficients_apply, MarkedLinear.linearValues_apply]
  rw [show P.periodEquiv b (Pi.single j 1) = (P.point b).basis j from
    PeriodTorusTypeOneOne.periodEquiv_single (P.point b) j]

/-- Pointwise zero antiholomorphic coefficients identify the actual
four holomorphic functions with an exhibited native linear period character. -/
theorem eq_linearCoefficients_of_dbar_eq_zero (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B)
    (ha : ∀ b, MarkedLinear.dbarLinear (P.point b) (fun j => a j b) = 0) :
    a = Cocycle.linearCoefficients P ![a 2, a 3] := by
  funext j
  apply ContMDiffMap.ext
  intro b
  have hp := (MarkedLinear.dbarLinear_eq_zero_iff (P.point b) (fun j => a j b)).mp (ha b)
  have hl := linearCoefficients_values P (![a 2, a 3] : Cocycle.LinearCoefficients V B) b
  have hlast : (fun k => (![a 2, a 3] : Cocycle.LinearCoefficients V B) k b) =
      ![a 2 b, a 3 b] := by
    funext k
    fin_cases k <;> rfl
  rw [hlast] at hl
  exact (congrFun hp j).trans (congrFun hl j).symm

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- The actual global period class vanishes exactly when its literal
four coefficient functions come from the exhibited holomorphic linear form. -/
theorem periodClass_eq_zero_iff_linearCoefficients (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) :
    Cocycle.periodClass P a = 0 ↔ a = Cocycle.linearCoefficients P ![a 2, a 3] := by
  constructor
  · intro ha
    exact eq_linearCoefficients_of_dbar_eq_zero P a
      (dbarLinear_eq_zero_of_periodClass_eq_zero P a ha)
  · intro ha
    exact (congrArg (Cocycle.periodClass P) ha).trans
      (Cocycle.periodClass_linearCoefficients P ![a 2, a 3])

/-- Pointwise fibre-coordinate detection is sufficient for period classes
because the resulting original linear period character is a genuine coboundary. -/
theorem periodClass_eq_zero_iff_dbar (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) :
    Cocycle.periodClass P a = 0 ↔
      ∀ b, MarkedLinear.dbarLinear (P.point b) (fun j => a j b) = 0 := by
  constructor
  · exact dbarLinear_eq_zero_of_periodClass_eq_zero P a
  · intro ha
    exact (periodClass_eq_zero_iff_linearCoefficients P a).mpr
      (eq_linearCoefficients_of_dbar_eq_zero P a ha)

/-- The exact kernel is also expressed by the original holomorphic
two-coordinate period reduction, not by a replacement cohomology model. -/
theorem periodClass_eq_zero_iff_reduction (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) :
    Cocycle.periodClass P a = 0 ↔
      ∀ b, MarkedLinear.reduction (P.point b) (fun j => a j b) = 0 := by
  constructor
  · exact reduction_eq_zero_of_periodClass_eq_zero P a
  · intro ha
    apply (periodClass_eq_zero_iff_dbar P a).mpr
    intro b
    rw [MarkedLinear.dbarLinear_eq_firstDbar_reduction, ha b, map_zero]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassInjectivity
