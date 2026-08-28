import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingFamily
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearReduction

/-!
# Actual fibre restrictions detect the first two period coefficient functions

A zero genuine global period-character class has zero coordinates on
every original fibre. The unchanged negative Čech marking and the proved
invertibility of the first-two-period Dolbeault map therefore detect both
holomorphic coefficient functions. No generation theorem is used.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassInjectivity

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- Zero in the original global Ext group restricts to zero under the
actual native fibre comparison, with the original negative Čech sign. -/
theorem dbarLinear_eq_zero_of_periodClass_eq_zero (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) (ha : Cocycle.periodClass P a = 0) (b : B) :
    MarkedLinear.dbarLinear (P.point b) (fun j => a j b) = 0 := by
  have h := CechConnecting.periodClass_fibre_coordinates P b a
  rw [ha, map_zero, map_zero, map_zero] at h
  exact neg_eq_zero.mp h.symm

/-- The actual holomorphic period reduction vanishes pointwise when its
genuine original global extension class vanishes. -/
theorem reduction_eq_zero_of_periodClass_eq_zero (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) (ha : Cocycle.periodClass P a = 0) (b : B) :
    MarkedLinear.reduction (P.point b) (fun j => a j b) = 0 := by
  apply (MarkedLinear.firstDbarEquiv (P.point b)).injective
  rw [map_zero, ← MarkedLinear.dbarLinear_eq_firstDbar_reduction]
  exact dbarLinear_eq_zero_of_periodClass_eq_zero P a ha b

omit [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B] in
/-- Evaluation of the first-two-function insertion is the original
pointwise first-two-period insertion, without changing the fibre marking. -/
theorem first_two_values (a : Cocycle.LinearCoefficients V B) (b : B) :
    (fun j => (![a 0, a 1, 0, 0] : Cocycle.Coefficients V B) j b) =
      MarkedLinear.firstCoefficients (fun j => a j b) := by
  funext j
  fin_cases j <;> rfl

/-- The actual first two global period classes have no nonzero
holomorphic coefficient relation. -/
theorem first_two_periodClass_eq_zero_iff (P : HolomorphicPeriodMap V B)
    (a : Cocycle.LinearCoefficients V B) :
    Cocycle.periodClass P ![a 0, a 1, 0, 0] = 0 ↔ a = 0 := by
  constructor
  · intro ha
    funext j
    apply ContMDiffMap.ext
    intro b
    have hd := dbarLinear_eq_zero_of_periodClass_eq_zero P
      (![a 0, a 1, 0, 0] : Cocycle.Coefficients V B) ha b
    rw [first_two_values] at hd
    have hv : (fun k => a k b) = (0 : Fin 2 → ℂ) :=
      (MarkedLinear.firstDbarEquiv (P.point b)).injective
        (hd.trans (map_zero (MarkedLinear.firstDbarEquiv (P.point b))).symm)
    exact congrFun hv j
  · rintro rfl
    have hz : (![(0 : Cocycle.LinearCoefficients V B) 0, 0, 0, 0] :
        Cocycle.Coefficients V B) = 0 := by
      funext j
      fin_cases j <;> rfl
    exact (congrArg (Cocycle.periodClass P) hz).trans (Cocycle.periodClass_zero P)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassInjectivity
