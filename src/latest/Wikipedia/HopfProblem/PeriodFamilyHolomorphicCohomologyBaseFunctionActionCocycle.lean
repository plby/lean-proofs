import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyBaseFunctionActionBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleClass

/-!
# Period classes respect actual holomorphic base multiplication

Both original local quotient lifts have the original base coordinate.
Consequently a holomorphic multiplier of the period coefficients gives
the literal coefficient-sheaf map of the original overlap cocycle.
Naturality of its actual extension class proves the corresponding
identity in native sheaf cohomology.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.BaseFunctionAction

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- Base multiplication factors out of the literal real-period-coordinate primitive. -/
theorem primitive_mul_base (P : HolomorphicPeriodMap V B) (g : BaseFunction V B)
    (a : Cocycle.Coefficients V B) (x : B × ComplexPlane₂) :
    Cocycle.primitive P (fun j => g * a j) x = g x.1 * Cocycle.primitive P a x := by
  simp [Cocycle.primitive, mul_assoc, Finset.mul_sum]

/-- On an actual overlap, both original lifts have the original base value. -/
theorem difference_mul_base (P : HolomorphicPeriodMap V B) (g : BaseFunction V B)
    (a : Cocycle.Coefficients V B) (i j : B × ComplexPlane₂) {x : P.TotalSpace}
    (hx : x ∈ Cocycle.coverOpen P i ⊓ Cocycle.coverOpen P j) :
    Cocycle.difference P (fun k => g * a k) i j x =
      g (P.projection x) * Cocycle.difference P a i j x := by
  simp only [Cocycle.difference, primitive_mul_base,
    Cocycle.lift_base P i hx.1, Cocycle.lift_base P j hx.2, mul_sub]

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original holomorphic cocycle changes by the actual base multiplier
on its original coefficient sheaf, not by a chosen cohomology action. -/
theorem cocycle_mul_base (P : HolomorphicPeriodMap V B) (g : BaseFunction V B)
    (a : Cocycle.Coefficients V B) :
    Cocycle.cocycle P (fun j => g * a j) =
      HolomorphicPicard.Cech.mapCocycle (baseMultiplyEnd P g) (Cocycle.cocycle P a) := by
  let := P.totalChartedSpace
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  apply ContMDiffMap.ext
  intro x
  exact difference_mul_base P g a i j x.property

/-- Holomorphic multiplication of coefficients is exactly the genuine map
of the original multiplier endomorphism on native first cohomology. -/
theorem periodClass_mul_base (P : HolomorphicPeriodMap V B) (g : BaseFunction V B)
    (a : Cocycle.Coefficients V B) :
    Cocycle.periodClass P (fun j => g * a j) =
      CategoryTheory.Sheaf.H.map (baseMultiplyEnd P g) 1 (Cocycle.periodClass P a) := by
  exact (congrArg
    (fun c => HolomorphicPicard.CechExtension.classOf c (Cocycle.coverOpen_covers P))
    (cocycle_mul_base P g a)).trans
      (HolomorphicPicard.CechExtension.classOf_naturality
        (baseMultiplyEnd P g) (Cocycle.cocycle P a) (Cocycle.coverOpen_covers P)).symm

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.BaseFunctionAction
