import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsVerticalDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationCritical

/-!
# The three actual zeros of the descended tangent field

The previously proved cubic, quartic, and normal-crossing local
projection equations supply genuine critical points over zero, one,
and infinity. Their actual projection differentials vanish. Thus the
holomorphic field constructed by descent vanishes at all three points.
-/

noncomputable section

open Set
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- Vanishing is forced by an actual critical point in the fibre. -/
theorem descendedField_eq_zero_of_criticalValue (v : Field) {b : RiemannSphere}
    (hb : b ∈ FibreClassification.criticalValues) : descendedField v b = 0 := by
  obtain ⟨x, hx, rfl⟩ := hb
  rw [descendedField_projection, (FibreClassification.mfderiv_eq_zero_iff_critical x).mpr hx]
  rfl

theorem descendedField_zero (v : Field) :
    descendedField v ((0 : ℂ) : RiemannSphere) = 0 :=
  descendedField_eq_zero_of_criticalValue v FibreClassification.zero_mem_criticalValues

theorem descendedField_one (v : Field) :
    descendedField v ((1 : ℂ) : RiemannSphere) = 0 :=
  descendedField_eq_zero_of_criticalValue v FibreClassification.one_mem_criticalValues

theorem descendedField_infty (v : Field) : descendedField v (∞ : RiemannSphere) = 0 :=
  descendedField_eq_zero_of_criticalValue v FibreClassification.infty_mem_criticalValues

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields
