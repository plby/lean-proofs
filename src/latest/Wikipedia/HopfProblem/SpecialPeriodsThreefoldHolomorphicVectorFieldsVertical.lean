import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsVerticalCritical
import Wikipedia.HopfProblem.RiemannSphereHolomorphicVectorFields

/-!
# Every global holomorphic vector field is vertical

For the actual unconditional compact threefold, the native differential
of its sphere projection annihilates every holomorphic tangent section.
The proof constructs the descended holomorphic sphere field using actual
function descent, obtains its three zeros from the proved singular-fibre
models, and applies the native three-zero theorem on the sphere.

This proves the verticality assertion in the proof of Proposition 9.23.
It does not assume or assert an automorphism-group classification.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

theorem descendedField_eq_zero (v : Field) : descendedField v = 0 :=
  RiemannSphere.HolomorphicVectorFields.eq_zero_of_three_zeros (descendedField v)
    (descendedField_zero v) (descendedField_one v) (descendedField_infty v)

/-- Verticality is defined using the genuine projection differential. -/
def IsVertical (v : Field) : Prop :=
  ∀ x : Threefold.Space, mfderiv IF 𝓘(ℂ) Threefold.projectionSphere x (v x) = 0

/-- Every genuine global holomorphic field on the constructed threefold
is killed by the actual differential of the sphere projection. -/
theorem projection_mfderiv_apply_eq_zero (v : Field) (x : Threefold.Space) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere x (v x) = 0 := by
  rw [← descendedField_projection, descendedField_eq_zero]
  rfl

theorem every_field_vertical (v : Field) : IsVertical v :=
  projection_mfderiv_apply_eq_zero v

/-- Pointwise, every holomorphic field lies in the native vertical tangent kernel. -/
theorem field_mem_projection_ker (v : Field) (x : Threefold.Space) :
    v x ∈ (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere x).ker :=
  projection_mfderiv_apply_eq_zero v x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields
