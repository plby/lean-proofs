import Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-! # Compactification retaining the actual centered stereographic coordinates -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def compactification (z : UnitSphere E) : OnePoint (Tangent z) ≃ₜ UnitSphere E :=
  onePointHyperplaneHomeoUnitSphere (by simp : ‖-z.val‖ = 1)

theorem compactification_coe (z : UnitSphere E) (v : Tangent z) :
    compactification z (v : OnePoint (Tangent z)) = inverse z v := rfl

theorem compactification_zero (z : UnitSphere E) :
    compactification z ((0 : Tangent z) : OnePoint (Tangent z)) = z := by
  rw [compactification_coe, inverse_zero]

theorem compactification_symm_of_mem (z w : UnitSphere E) (hw : w ∈ (chart z).source) :
    (compactification z).symm w = (chart z w : OnePoint (Tangent z)) := by
  apply (compactification z).injective
  rw [Homeomorph.apply_symm_apply, compactification_coe]
  exact ((chart z).left_inv hw).symm

theorem compactification_symm_eq_zero_iff (z w : UnitSphere E) :
    (compactification z).symm w = ((0 : Tangent z) : OnePoint (Tangent z)) ↔ w = z := by
  constructor
  · intro h
    have he := congrArg (compactification z) h
    simpa only [Homeomorph.apply_symm_apply, compactification_zero] using he
  · intro h
    subst w
    have he := (compactification z).symm_apply_apply ((0 : Tangent z) : OnePoint (Tangent z))
    simpa only [compactification_zero] using he

end Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
