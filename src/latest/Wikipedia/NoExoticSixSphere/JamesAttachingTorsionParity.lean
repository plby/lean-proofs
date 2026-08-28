import Wikipedia.NoExoticSixSphere.JamesAttachingQuaternionClass
import Wikipedia.NoExoticSixSphere.JamesQuaternionRetractionParity

/-!
# The original attaching torsion coordinate has odd parity

The actual retracted attaching class is the nonsquare quaternionic
Samelson class or its inverse. The previously proved retraction/parity
criterion therefore determines the parity of the ORIGINAL attaching
relation, independently of the choice of Hopf-coordinate lift.
-/

noncomputable section

open scoped Topology
open Wikipedia.HomotopyGroupsOfSpheres

namespace NoExoticSixSphere.JamesSphere.ThreeRetraction

theorem originalAttaching_retraction_not_square
    (a : π_ 6 (Sphere 3) (spherePole 3)) :
    a ^ 2 ≠ sectionHom 6 SphereFourAttaching.attachingClass := by
  intro ha
  rcases originalAttaching_retraction_eq_nu_or_inv with h | h
  · have hq := congrArg quaternionSphereEquiv.symm (ha.trans h)
    rw [map_pow, MulEquiv.symm_apply_apply] at hq
    exact QuaternionSamelsonOrder.square_ne_nu _ hq
  · have hq := congrArg quaternionSphereEquiv.symm (ha.trans h)
    rw [map_pow, map_inv, MulEquiv.symm_apply_apply] at hq
    apply QuaternionSamelsonOrder.square_ne_nu (quaternionSphereEquiv.symm a)⁻¹
    rw [inv_pow, hq, inv_inv]

end NoExoticSixSphere.JamesSphere.ThreeRetraction

namespace NoExoticSixSphere.SphereFiveEighth

theorem torsionParity_ne_zero : torsionParity ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := JamesSphere.ThreeRetraction.originalAttaching_square_iff_parity.mpr h
  exact JamesSphere.ThreeRetraction.originalAttaching_retraction_not_square a ha

theorem torsionParity_eq_one : torsionParity = 1 := by
  have hb (b : ZMod 2) : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact (hb torsionParity).resolve_left torsionParity_ne_zero

theorem integerLift_twelfth_power_ne_one : integerLift ^ 12 ≠ 1 :=
  fun h ↦ torsionParity_ne_zero (integerLift_twelfth_power_iff_parity.mp h)

end NoExoticSixSphere.SphereFiveEighth

namespace NoExoticSixSphere.StableThirdAttaching

theorem integerLift_twelfth_power_ne_one (k : ℕ) : integerLift k ^ 12 ≠ 1 :=
  fun h ↦ SphereFiveEighth.torsionParity_ne_zero
    ((integerLift_twelfth_power_iff_parity k).mp h)

end NoExoticSixSphere.StableThirdAttaching
