import Wikipedia.NoExoticSixSphere.StableThirdParityCriterion
import Wikipedia.NoExoticSixSphere.QuaternionSamelsonOrder

/-!
# Original attaching parity through the actual quaternion James retraction

The quaternion multiplication retraction is a left inverse of the
original suspension. In the existing split coordinates it differs
from the torsion projection by a multiple of the integer coordinate.
That coordinate is plus or minus two on the original attaching class,
so its parity is exactly the parity of the actual retracted class.
The value of that retracted class is not asserted here.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.ThreeRetraction

open Wikipedia.HomotopyGroupsOfSpheres
open SphereFiveEighth

def residueRetraction : π_ 7 (Sphere 4) (spherePole 4) →* Multiplicative (ZMod 12) :=
  (pi6_sphere_three_mulEquiv (spherePole 3)).toMonoidHom.comp (sectionHom 6)

theorem residueRetraction_suspension (a : π_ 6 (Sphere 3) (spherePole 3)) :
    residueRetraction (SphereFourSeventh.suspension a) =
      pi6_sphere_three_mulEquiv (spherePole 3) a := by
  change pi6_sphere_three_mulEquiv (spherePole 3)
    (sectionHom 6 (CubicalSphereSuspension.hom 6 3 a)) = _
  rw [sectionHom_suspension]

def coordinateRetraction : Coordinates →* Multiplicative (ZMod 12) :=
  residueRetraction.comp SphereFourSeventh.groupEquiv.symm.toMonoidHom

theorem coordinateRetraction_torsion (b : Multiplicative (ZMod 12)) :
    coordinateRetraction (1, b) = b := by
  let a := (pi6_sphere_three_mulEquiv (spherePole 3)).symm b
  have ha : SphereFourSeventh.groupEquiv (SphereFourSeventh.suspension a) = (1, b) :=
    (SphereFourSeventh.groupEquiv_suspension a).trans
      (congrArg (fun t ↦ ((1 : Multiplicative ℤ), t))
        ((pi6_sphere_three_mulEquiv (spherePole 3)).apply_symm_apply b))
  change residueRetraction (SphereFourSeventh.groupEquiv.symm (1, b)) = b
  rw [← ha, MulEquiv.symm_apply_apply, residueRetraction_suspension]
  exact (pi6_sphere_three_mulEquiv (spherePole 3)).apply_symm_apply b

theorem coordinateRetraction_split (x : Coordinates) :
    coordinateRetraction x =
      coordinateRetraction (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd * x.2 := by
  have hx : x = (x.1, 1) * (1, x.2) := by simp
  have hk : (x.1, (1 : Multiplicative (ZMod 12))) =
      (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd := by
    apply Prod.ext
    · change x.1 = Multiplicative.ofAdd (x.1.toAdd • (1 : ℤ))
      rw [Int.zsmul_eq_mul, mul_one]
      rfl
    · exact (one_zpow _).symm
  calc
    coordinateRetraction x = coordinateRetraction ((x.1, 1) * (1, x.2)) :=
      congrArg coordinateRetraction hx
    _ = coordinateRetraction (x.1, 1) * coordinateRetraction (1, x.2) := map_mul _ _ _
    _ = coordinateRetraction (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd * x.2 := by
      rw [hk, map_zpow, coordinateRetraction_torsion]

theorem coordinateRetraction_parity (x : Coordinates) :
    residueParity (coordinateRetraction x).toAdd =
      x.1.toAdd • residueParity (coordinateRetraction (Multiplicative.ofAdd 1, 1)).toAdd +
        residueParity x.2.toAdd := by
  rw [coordinateRetraction_split]
  change residueParity (x.1.toAdd •
    (coordinateRetraction (Multiplicative.ofAdd 1, 1)).toAdd + x.2.toAdd) = _
  rw [map_add, map_zsmul]

theorem coordinateRetraction_relation :
    coordinateRetraction relation = residueRetraction SphereFourAttaching.attachingClass := by
  change residueRetraction (SphereFourSeventh.groupEquiv.symm
    (SphereFourSeventh.groupEquiv SphereFourAttaching.attachingClass)) = _
  rw [MulEquiv.symm_apply_apply]

theorem originalAttaching_parity :
    residueParity (residueRetraction SphereFourAttaching.attachingClass).toAdd = torsionParity := by
  rw [← coordinateRetraction_relation, coordinateRetraction_parity]
  rcases Int.natAbs_eq_iff.mp AttachingSquare.originalAttachingClass_hopf_natAbs_two with h | h
  · rw [h]
    simp [zsmul_eq_mul, torsionParity, show (2 : ZMod 2) = 0 from by decide]
  · rw [h]
    simp [zsmul_eq_mul, torsionParity, show (2 : ZMod 2) = 0 from by decide]

theorem residue_double_iff_parity (b : ZMod 12) :
    (∃ a : ZMod 12, (2 : ℕ) • a = b) ↔ residueParity b = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [map_nsmul, nsmul_eq_mul]
    simp [show (2 : ZMod 2) = 0 from by decide]
  · intro h
    fin_cases b <;> first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩
    | exact ⟨5, rfl⟩
    | exfalso; revert h; decide

theorem native_square_iff_parity (c : π_ 6 (Sphere 3) (spherePole 3)) :
    (∃ a : π_ 6 (Sphere 3) (spherePole 3), a ^ 2 = c) ↔
      residueParity (pi6_sphere_three_mulEquiv (spherePole 3) c).toAdd = 0 := by
  rw [← residue_double_iff_parity]
  let e := pi6_sphere_three_mulEquiv (spherePole 3)
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(e a).toAdd, ?_⟩
    have h := congrArg (fun v ↦ (e v).toAdd) ha
    rw [map_pow] at h
    exact h
  · rintro ⟨b, hb⟩
    refine ⟨e.symm (Multiplicative.ofAdd b), e.injective ?_⟩
    rw [map_pow, MulEquiv.apply_symm_apply]
    exact congrArg Multiplicative.ofAdd hb

theorem originalAttaching_square_iff_parity :
    (∃ a : π_ 6 (Sphere 3) (spherePole 3),
      a ^ 2 = sectionHom 6 SphereFourAttaching.attachingClass) ↔ torsionParity = 0 := by
  rw [native_square_iff_parity]
  change residueParity (residueRetraction SphereFourAttaching.attachingClass).toAdd = 0 ↔ _
  rw [originalAttaching_parity]

end NoExoticSixSphere.JamesSphere.ThreeRetraction
