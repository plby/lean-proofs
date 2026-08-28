import Wikipedia.NoExoticSixSphere.JamesSphereAttachingLoopCorrection
import Wikipedia.NoExoticSixSphere.JamesSphereFourSourceGenerator

/-!
# The corrected native seven-cube represents the actual attaching class up to sign

The identity sphere map, written using the actual smooth cube quotient,
gives an integral generator of the native seventh sphere group. This
follows from the proved based sphere/cube correspondence and cyclicity,
without an assumed orientation for the cube triangulation. Combining
it with the source-generator comparison identifies the corrected
uncurried cube with the ORIGINAL attaching class up to sign.
-/

noncomputable section

open scoped Topology
open Wikipedia.HomotopyGroupsOfSpheres

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def cubeIdentityClass : π_ 7 (Sphere 7) (spherePole 7) :=
  SmoothCube.sphereClass ⟨ContinuousMap.id _, rfl⟩

theorem cubeIdentity_map {X : Type*} [TopologicalSpace X] {x : X}
    (f : SmoothCube.BasedMap 7 X x) :
    HigherHomotopy.map (N := Fin 7) f.val f.property cubeIdentityClass =
      SmoothCube.sphereClass f := rfl

theorem cubeIdentity_generates : Function.Surjective (fun k : ℤ ↦ cubeIdentityClass ^ k) := by
  intro a
  obtain ⟨f, hf⟩ := SmoothCube.sphereClass_surjective (by decide : 0 < 7) a
  let F := HigherHomotopy.mapMonoidHom (N := Fin 7) f.val f.property
  have ha : F cubeIdentityClass = a := (cubeIdentity_map f).trans hf
  obtain ⟨k, hk⟩ := sphereSevenGenerator_generates (spherePole 7) cubeIdentityClass
  obtain ⟨j, hj⟩ := sphereSevenGenerator_generates (spherePole 7)
    (F (sphereSevenGenerator (spherePole 7)))
  refine ⟨j, ?_⟩
  calc
    cubeIdentityClass ^ j = (sphereSevenGenerator (spherePole 7) ^ k) ^ j :=
      congrArg (fun c ↦ c ^ j) hk.symm
    _ = (sphereSevenGenerator (spherePole 7) ^ j) ^ k := by
      rw [← zpow_mul, ← zpow_mul, mul_comm k j]
    _ = (F (sphereSevenGenerator (spherePole 7))) ^ k := congrArg (fun c ↦ c ^ k) hj
    _ = F (sphereSevenGenerator (spherePole 7) ^ k) := (map_zpow F _ k).symm
    _ = F cubeIdentityClass := congrArg F hk
    _ = a := ha

def cubeIdentitySign : ℤ := (pi7_sphere_seven_mulEquiv (spherePole 7) cubeIdentityClass).toAdd

theorem cubeIdentitySign_natAbs : Int.natAbs cubeIdentitySign = 1 :=
  generating_integer_coordinate (pi7_sphere_seven_mulEquiv (spherePole 7)) _ cubeIdentity_generates

theorem cubeIdentitySign_eq_one_or_neg_one : cubeIdentitySign = 1 ∨ cubeIdentitySign = -1 :=
  Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr cubeIdentitySign_natAbs)

theorem cubeIdentity_eq_generator_power :
    cubeIdentityClass = sphereSevenGenerator (spherePole 7) ^ cubeIdentitySign := by
  apply (pi7_sphere_seven_mulEquiv (spherePole 7)).injective
  rw [map_zpow]
  change Multiplicative.ofAdd cubeIdentitySign =
    ((pi7_sphere_seven_mulEquiv (spherePole 7))
      ((pi7_sphere_seven_mulEquiv (spherePole 7)).symm (Multiplicative.ofAdd 1))) ^ cubeIdentitySign
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd cubeIdentitySign = Multiplicative.ofAdd (cubeIdentitySign • (1 : ℤ))
  rw [Int.zsmul_eq_mul, mul_one]

def correctedSevenClass : π_ 7 (Sphere 4) (spherePole 4) :=
  Quotient.mk' (GeneralizedLoopCurrying.uncurry (correctedCube 3))

theorem correctedSevenClass_eq_map_identity :
    correctedSevenClass = sourceSphereAttachingHom 3 7 cubeIdentityClass := by
  change Quotient.mk' (GeneralizedLoopCurrying.uncurry (correctedCube 3)) = _
  rw [correctedCube_uncurry]
  exact (cubeIdentity_map ⟨sourceSphereAttaching 3, sourceSphereAttaching_pole 3⟩).symm

theorem correctedSevenClass_eq_power :
    correctedSevenClass = sourceFourAttachingClass ^ cubeIdentitySign := by
  rw [correctedSevenClass_eq_map_identity, cubeIdentity_eq_generator_power, map_zpow]
  rfl

theorem correctedSevenClass_eq_or_inv :
    correctedSevenClass = sourceFourAttachingClass ∨
      correctedSevenClass = sourceFourAttachingClass⁻¹ := by
  rcases cubeIdentitySign_eq_one_or_neg_one with h | h
  · left
    simpa only [h, zpow_one] using correctedSevenClass_eq_power
  · right
    simpa only [h, zpow_neg, zpow_one] using correctedSevenClass_eq_power

theorem originalAttachingClass_eq_corrected_or_inv :
    SphereFourAttaching.attachingClass = correctedSevenClass ∨
      SphereFourAttaching.attachingClass = correctedSevenClass⁻¹ := by
  rcases originalAttachingClass_eq_or_inv with h₁ | h₁ <;>
    rcases correctedSevenClass_eq_or_inv with h₂ | h₂
  · exact Or.inl (h₁.trans h₂.symm)
  · right
    rw [h₁, h₂, inv_inv]
  · right
    rw [h₁, h₂]
  · exact Or.inl (h₁.trans h₂.symm)

theorem original_integer_coordinate_natAbs
    (f : π_ 7 (Sphere 4) (spherePole 4) →* Multiplicative ℤ) :
    Int.natAbs (f SphereFourAttaching.attachingClass).toAdd =
      Int.natAbs (f correctedSevenClass).toAdd := by
  rcases originalAttachingClass_eq_corrected_or_inv with h | h
  · rw [h]
  · rw [h, map_inv]
    exact Int.natAbs_neg _

end NoExoticSixSphere.JamesSphere.AttachingSquare
