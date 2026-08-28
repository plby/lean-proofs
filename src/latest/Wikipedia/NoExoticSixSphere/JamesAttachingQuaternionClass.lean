import Wikipedia.NoExoticSixSphere.JamesAttachingQuaternionHomotopy

/-!
# The original retracted attaching class is the quaternionic Samelson class

The literal quaternion product cube has the original six-sphere pairing
coordinates, including every collapsed face. Compose the wedge-fixed
homotopy with that cube to obtain a native boundary-relative homotopy.
The resulting class is the Samelson square of the original quaternion
cube, already proved equal to the distinguished class nu. Finally the
pointed quaternion homeomorphism returns the original sphere retraction.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres

namespace NoExoticSixSphere.JamesSphere.ThreeRetraction

open AttachingSquare QuaternionCommutatorNativeSphere QuaternionCommutatorBoundaryLift

theorem quaternionParameters_cubePair (u : Fin 6 → I) :
    quaternionParameters (cubePair quaternionCube quaternionCube u) =
      sphereParameters 3 ((tailCoordinates 3).symm u) := by
  funext i
  fin_cases i
  · change sphereHomeomorph (sphereHomeomorph.symm
      (SmoothCube.quotient 3 (fun j ↦ u (blockCoordinates (Sum.inl j))))) = _
    rw [Homeomorph.apply_symm_apply]
    apply congrArg (SmoothCube.quotient 3)
    funext j
    fin_cases j <;> rfl
  · change sphereHomeomorph (sphereHomeomorph.symm
      (SmoothCube.quotient 3 (fun j ↦ u (blockCoordinates (Sum.inr j))))) = _
    rw [Homeomorph.apply_symm_apply]
    apply congrArg (SmoothCube.quotient 3)
    funext j
    fin_cases j <;> rfl

theorem quaternionPairing_cubePair (u : Fin 6 → I) :
    quaternionPairing (cubePair quaternionCube quaternionCube u) = SmoothCube.quotient 6 u := by
  change SecondStage.arrayPairing 3
    (quaternionParameters (cubePair quaternionCube quaternionCube u)) = _
  rw [quaternionParameters_cubePair, pairing_tail_cube, Homeomorph.apply_symm_apply]

def correctedQuaternionLoopHomotopy :
    (SmoothCube.toGenLoop correctedQuaternionSphere).val.HomotopyRel
      (commutatorLoop quaternionCube quaternionCube).val (Cube.boundary (Fin 6)) where
  toFun tu := correctedQuaternionCommutatorHomotopy
    (tu.1, cubePair quaternionCube quaternionCube tu.2)
  continuous_toFun := correctedQuaternionCommutatorHomotopy.continuous.comp
    (continuous_fst.prodMk
      ((cubePair quaternionCube quaternionCube).continuous.comp continuous_snd))
  map_zero_left u := by
    rw [correctedQuaternionCommutatorHomotopy.apply_zero]
    change correctedQuaternionSphere.val (quaternionPairing
      (cubePair quaternionCube quaternionCube u)) = correctedQuaternionSphere.val
        (SmoothCube.quotient 6 u)
    rw [quaternionPairing_cubePair]
  map_one_left u := correctedQuaternionCommutatorHomotopy.apply_one _
  prop' s u hu := by
    change correctedQuaternionCommutatorHomotopy
      (s, cubePair quaternionCube quaternionCube u) =
        correctedQuaternionSphere.val (SmoothCube.quotient 6 u)
    rw [correctedQuaternionCommutatorHomotopy.eq_fst s
      (cubePair_boundary quaternionCube quaternionCube u hu)]
    change correctedQuaternionSphere.val (quaternionPairing
      (cubePair quaternionCube quaternionCube u)) = correctedQuaternionSphere.val
        (SmoothCube.quotient 6 u)
    rw [quaternionPairing_cubePair]

theorem correctedQuaternionSphere_class :
    SmoothCube.sphereClass correctedQuaternionSphere = QuaternionSamelson.nu := by
  have h : SmoothCube.sphereClass correctedQuaternionSphere =
      (⟦commutatorLoop quaternionCube quaternionCube⟧ : π_ 6 UnitQuaternions 1) :=
    Quotient.sound ⟨correctedQuaternionLoopHomotopy⟩
  exact h.trans quaternionClass_pairing

def quaternionSphereEquiv : π_ 6 UnitQuaternions 1 ≃* π_ 6 (Sphere 3) (spherePole 3) :=
  pointedHomeomorphMulEquiv sphereHomeomorph 1 (spherePole 3) sphereHomeomorph_one

theorem quaternionSphereEquiv_corrected :
    quaternionSphereEquiv (SmoothCube.sphereClass correctedQuaternionSphere) =
      sectionHom 6 correctedSevenClass := by
  change pointedHomeomorphMulEquiv sphereHomeomorph 1 (spherePole 3) sphereHomeomorph_one
    (⟦SmoothCube.toGenLoop correctedQuaternionSphere⟧ : π_ 6 UnitQuaternions 1) = _
  rw [pointedHomeomorphMulEquiv_mk]
  exact correctedRepresentative_retraction_class

theorem corrected_retraction_eq_nu :
    sectionHom 6 correctedSevenClass = quaternionSphereEquiv QuaternionSamelson.nu := by
  rw [← correctedQuaternionSphere_class]
  exact quaternionSphereEquiv_corrected.symm

theorem originalAttaching_retraction_eq_nu_or_inv :
    sectionHom 6 SphereFourAttaching.attachingClass =
      quaternionSphereEquiv QuaternionSamelson.nu ∨
    sectionHom 6 SphereFourAttaching.attachingClass =
      (quaternionSphereEquiv QuaternionSamelson.nu)⁻¹ := by
  rcases originalAttachingClass_eq_corrected_or_inv with h | h
  · exact Or.inl ((congrArg (sectionHom 6) h).trans corrected_retraction_eq_nu)
  · right
    rw [h, map_inv, corrected_retraction_eq_nu]

end NoExoticSixSphere.JamesSphere.ThreeRetraction
