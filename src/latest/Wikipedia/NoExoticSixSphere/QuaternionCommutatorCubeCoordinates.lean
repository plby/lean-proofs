import Wikipedia.NoExoticSixSphere.QuaternionCommutatorBlockChart

/-!
# The exact time and three-plus-three coordinate blocks of the native seven-cube
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.QuaternionCommutatorCubeCoordinates

open GLOrthonormalization QuaternionCommutatorBoundaryLift
open QuaternionCommutatorNativeSphere CubeFirstCoordinate

def blocksLinear : Vector 7 ≃ₗ[ℝ] ℝ × (Vector 3 × Vector 3) where
  toFun x := (x 0,
    (WithLp.toLp 2 (fun i ↦ x (blockCoordinates (Sum.inl i)).succ),
      WithLp.toLp 2 (fun i ↦ x (blockCoordinates (Sum.inr i)).succ)))
  invFun z := WithLp.toLp 2 (Fin.cons z.1
    (fun i ↦ Sum.elim z.2.1 z.2.2 (blockCoordinates.symm i)))
  left_inv x := by
    apply PiLp.ext
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      obtain ⟨j, rfl⟩ := blockCoordinates.surjective i
      cases j <;> simp
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply PiLp.ext
        intro i
        change Sum.elim z.2.1 z.2.2 (blockCoordinates.symm (blockCoordinates (Sum.inl i))) = _
        rw [Equiv.symm_apply_apply]
        rfl
      · apply PiLp.ext
        intro i
        change Sum.elim z.2.1 z.2.2 (blockCoordinates.symm (blockCoordinates (Sum.inr i))) = _
        rw [Equiv.symm_apply_apply]
        rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blocks : Vector 7 ≃L[ℝ] ℝ × (Vector 3 × Vector 3) := blocksLinear.toContinuousLinearEquiv

theorem blocks_cube (u : Fin 7 → I) :
    blocks (SmoothCube.vectorOfCube 7 u) = ((split 6 u).1.val,
      (SmoothCube.vectorOfCube 3 (fun i ↦ (split 6 u).2 (blockCoordinates (Sum.inl i))),
        SmoothCube.vectorOfCube 3 (fun i ↦ (split 6 u).2 (blockCoordinates (Sum.inr i))))) := rfl

theorem blocks_left_open {x : Vector 7} (hx : x ∈ SmoothCube.openCube 7) :
    (blocks x).2.1 ∈ SmoothCube.openCube 3 := fun i ↦ hx (blockCoordinates (Sum.inl i)).succ

theorem blocks_right_open {x : Vector 7} (hx : x ∈ SmoothCube.openCube 7) :
    (blocks x).2.2 ∈ SmoothCube.openCube 3 := fun i ↦ hx (blockCoordinates (Sum.inr i)).succ

theorem blocks_antipodal :
    blocks (SmoothCube.vectorOfCube 7 antipodalSevenCube) = (1 / 2,
      (SmoothCube.vectorOfCube 3 antipodalCube, SmoothCube.vectorOfCube 3 antipodalCube)) := by
  rw [blocks_cube]
  change ((1 / 2 : ℝ),
    (SmoothCube.vectorOfCube 3 (fun i ↦ antipodalSixCube (blockCoordinates (Sum.inl i))),
      SmoothCube.vectorOfCube 3 (fun i ↦ antipodalSixCube (blockCoordinates (Sum.inr i))))) = _
  rw [antipodal_leftBlock, antipodal_rightBlock]

def timeCoordinates : ℝ ≃ₜ ℝ where
  toFun t := Real.pi / 4 - (Real.pi / 2) * t
  invFun a := (Real.pi / 4 - a) / (Real.pi / 2)
  left_inv t := by field_simp; ring
  right_inv a := by field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem timeCoordinates_half : timeCoordinates (1 / 2) = 0 := by
  change Real.pi / 4 - (Real.pi / 2) * (1 / 2) = 0
  ring

theorem angle_timeCoordinates (t : ℝ) :
    Real.pi / 4 + timeCoordinates t = (1 - t) * (Real.pi / 2) := by
  change Real.pi / 4 + (Real.pi / 4 - (Real.pi / 2) * t) = _
  ring

end NoExoticSixSphere.QuaternionCommutatorCubeCoordinates
