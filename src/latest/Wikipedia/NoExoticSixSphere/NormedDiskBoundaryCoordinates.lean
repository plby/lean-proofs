import Wikipedia.NoExoticSixSphere.JamesCellCubeCoordinates
import Wikipedia.HopfProblem.DegreeCollapseDiskCube

/-!
# Boundary-preserving coordinates between round and max-norm disks

The max-norm disk is affinely homeomorphic to the literal unit cube.
Composing with the proved disk-cube homeomorphism gives a genuine disk
homeomorphism with its exact boundary predicate. Restriction constructs
the corresponding sphere-boundary homeomorphism without an isometry claim.
-/

noncomputable section

open Set Metric
open scoped unitInterval
open Wikipedia.HopfProblem.DegreeCollapse

namespace NoExoticSixSphere.NormedDiskBoundaryCoordinates

def cubeHomeomorph (m : ℕ) : DiskCylinder.Disk (E := Fin m → ℝ) ≃ₜ (Fin m → unitInterval) where
  toFun x := JamesCellCube.cube m x.val
  invFun u := ⟨JamesCellCube.unscale m u, JamesCellCube.unscale_mem_closedBall m u⟩
  left_inv x := Subtype.ext (JamesCellCube.unscale_cube_of_mem_closedBall m x.property)
  right_inv u := JamesCellCube.cube_unscale m u
  continuous_toFun := (JamesCellCube.continuous_cube m).comp continuous_subtype_val
  continuous_invFun := (JamesCellCube.continuous_unscale m).subtype_mk _

theorem cubeHomeomorph_boundary (m : ℕ) (x : DiskCylinder.Disk (E := Fin m → ℝ)) :
    cubeHomeomorph m x ∈ Cube.boundary (Fin m) ↔ x.val ∈ sphere (0 : Fin m → ℝ) 1 := by
  constructor
  · intro hx
    have hnot : x.val ∉ ball (0 : Fin m → ℝ) 1 := by
      intro h
      exact (JamesCellCube.cube_not_boundary_iff m x.val).mpr h hx
    exact mem_sphere.mpr (le_antisymm (mem_closedBall.mp x.property) (le_of_not_gt hnot))
  · intro hx
    by_contra h
    have hball := (JamesCellCube.cube_not_boundary_iff m x.val).mp h
    exact (not_lt_of_ge (mem_sphere.mp hx).ge) hball

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def boundaryHomeomorph (e : DiskCylinder.Disk (E := E) ≃ₜ DiskCylinder.Disk (E := F))
    (he : ∀ x, (e x).val ∈ sphere (0 : F) 1 ↔ x.val ∈ sphere (0 : E) 1) :
    DiskCylinder.Sphere (E := E) ≃ₜ DiskCylinder.Sphere (E := F) where
  toFun s := ⟨(e (DiskCylinder.boundaryToDisk s)).val, (he _).mpr s.property⟩
  invFun s := ⟨(e.symm (DiskCylinder.boundaryToDisk s)).val, (he _).mp (by
    rw [Homeomorph.apply_symm_apply]
    exact s.property)⟩
  left_inv s := by
    apply Subtype.ext
    change (e.symm (e (DiskCylinder.boundaryToDisk s))).val = s.val
    rw [Homeomorph.symm_apply_apply]
    rfl
  right_inv s := by
    apply Subtype.ext
    change (e (e.symm (DiskCylinder.boundaryToDisk s))).val = s.val
    rw [Homeomorph.apply_symm_apply]
    rfl
  continuous_toFun :=
    (continuous_subtype_val.comp
      (e.continuous.comp DiskCylinder.boundaryToDisk.continuous)).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp
    (e.symm.continuous.comp DiskCylinder.boundaryToDisk.continuous)).subtype_mk _

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem boundaryHomeomorph_disk
    (e : DiskCylinder.Disk (E := E) ≃ₜ DiskCylinder.Disk (E := F))
    (he : ∀ x, (e x).val ∈ sphere (0 : F) 1 ↔ x.val ∈ sphere (0 : E) 1)
    (s : DiskCylinder.Sphere (E := E)) :
    DiskCylinder.boundaryToDisk (boundaryHomeomorph e he s) = e (DiskCylinder.boundaryToDisk s) :=
  rfl

variable [FiniteDimensional ℝ E] {m : ℕ} (L : E ≃L[ℝ] (Fin m → ℝ))

def diskHomeomorph : DiskCylinder.Disk (E := E) ≃ₜ DiskCylinder.Disk (E := Fin m → ℝ) :=
  (DiskCube.homeomorph L).trans (cubeHomeomorph m).symm

theorem diskHomeomorph_boundary (x : DiskCylinder.Disk (E := E)) :
    (diskHomeomorph L x).val ∈ sphere (0 : Fin m → ℝ) 1 ↔ x.val ∈ sphere (0 : E) 1 := by
  rw [← cubeHomeomorph_boundary]
  change cubeHomeomorph m ((cubeHomeomorph m).symm (DiskCube.homeomorph L x)) ∈
    Cube.boundary (Fin m) ↔ _
  rw [Homeomorph.apply_symm_apply, DiskCube.boundary_iff, mem_sphere_zero_iff_norm]

end NoExoticSixSphere.NormedDiskBoundaryCoordinates
