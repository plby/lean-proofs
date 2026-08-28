import Wikipedia.HopfProblem.SixSphereCubeInteriorInterval
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# The original cube interior and Euclidean space

The complement of the native cube boundary consists exactly of the points
whose coordinates belong to `(0,1)`.  Coordinatewise interval homeomorphisms
identify this original subtype with Euclidean space in the same dimension.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixSphereCube

/-- The complement of the native boundary in the original finite cube. -/
abbrev CubeInteriorN (n : ℕ) := {u : Fin n → I // u ∉ Cube.boundary (Fin n)}

theorem not_mem_cubeBoundary_iff {n : ℕ} (u : Fin n → I) :
    u ∉ Cube.boundary (Fin n) ↔ ∀ i, 0 < (u i : ℝ) ∧ (u i : ℝ) < 1 := by
  simp only [Cube.boundary, Set.mem_ofPred_eq, not_exists, not_or,
    unitInterval.coe_pos, unitInterval.coe_lt_one,
    unitInterval.pos_iff_ne_zero, unitInterval.lt_one_iff_ne_one]

theorem cubeBoundary_eq_iUnion (n : ℕ) :
    Cube.boundary (Fin n) =
      ⋃ i : Fin n, {u : Fin n → I | u i = 0} ∪ {u : Fin n → I | u i = 1} := by
  ext u
  simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union]

theorem isClosed_cubeBoundaryN (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  rw [cubeBoundary_eq_iUnion]
  exact isClosed_iUnion_of_finite fun i =>
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const)

theorem isOpen_cubeInteriorN (n : ℕ) :
    IsOpen {u : Fin n → I | u ∉ Cube.boundary (Fin n)} :=
  (isClosed_cubeBoundaryN n).isOpen_compl

/-- Coordinatewise inclusion identifies the original interior with a product
of ordinary open intervals; neither the cube nor its boundary is replaced. -/
def cubeInteriorCoordinates (n : ℕ) : CubeInteriorN n ≃ₜ (Fin n → OpenUnitInterval) where
  toFun u i := ⟨(u.val i : ℝ), (not_mem_cubeBoundary_iff u.val).mp u.property i⟩
  invFun v := ⟨fun i => ⟨(v i : ℝ), ⟨(v i).property.1.le, (v i).property.2.le⟩⟩,
    (not_mem_cubeBoundary_iff _).mpr fun i => (v i).property⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    exact Subtype.ext rfl
  right_inv v := by
    funext i
    exact Subtype.ext rfl
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    have hi : Continuous (fun u : CubeInteriorN n => u.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact (continuous_subtype_val.comp hi).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i => ?_
    have hi : Continuous (fun v : Fin n → OpenUnitInterval => v i) :=
      continuous_apply i
    exact (continuous_subtype_val.comp hi).subtype_mk _

@[simp] theorem cubeInteriorCoordinates_apply (n : ℕ) (u : CubeInteriorN n) (i : Fin n) :
    (cubeInteriorCoordinates n u i : ℝ) = (u.val i : ℝ) := rfl

@[simp] theorem cubeInteriorCoordinates_symm_apply (n : ℕ)
    (v : Fin n → OpenUnitInterval) (i : Fin n) :
    (((cubeInteriorCoordinates n).symm v).val i : ℝ) = (v i : ℝ) := rfl

/-- The genuine finite-cube interior homeomorphism, with the original indexing. -/
def cubeInteriorEuclideanHomeomorph (n : ℕ) :
    CubeInteriorN n ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (cubeInteriorCoordinates n).trans
    ((Homeomorph.piCongrRight fun _ : Fin n => openUnitIntervalHomeomorph).trans
      (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm)

@[simp] theorem cubeInteriorEuclideanHomeomorph_apply (n : ℕ) (u : CubeInteriorN n)
    (i : Fin n) :
    cubeInteriorEuclideanHomeomorph n u i =
      openUnitIntervalHomeomorph (cubeInteriorCoordinates n u i) := rfl

@[simp] theorem cubeInteriorEuclideanHomeomorph_symm_apply (n : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (((cubeInteriorEuclideanHomeomorph n).symm v).val i : ℝ) =
      (openUnitIntervalHomeomorph.symm (v i) : ℝ) := rfl

/-- The actual boundary complement of the native six-cube. -/
abbrev CubeInterior := CubeInteriorN 6

theorem isClosed_cubeBoundary : IsClosed (Cube.boundary (Fin 6)) :=
  isClosed_cubeBoundaryN 6

theorem isOpen_cubeInterior :
    IsOpen {u : Fin 6 → I | u ∉ Cube.boundary (Fin 6)} :=
  isOpen_cubeInteriorN 6

/-- The original six-cube interior is homeomorphic to the original Euclidean six-space. -/
abbrev cubeInteriorHomeomorph : CubeInterior ≃ₜ EuclideanSpace ℝ (Fin 6) :=
  cubeInteriorEuclideanHomeomorph 6

@[simp] theorem zero_mem_cubeBoundary :
    (0 : Fin 6 → I) ∈ Cube.boundary (Fin 6) :=
  ⟨0, Or.inl rfl⟩

theorem cubeBoundary_nonempty : (Cube.boundary (Fin 6)).Nonempty :=
  ⟨0, zero_mem_cubeBoundary⟩

end Wikipedia.HopfProblem.SixSphereCube
