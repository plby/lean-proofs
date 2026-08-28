import Wikipedia.NoExoticSixSphere.JamesSphereAttachingTailFaces
import Wikipedia.NoExoticSixSphere.CubeCollar

/-!
# The full original attaching boundary in clock-and-tail coordinates

Splitting off the leading coordinate of each original block is a
homeomorphism of actual cubes. The full boundary is exactly the union
of the clock-perimeter and tail-boundary faces. Affine unscaling gives
a homeomorphism onto the ORIGINAL characteristic boundary, extending
both previously constructed face parametrizations literally.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval
open Wikipedia.HopfProblem.DegreeCollapse

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def cubeCoordinates (n : ℕ) :
    ((Fin 2 → I) × Parameter n) ≃ₜ (Fin (2 * (n + 1)) → I) where
  toFun := packedCube n
  invFun u := (fun i ↦ JamesCellCube.block (n + 1) 2 u i 0,
    fun i ↦ Fin.tail (JamesCellCube.block (n + 1) 2 u i))
  left_inv p := by
    apply Prod.ext
    · funext i
      change JamesCellCube.block (n + 1) 2
        (JamesCellCube.pack (n + 1) 2 (fun j ↦ Fin.cons (p.1 j) (p.2 j))) i 0 = p.1 i
      rw [JamesCellCube.block_pack]
      rfl
    · funext i j
      change JamesCellCube.block (n + 1) 2
        (JamesCellCube.pack (n + 1) 2 (fun k ↦ Fin.cons (p.1 k) (p.2 k))) i j.succ = p.2 i j
      rw [JamesCellCube.block_pack]
      rfl
  right_inv u := by
    change JamesCellCube.pack (n + 1) 2 (fun i ↦
      Fin.cons (JamesCellCube.block (n + 1) 2 u i 0)
        (Fin.tail (JamesCellCube.block (n + 1) 2 u i))) = u
    simp only [Fin.cons_self_tail, JamesCellCube.pack_block]
  continuous_toFun := (packedCube n).continuous
  continuous_invFun := (continuous_pi (fun _ ↦ continuous_apply _)).prodMk
    (continuous_pi (fun _ ↦ continuous_pi (fun _ ↦ continuous_apply _)))

def fullBoundary (n : ℕ) : Set ((Fin 2 → I) × Parameter n) :=
  {p | p.1 ∈ Cube.boundary (Fin 2) ∨ ∃ i, p.2 i ∈ Cube.boundary (Fin n)}

theorem packedCube_mem_boundary_iff (n : ℕ) (p : (Fin 2 → I) × Parameter n) :
    packedCube n p ∈ Cube.boundary (Fin (2 * (n + 1))) ↔ p ∈ fullBoundary n := by
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective l
    change JamesCellCube.block (n + 1) 2
      (JamesCellCube.pack (n + 1) 2 (fun k ↦ Fin.cons (p.1 k) (p.2 k))) i j = 0 ∨
        JamesCellCube.block (n + 1) 2
          (JamesCellCube.pack (n + 1) 2 (fun k ↦ Fin.cons (p.1 k) (p.2 k))) i j = 1 at hl
    rw [JamesCellCube.block_pack] at hl
    cases j using Fin.cases with
    | zero => exact Or.inl ⟨i, hl⟩
    | succ j => exact Or.inr ⟨i, j, hl⟩
  · rintro (hp | hp)
    · exact packedCube_boundary n ⟨p.1, hp⟩ p.2
    · exact packedCube_tail_boundary n ⟨p, hp⟩

theorem isClosed_fullBoundary (n : ℕ) : IsClosed (fullBoundary n) := by
  have he : fullBoundary n = (packedCube n) ⁻¹' Cube.boundary (Fin (2 * (n + 1))) := by
    ext p
    exact (packedCube_mem_boundary_iff n p).symm
  rw [he]
  exact (CubeCollar.isClosed_boundary _).preimage (packedCube n).continuous

instance (n : ℕ) : CompactSpace (fullBoundary n) :=
  isCompact_iff_compactSpace.mp (isClosed_fullBoundary n).isCompact

theorem cube_mem_boundary_of_mem_sphere (m : ℕ) (s : sphere (0 : Fin m → ℝ) 1) :
    JamesCellCube.cube m s.val ∈ Cube.boundary (Fin m) := by
  by_contra hn
  have h := (JamesCellCube.cube_not_boundary_iff m s.val).mp hn
  exact (not_lt_of_ge (mem_sphere.mp s.property).ge) h

def fullBoundaryHomeomorph (n : ℕ) : fullBoundary n ≃ₜ CellBoundary.Boundary (n + 1) where
  toFun p := ⟨JamesCellCube.unscale _ (packedCube n p.val),
    unscale_boundary _ _ ((packedCube_mem_boundary_iff n p.val).mpr p.property)⟩
  invFun s := ⟨(cubeCoordinates n).symm (JamesCellCube.cube _ s.val), by
    apply (packedCube_mem_boundary_iff n _).mp
    change cubeCoordinates n ((cubeCoordinates n).symm (JamesCellCube.cube _ s.val)) ∈ _
    rw [Homeomorph.apply_symm_apply]
    exact cube_mem_boundary_of_mem_sphere _ s⟩
  left_inv p := by
    apply Subtype.ext
    change (cubeCoordinates n).symm
      (JamesCellCube.cube _ (JamesCellCube.unscale _ (cubeCoordinates n p.val))) = p.val
    rw [JamesCellCube.cube_unscale, Homeomorph.symm_apply_apply]
  right_inv s := by
    apply Subtype.ext
    change JamesCellCube.unscale _ (cubeCoordinates n
      ((cubeCoordinates n).symm (JamesCellCube.cube _ s.val))) = s.val
    rw [Homeomorph.apply_symm_apply]
    exact JamesCellCube.unscale_cube_of_mem_closedBall _ (sphere_subset_closedBall s.property)
  continuous_toFun := ((JamesCellCube.continuous_unscale _).comp
    ((packedCube n).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((cubeCoordinates n).symm.continuous.comp
    ((JamesCellCube.continuous_cube _).comp continuous_subtype_val)).subtype_mk _

theorem fullBoundaryHomeomorph_clock (n : ℕ) (t : ClockBoundary) (v : Parameter n) :
    fullBoundaryHomeomorph n ⟨(t.val, v), Or.inl t.property⟩ = boundaryMap n (t, v) := rfl

theorem fullBoundaryHomeomorph_tail (n : ℕ) (p : TailFaces n) :
    fullBoundaryHomeomorph n ⟨p.val, Or.inr p.property⟩ = tailBoundaryMap n p := rfl

def fullAttaching (n : ℕ) : C(fullBoundary n, Sphere (n + 1)) :=
  (CellBoundary.attaching (n + 1)).comp (fullBoundaryHomeomorph n : C(_, _))

end NoExoticSixSphere.JamesSphere.AttachingSquare
