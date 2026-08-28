import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometry
import Wikipedia.HopfProblem.ThirdHurewiczCubeTriangulationCoverSort

/-!
# Barycentric coordinates on the six actual cube tetrahedra

For a coordinate ordering, successive coordinate differences give the
inverse barycentric coordinates of the original affine tetrahedron. Thus
its exact range is the corresponding closed ordering region of the cube.
-/

noncomputable section

open Set
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation

open FirstHurewicz Geometry

/-- The closed cube region with the coordinate order specified by `e`. -/
def cubeOrderedRegion (e : Equiv.Perm (Fin 3)) : Set Cube3 :=
  {u | SortedCoordinates u e}

theorem continuous_cubeCoordinate (i : Fin 3) :
    Continuous (fun u : Cube3 => (u i : ℝ)) :=
  continuous_subtype_val.comp (continuous_apply i)

theorem isClosed_cubeOrderedRegion (e : Equiv.Perm (Fin 3)) :
    IsClosed (cubeOrderedRegion e) :=
  (isClosed_le (continuous_cubeCoordinate (e 2)) (continuous_cubeCoordinate (e 1))).inter
    (isClosed_le (continuous_cubeCoordinate (e 1)) (continuous_cubeCoordinate (e 0)))

/-- Successive differences of ordered cube coordinates. -/
def cubeBarycentric (e : Equiv.Perm (Fin 3)) (u : Cube3) : Fin 4 → ℝ :=
  ![1 - (u (e 0) : ℝ), (u (e 0) : ℝ) - u (e 1),
    (u (e 1) : ℝ) - u (e 2), (u (e 2) : ℝ)]

theorem cubeBarycentric_nonneg (e : Equiv.Perm (Fin 3)) (u : Cube3)
    (h : SortedCoordinates u e) (i : Fin 4) : 0 ≤ cubeBarycentric e u i := by
  fin_cases i
  · exact sub_nonneg.mpr (u (e 0)).property.2
  · exact sub_nonneg.mpr h.2
  · exact sub_nonneg.mpr h.1
  · exact (u (e 2)).property.1

theorem cubeBarycentric_sum (e : Equiv.Perm (Fin 3)) (u : Cube3) :
    ∑ i, cubeBarycentric e u i = 1 := by
  simp [cubeBarycentric, Fin.sum_univ_succ]

/-- The actual continuous inverse on the precise coordinate-order region. -/
def cubeTetrahedronInverse (e : Equiv.Perm (Fin 3)) :
    C(↥(cubeOrderedRegion e), Simplex 3) where
  toFun u := ⟨cubeBarycentric e u.val,
    ⟨cubeBarycentric_nonneg e u.val u.property, cubeBarycentric_sum e u.val⟩⟩
  continuous_toFun := by
    have hc (i : Fin 3) : Continuous (fun u : ↥(cubeOrderedRegion e) => (u.val i : ℝ)) :=
      (continuous_cubeCoordinate i).comp continuous_subtype_val
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const.sub (hc (e 0))
    · exact (hc (e 0)).sub (hc (e 1))
    · exact (hc (e 1)).sub (hc (e 2))
    · exact hc (e 2)

@[simp] theorem cubeTetrahedronInverse_coordinate (e : Equiv.Perm (Fin 3))
    (u : ↥(cubeOrderedRegion e)) (i : Fin 4) :
    cubeTetrahedronInverse e u i = cubeBarycentric e u.val i := rfl

theorem cubeTetrahedron_sorted (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    SortedCoordinates (cubeTetrahedron e s) e :=
  ⟨cubeTetrahedron_order_second e s, cubeTetrahedron_order_first e s⟩

/-- The affine cell restores every point of its order region. -/
@[simp] theorem cubeTetrahedron_inverse (e : Equiv.Perm (Fin 3))
    (u : ↥(cubeOrderedRegion e)) :
    cubeTetrahedron e (cubeTetrahedronInverse e u) = u.val := by
  funext k
  obtain ⟨j, rfl⟩ := e.surjective k
  apply Subtype.ext
  fin_cases j
  · change (cubeTetrahedron e (cubeTetrahedronInverse e u) (e 0) : ℝ) =
      (u.val (e 0) : ℝ)
    rw [cubeTetrahedron_coordinate_zero]
    change ((u.val (e 0) : ℝ) - u.val (e 1)) +
      ((u.val (e 1) : ℝ) - u.val (e 2)) + u.val (e 2) = (u.val (e 0) : ℝ)
    ring
  · change (cubeTetrahedron e (cubeTetrahedronInverse e u) (e 1) : ℝ) =
      (u.val (e 1) : ℝ)
    rw [cubeTetrahedron_coordinate_one]
    change ((u.val (e 1) : ℝ) - u.val (e 2)) + u.val (e 2) = (u.val (e 1) : ℝ)
    ring
  · change (cubeTetrahedron e (cubeTetrahedronInverse e u) (e 2) : ℝ) =
      (u.val (e 2) : ℝ)
    rw [cubeTetrahedron_coordinate_two]
    rfl

/-- The successive differences restore the original barycentric simplex point. -/
@[simp] theorem cubeTetrahedronInverse_tetrahedron (e : Equiv.Perm (Fin 3))
    (s : Simplex 3) :
    cubeTetrahedronInverse e ⟨cubeTetrahedron e s, cubeTetrahedron_sorted e s⟩ = s := by
  apply Subtype.ext
  funext i
  change cubeBarycentric e (cubeTetrahedron e s) i = s i
  fin_cases i
  · change 1 - (cubeTetrahedron e s (e 0) : ℝ) = s 0
    rw [cubeTetrahedron_coordinate_zero]
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
    linarith
  · change (cubeTetrahedron e s (e 0) : ℝ) - cubeTetrahedron e s (e 1) = s 1
    rw [cubeTetrahedron_coordinate_zero, cubeTetrahedron_coordinate_one]
    ring
  · change (cubeTetrahedron e s (e 1) : ℝ) - cubeTetrahedron e s (e 2) = s 2
    rw [cubeTetrahedron_coordinate_one, cubeTetrahedron_coordinate_two]
    ring
  · change (cubeTetrahedron e s (e 2) : ℝ) = s 3
    exact cubeTetrahedron_coordinate_two e s

theorem cubeTetrahedron_range (e : Equiv.Perm (Fin 3)) :
    Set.range (cubeTetrahedron e) = cubeOrderedRegion e := by
  ext u
  constructor
  · rintro ⟨s, rfl⟩
    exact cubeTetrahedron_sorted e s
  · intro hu
    exact ⟨cubeTetrahedronInverse e ⟨u, hu⟩, cubeTetrahedron_inverse e ⟨u, hu⟩⟩

theorem cubeTetrahedron_injective (e : Equiv.Perm (Fin 3)) :
    Function.Injective (cubeTetrahedron e) := by
  intro s t h
  have hh : (⟨cubeTetrahedron e s, cubeTetrahedron_sorted e s⟩ : ↥(cubeOrderedRegion e)) =
      ⟨cubeTetrahedron e t, cubeTetrahedron_sorted e t⟩ := Subtype.ext h
  simpa only [cubeTetrahedronInverse_tetrahedron] using congrArg (cubeTetrahedronInverse e) hh

/-- The actual affine tetrahedron is a homeomorphism onto its closed order region. -/
def cubeTetrahedronHomeomorph (e : Equiv.Perm (Fin 3)) :
    Simplex 3 ≃ₜ ↥(cubeOrderedRegion e) where
  toFun s := ⟨cubeTetrahedron e s, cubeTetrahedron_sorted e s⟩
  invFun := cubeTetrahedronInverse e
  left_inv := cubeTetrahedronInverse_tetrahedron e
  right_inv u := Subtype.ext (cubeTetrahedron_inverse e u)
  continuous_toFun := (cubeTetrahedron e).continuous.subtype_mk _
  continuous_invFun := (cubeTetrahedronInverse e).continuous

end Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation
