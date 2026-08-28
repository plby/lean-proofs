import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSquareGeometry
import Mathlib.GroupTheory.Perm.Sign

/-!
# The six affine tetrahedra of the native three-dimensional cube

The simplex indexed by a permutation `e` has ordered vertices
`000`, `e₀`, `e₀ + e₁`, `111`.  These are actual continuous singular
simplices in Mathlib's `Fin 3` cube.  Adjacent transpositions identify
their common faces with the original face parametrizations.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.Geometry

open FirstHurewicz SingularMayerVietoris

abbrev Cube3 := Fin 3 → I

/-- Barycentric interpolation of actual cube vertices. -/
def cubeAffineSimplex {n : ℕ} (v : Fin (n + 1) → Cube3) : C(Simplex n, Cube3) where
  toFun s i := ⟨∑ j, s j * (v j i : ℝ), by
    constructor
    · exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (stdSimplex.zero_le s j) (v j i).property.1
    · calc
        ∑ j, s j * (v j i : ℝ) ≤ ∑ j, s j * 1 :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (v j i).property.2 (stdSimplex.zero_le s j)
        _ = 1 := by simp only [mul_one, stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

@[simp] theorem cubeAffineSimplex_coordinate {n : ℕ}
    (v : Fin (n + 1) → Cube3) (s : Simplex n) (i : Fin 3) :
    (cubeAffineSimplex v s i : ℝ) = ∑ j, s j * (v j i : ℝ) := rfl

@[simp] theorem cubeAffineSimplex_vertex {n : ℕ}
    (v : Fin (n + 1) → Cube3) (j : Fin (n + 1)) :
    cubeAffineSimplex v (stdVertices n j) = v j := by
  funext i
  apply Subtype.ext
  simp [cubeAffineSimplex_coordinate, stdVertices, stdSimplex.vertex, Pi.single_apply]

theorem cubeAffineSimplex_face {n : ℕ}
    (v : Fin (n + 2) → Cube3) (i : Fin (n + 2)) :
    (cubeAffineSimplex v).comp (simplexFace n i) =
      cubeAffineSimplex (fun j => v (i.succAbove j)) := by
  ext s k
  change (∑ j : Fin (n + 2), simplexFace n i s j * (v j k : ℝ)) =
    ∑ j : Fin (n + 1), s j * (v (i.succAbove j) k : ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  simp only [simplexFace_apply_self, zero_mul, simplexFace_apply_succAbove, zero_add]

theorem cubeAffineSimplex_constant_coordinate {n : ℕ}
    (v : Fin (n + 1) → Cube3) (i : Fin 3) (c : I)
    (h : ∀ j, v j i = c) (s : Simplex n) : cubeAffineSimplex v s i = c := by
  apply Subtype.ext
  simp only [cubeAffineSimplex_coordinate, h, ← Finset.sum_mul,
    stdSimplex.sum_eq_one, one_mul]

/-- The `k`th vertex switches on precisely the first `k` coordinates in `e`. -/
def cubeVertex (e : Equiv.Perm (Fin 3)) (k : Fin 4) : Cube3 :=
  fun i => if (e.symm i).val < k.val then 1 else 0

/-- The tetrahedron with vertex chain `000 → e₀ → e₀+e₁ → 111`. -/
def cubeTetrahedron (e : Equiv.Perm (Fin 3)) : C(Simplex 3, Cube3) :=
  cubeAffineSimplex (cubeVertex e)

@[simp] theorem cubeVertex_zero (e : Equiv.Perm (Fin 3)) :
    cubeVertex e 0 = fun _ => 0 := by
  funext i
  simp [cubeVertex]

@[simp] theorem cubeVertex_three (e : Equiv.Perm (Fin 3)) :
    cubeVertex e 3 = fun _ => 1 := by
  funext i
  simp [cubeVertex, (e.symm i).isLt]

@[simp] theorem cubeTetrahedron_vertex (e : Equiv.Perm (Fin 3)) (k : Fin 4) :
    cubeTetrahedron e (stdVertices 3 k) = cubeVertex e k :=
  cubeAffineSimplex_vertex _ _

@[simp] theorem cubeTetrahedron_coordinate_zero
    (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    (cubeTetrahedron e s (e 0) : ℝ) = s 1 + s 2 + s 3 := by
  simp [cubeTetrahedron, cubeAffineSimplex_coordinate, cubeVertex,
    Fin.sum_univ_succ, add_assoc]

@[simp] theorem cubeTetrahedron_coordinate_one
    (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    (cubeTetrahedron e s (e 1) : ℝ) = s 2 + s 3 := by
  simp [cubeTetrahedron, cubeAffineSimplex_coordinate, cubeVertex, Fin.sum_univ_succ]

@[simp] theorem cubeTetrahedron_coordinate_two
    (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    (cubeTetrahedron e s (e 2) : ℝ) = s 3 := by
  simp [cubeTetrahedron, cubeAffineSimplex_coordinate, cubeVertex, Fin.sum_univ_succ]

theorem cubeTetrahedron_order_first (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    cubeTetrahedron e s (e 1) ≤ cubeTetrahedron e s (e 0) := by
  change (cubeTetrahedron e s (e 1) : ℝ) ≤ (cubeTetrahedron e s (e 0) : ℝ)
  rw [cubeTetrahedron_coordinate_one, cubeTetrahedron_coordinate_zero]
  linarith [stdSimplex.zero_le s 1]

theorem cubeTetrahedron_order_second (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    cubeTetrahedron e s (e 2) ≤ cubeTetrahedron e s (e 1) := by
  change (cubeTetrahedron e s (e 2) : ℝ) ≤ (cubeTetrahedron e s (e 1) : ℝ)
  rw [cubeTetrahedron_coordinate_two, cubeTetrahedron_coordinate_one]
  exact le_add_of_nonneg_left (stdSimplex.zero_le s 2)

/-- The first face is on the cube side with coordinate `e₀ = 1`. -/
theorem cubeTetrahedron_face_zero_coordinate (e : Equiv.Perm (Fin 3)) (s : Simplex 2) :
    cubeTetrahedron e (simplexFace 2 0 s) (e 0) = 1 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp (simplexFace 2 0)) s (e 0) = 1
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  fin_cases j <;> simp [cubeVertex, Fin.succAbove]

/-- The last face is on the cube side with coordinate `e₂ = 0`. -/
theorem cubeTetrahedron_face_three_coordinate (e : Equiv.Perm (Fin 3)) (s : Simplex 2) :
    cubeTetrahedron e (simplexFace 2 3 s) (e 2) = 0 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp (simplexFace 2 3)) s (e 2) = 0
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  fin_cases j <;> simp [cubeVertex, Fin.succAbove]

theorem cubeTetrahedron_face_zero_boundary (e : Equiv.Perm (Fin 3)) (s : Simplex 2) :
    cubeTetrahedron e (simplexFace 2 0 s) ∈ Cube.boundary (Fin 3) :=
  ⟨e 0, Or.inr (cubeTetrahedron_face_zero_coordinate e s)⟩

theorem cubeTetrahedron_face_three_boundary (e : Equiv.Perm (Fin 3)) (s : Simplex 2) :
    cubeTetrahedron e (simplexFace 2 3 s) ∈ Cube.boundary (Fin 3) :=
  ⟨e 2, Or.inl (cubeTetrahedron_face_three_coordinate e s)⟩

/-- Swapping the first two switched coordinates preserves the first interior face. -/
theorem cubeTetrahedron_face_one_swap (e : Equiv.Perm (Fin 3)) :
    (cubeTetrahedron e).comp (simplexFace 2 1) =
      (cubeTetrahedron ((Equiv.swap 0 1).trans e)).comp (simplexFace 2 1) := by
  simp only [cubeTetrahedron, cubeAffineSimplex_face]
  congr 1
  funext j i
  obtain ⟨k, rfl⟩ := e.surjective i
  fin_cases j <;> fin_cases k <;> simp [cubeVertex, Equiv.swap_apply_def, Fin.succAbove]

/-- Swapping the last two switched coordinates preserves the second interior face. -/
theorem cubeTetrahedron_face_two_swap (e : Equiv.Perm (Fin 3)) :
    (cubeTetrahedron e).comp (simplexFace 2 2) =
      (cubeTetrahedron ((Equiv.swap 1 2).trans e)).comp (simplexFace 2 2) := by
  simp only [cubeTetrahedron, cubeAffineSimplex_face]
  congr 1
  funext j i
  obtain ⟨k, rfl⟩ := e.surjective i
  fin_cases j <;> fin_cases k <;> simp [cubeVertex, Equiv.swap_apply_def, Fin.succAbove]

/-- The orientation of the ordered vertex chain is the permutation sign. -/
def cubeOrientation (e : Equiv.Perm (Fin 3)) : ℤ := Equiv.Perm.sign e

@[simp] theorem cubeOrientation_refl : cubeOrientation (Equiv.refl (Fin 3)) = 1 := by
  simp [cubeOrientation]

theorem cubeOrientation_swap (e : Equiv.Perm (Fin 3)) {i j : Fin 3} (h : i ≠ j) :
    cubeOrientation ((Equiv.swap i j).trans e) = -cubeOrientation e := by
  simp [cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap h]

end Wikipedia.HopfProblem.ThirdHurewicz.Geometry
