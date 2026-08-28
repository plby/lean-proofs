import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSquareGeometry
import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutation simplices in cubes of arbitrary dimension

The simplex associated to a permutation switches on its coordinates in that
order. Its ordered coordinates are tails of the barycentric coordinates.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

open FirstHurewicz SingularMayerVietoris

abbrev CubeN (n : ℕ) := Fin n → I

/-- Barycentric interpolation of vertices in a cube. -/
def cubeAffineSimplex {m n : ℕ} (v : Fin (m + 1) → CubeN n) :
    C(Simplex m, CubeN n) where
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

@[simp] theorem cubeAffineSimplex_coordinate {m n : ℕ}
    (v : Fin (m + 1) → CubeN n) (s : Simplex m) (i : Fin n) :
    (cubeAffineSimplex v s i : ℝ) = ∑ j, s j * (v j i : ℝ) := rfl

@[simp] theorem cubeAffineSimplex_vertex {m n : ℕ}
    (v : Fin (m + 1) → CubeN n) (j : Fin (m + 1)) :
    cubeAffineSimplex v (stdVertices m j) = v j := by
  funext i
  apply Subtype.ext
  simp [cubeAffineSimplex_coordinate, stdVertices, stdSimplex.vertex, Pi.single_apply]

theorem cubeAffineSimplex_face {m n : ℕ}
    (v : Fin (m + 2) → CubeN n) (i : Fin (m + 2)) :
    (cubeAffineSimplex v).comp (simplexFace m i) =
      cubeAffineSimplex (fun j => v (i.succAbove j)) := by
  ext s k
  change (∑ j : Fin (m + 2), simplexFace m i s j * (v j k : ℝ)) =
    ∑ j : Fin (m + 1), s j * (v (i.succAbove j) k : ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  simp only [simplexFace_apply_self, zero_mul, simplexFace_apply_succAbove, zero_add]

theorem cubeAffineSimplex_constant_coordinate {m n : ℕ}
    (v : Fin (m + 1) → CubeN n) (i : Fin n) (c : I)
    (h : ∀ j, v j i = c) (s : Simplex m) : cubeAffineSimplex v s i = c := by
  apply Subtype.ext
  simp only [cubeAffineSimplex_coordinate, h, ← Finset.sum_mul,
    stdSimplex.sum_eq_one, one_mul]

/-- The `k`th vertex has precisely the first `k` coordinates of `e` switched on. -/
def cubeVertex {n : ℕ} (e : Equiv.Perm (Fin n)) (k : Fin (n + 1)) : CubeN n :=
  fun i => if (e.symm i).val < k.val then 1 else 0

/-- The affine simplex of the ordered chain of cube vertices. -/
def cubeSimplex {n : ℕ} (e : Equiv.Perm (Fin n)) : C(Simplex n, CubeN n) :=
  cubeAffineSimplex (cubeVertex e)

@[simp] theorem cubeVertex_zero {n : ℕ} (e : Equiv.Perm (Fin n)) :
    cubeVertex e 0 = fun _ => 0 := by
  funext i
  simp [cubeVertex]

@[simp] theorem cubeVertex_last {n : ℕ} (e : Equiv.Perm (Fin n)) :
    cubeVertex e (Fin.last n) = fun _ => 1 := by
  funext i
  simp [cubeVertex, (e.symm i).isLt]

@[simp] theorem cubeSimplex_vertex {n : ℕ}
    (e : Equiv.Perm (Fin n)) (k : Fin (n + 1)) :
    cubeSimplex e (stdVertices n k) = cubeVertex e k :=
  cubeAffineSimplex_vertex _ _

/-- An ordered cube coordinate is a tail of the barycentric coordinates. -/
theorem cubeSimplex_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : Simplex n) (i : Fin n) :
    (cubeSimplex e s (e i) : ℝ) =
      ∑ k : Fin (n + 1), if i.val < k.val then s k else 0 := by
  simp only [cubeSimplex, cubeAffineSimplex_coordinate, cubeVertex,
    Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

/-- The coordinate order prescribed by the indexing permutation holds on its simplex. -/
theorem cubeSimplex_antitone {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : Simplex n) :
    Antitone (fun i => cubeSimplex e s (e i)) := by
  intro i j hij
  change (cubeSimplex e s (e j) : ℝ) ≤ (cubeSimplex e s (e i) : ℝ)
  rw [cubeSimplex_coordinate, cubeSimplex_coordinate]
  apply Finset.sum_le_sum
  intro k _
  by_cases hj : j.val < k.val
  · have hi : i.val < k.val := lt_of_le_of_lt hij hj
    simp only [if_pos hj, if_pos hi, le_refl]
  · simp only [if_neg hj]
    split_ifs
    · exact stdSimplex.zero_le s k
    · exact le_refl 0

/-- Orientation of the ordered cube-vertex chain. -/
def cubeOrientation {n : ℕ} (e : Equiv.Perm (Fin n)) : ℤ := Equiv.Perm.sign e

@[simp] theorem cubeOrientation_refl (n : ℕ) :
    cubeOrientation (Equiv.refl (Fin n)) = 1 := by
  simp [cubeOrientation]

theorem cubeOrientation_swap {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (h : i ≠ j) :
    cubeOrientation ((Equiv.swap i j).trans e) = -cubeOrientation e := by
  simp [cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap h]

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
