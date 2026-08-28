import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsRealization
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsCurryingGeometry

/-!
# Actual barycentric maps for interval-cube-simplex prisms

The affine product map used by singular cross products is identified
with interpolation of its actual cube vertices. The comparison allows
arbitrary dimensions and repeated vertices.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation

/-- Affine interpolation in a cube commutes with affine simplex substitution. -/
theorem cubeAffineSimplex_comp {k m n : ℕ} (v : Fin (n + 1) → CubeN k)
    (w : Fin (m + 1) → Simplex n) :
    (cubeAffineSimplex v).comp (affineSimplex w) =
      cubeAffineSimplex (fun j => cubeAffineSimplex v (w j)) := by
  ext t i
  change (cubeAffineSimplex v (affineSimplex w t) i : ℝ) =
    (cubeAffineSimplex (fun j => cubeAffineSimplex v (w j)) t i : ℝ)
  simp only [cubeAffineSimplex_coordinate, affineSimplex_coordinate,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- In particular, selecting standard vertices selects precisely their prescribed cube points. -/
theorem cubeAffineSimplex_comp_selectedVertices {k m n : ℕ}
    (v : Fin (n + 1) → CubeN k) (a : Fin (m + 1) → Fin (n + 1)) :
    (cubeAffineSimplex v).comp (affineSimplex (fun j => stdVertices n (a j))) =
      cubeAffineSimplex (fun j => v (a j)) := by
  rw [cubeAffineSimplex_comp]
  simp only [cubeAffineSimplex_vertex]

/-- The genuine interval-times-ordered-cube-simplex map into the next-dimensional cube. -/
def prismCubeMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(Simplex 1 × Simplex n, CubeN (n + 1)) where
  toFun z := Fin.cases (pathSimplex Path.id z.1) (cubeSimplex e z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (pathSimplex Path.id).continuous.comp continuous_fst
    · exact (continuous_apply j).comp ((cubeSimplex e).continuous.comp continuous_snd)

@[simp] theorem prismCubeMap_zero {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Simplex 1 × Simplex n) :
    prismCubeMap e z 0 = pathSimplex Path.id z.1 := rfl

@[simp] theorem prismCubeMap_succ {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Simplex 1 × Simplex n) (i : Fin n) :
    prismCubeMap e z i.succ = cubeSimplex e z.2 i := rfl

/-- The actual affine product map has the prescribed prism vertices, including repetitions. -/
theorem prismCubeMap_affine {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    (prismCubeMap e).comp
        (productAffineSimplex (fun j => (stdVertices 1 (v j).1, stdVertices n (v j).2))) =
      prismCubeSimplex e v := by
  apply ContinuousMap.ext
  intro t
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply Subtype.ext
    change affineSimplex (fun j => stdVertices 1 (v j).1) t 1 =
      ∑ j, t j * stdVertices 1 (v j).1 1
    exact affineSimplex_coordinate _ _ _
  · change ((cubeAffineSimplex (cubeVertex e)).comp
      (affineSimplex (fun j => stdVertices n (v j).2))) t k = _
    rw [cubeAffineSimplex_comp_selectedVertices]
    rfl

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
