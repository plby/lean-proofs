import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology
import Wikipedia.HopfProblem.SingularMayerVietorisAffineSimplex

/-!
# Integer-affine simplices in the actual product torus

Barycentric interpolation of integral vertices, followed by the native
coordinate quotient, gives singular simplices whose vertices are all zero.
Restriction selects the literal vertices, and an edge is exactly the positive
period loop of the difference of its two integral vertices.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz PeriodTorusHigherHomology

/-- Real barycentric interpolation of a tuple of integral vertices. -/
def affineTorusLift {n k : ℕ} (v : Fin (k + 1) → Fin n → ℤ) :
    C(Simplex k, Fin n → ℝ) where
  toFun t := ∑ i, t i • (fun j => (v i j : ℝ))
  continuous_toFun := continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)

@[simp] theorem affineTorusLift_apply {n k : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (t : Simplex k) :
    affineTorusLift v t = ∑ i, t i • (fun j => (v i j : ℝ)) := rfl

@[simp] theorem affineTorusLift_coordinate {n k : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (t : Simplex k) (j : Fin n) :
    affineTorusLift v t j = ∑ i, t i * (v i j : ℝ) := by
  simp only [affineTorusLift_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

@[simp] theorem affineTorusLift_vertex {n k : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (i : Fin (k + 1)) :
    affineTorusLift v (stdSimplex.vertex (S := ℝ) i) = fun j => (v i j : ℝ) := by
  ext j
  simp [affineTorusLift_coordinate, Pi.single_apply]

/-- A singular simplex in the actual product of additive circles, obtained by
reducing an integral affine simplex modulo the coordinate lattice. -/
def affineTorusSimplex {n k : ℕ} (v : Fin (k + 1) → Fin n → ℤ) :
    SingularSimplex (ProductTorus n) k :=
  (⟨coordinateProjection n, coordinateProjection_continuous n⟩ :
    C(Fin n → ℝ, ProductTorus n)).comp (affineTorusLift v)

@[simp] theorem affineTorusSimplex_apply {n k : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (t : Simplex k) :
    affineTorusSimplex v t = coordinateProjection n
      (∑ i, t i • (fun j => (v i j : ℝ))) := rfl

@[simp] theorem affineTorusSimplex_coordinate {n k : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (t : Simplex k) (j : Fin n) :
    affineTorusSimplex v t j = ((∑ i, t i * (v i j : ℝ) : ℝ) :
      AddCircle (1 : ℝ)) := by
  change (affineTorusLift v t j : AddCircle (1 : ℝ)) = _
  rw [affineTorusLift_coordinate]

/-- Every integral vertex projects to the native zero of the torus. -/
@[simp] theorem affineTorusSimplex_vertex {n k : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (i : Fin (k + 1)) :
    affineTorusSimplex v (stdSimplex.vertex (S := ℝ) i) = 0 := by
  change coordinateProjection n (affineTorusLift v _) = 0
  rw [affineTorusLift_vertex]
  exact (coordinateProjection_eq_zero_iff n _).mpr ⟨v i, rfl⟩

/-- Barycentric interpolation commutes with every map of the vertex sets,
including noninjective maps. -/
theorem affineTorusLift_map {n k l : ℕ} (v : Fin (k + 1) → Fin n → ℤ)
    (f : Fin (l + 1) → Fin (k + 1)) (t : Simplex l) :
    affineTorusLift v (stdSimplex.map f t) = affineTorusLift (v ∘ f) t := by
  ext j
  simp only [affineTorusLift_coordinate, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Exact restriction of the actual singular simplex along a native simplex map. -/
theorem affineTorusSimplex_restrict {n k l : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (f : Fin (l + 1) → Fin (k + 1)) :
    (affineTorusSimplex v).comp
      ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ =
        affineTorusSimplex (v ∘ f) := by
  apply ContinuousMap.ext
  intro t
  change coordinateProjection n (affineTorusLift v (stdSimplex.map f t)) =
    coordinateProjection n (affineTorusLift (v ∘ f) t)
  rw [affineTorusLift_map]

theorem affineTorusSimplex_map {n k l : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (f : Fin (l + 1) → Fin (k + 1))
    (t : Simplex l) :
    affineTorusSimplex v (stdSimplex.map f t) = affineTorusSimplex (v ∘ f) t :=
  ContinuousMap.congr_fun (affineTorusSimplex_restrict v f) t

/-- The faces are the simplices with the corresponding vertex deleted. -/
theorem affineTorusSimplex_face {n k : ℕ}
    (v : Fin (k + 2) → Fin n → ℤ) (i : Fin (k + 2)) :
    (affineTorusSimplex v).comp (simplexFace k i) =
      affineTorusSimplex (fun j => v (i.succAbove j)) :=
  affineTorusSimplex_restrict v i.succAbove

/-- In dimension one, the real affine simplex differs from the straight
period path only by its initial integral vertex. -/
theorem affineTorusLift_one {n : ℕ} (v : Fin 2 → Fin n → ℤ) (t : Simplex 1) :
    affineTorusLift v t = (fun j => (v 0 j : ℝ)) +
      t 1 • (fun j => ((v 1 - v 0) j : ℝ)) := by
  ext j
  rw [affineTorusLift_coordinate, Fin.sum_univ_two]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Int.cast_sub]
  have ht : t 0 = 1 - t 1 := by linarith [stdSimplex.add_eq_one t]
  rw [ht]
  ring

/-- The entire singular edge equals the marked period loop of the vertex
difference; this is equality of continuous maps, not only of homology classes. -/
theorem affineTorusSimplex_one {n : ℕ} (v : Fin 2 → Fin n → ℤ) :
    affineTorusSimplex v = pathSimplex (coordinatePeriodLoop n (v 1 - v 0)) := by
  apply ContinuousMap.ext
  intro t
  change coordinateProjection n (affineTorusLift v t) =
    coordinatePeriodLoop n (v 1 - v 0) (simplexCoordinate 1 1 t)
  rw [affineTorusLift_one, map_add,
    (coordinateProjection_eq_zero_iff n _).mpr ⟨v 0, rfl⟩, zero_add]
  ext j
  rw [coordinateProjection_apply, coordinatePeriodLoop_apply]
  rfl

/-- Restricting to any ordered pair of vertices gives its actual period loop. -/
theorem affineTorusSimplex_edge {n k : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (f : Fin 2 → Fin (k + 1)) :
    (affineTorusSimplex v).comp
      ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ =
        pathSimplex (coordinatePeriodLoop n (v (f 1) - v (f 0))) := by
  rw [affineTorusSimplex_restrict, affineTorusSimplex_one]
  rfl

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
