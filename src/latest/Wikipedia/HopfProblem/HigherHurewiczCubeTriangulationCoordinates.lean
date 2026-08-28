import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationCoordinatesBasic
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometryCoordinates

/-!
# The ordered cube regions are the actual permutation simplices

The successive-coordinate-difference map is a continuous inverse to the
original affine simplex on its closed coordinate-order region.
-/

noncomputable section

open Set
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

open FirstHurewicz

/-- The cube region with the coordinate order specified by a permutation. -/
def cubeOrderedRegion {n : ℕ} (e : Equiv.Perm (Fin n)) : Set (CubeN n) :=
  {u | SortedCoordinates u e}

theorem continuous_cubeCoordinate {n : ℕ} (i : Fin n) :
    Continuous (fun u : CubeN n => (u i : ℝ)) :=
  continuous_subtype_val.comp (continuous_apply i)

theorem isClosed_cubeOrderedRegion {n : ℕ} (e : Equiv.Perm (Fin n)) :
    IsClosed (cubeOrderedRegion e) := by
  change IsClosed {u : CubeN n | ∀ i j, i ≤ j → (u (e j) : ℝ) ≤ (u (e i) : ℝ)}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (continuous_cubeCoordinate (e j)) (continuous_cubeCoordinate (e i))

theorem continuous_cubeExtendedCoordinates {n : ℕ} (e : Equiv.Perm (Fin n))
    (i : Fin (n + 2)) : Continuous (fun u : CubeN n => cubeExtendedCoordinates e u i) := by
  cases i using Fin.cases with
  | zero => simpa only [cubeExtendedCoordinates_zero] using
      (continuous_const : Continuous (fun _ : CubeN n => (1 : ℝ)))
  | succ i =>
    cases i using Fin.lastCases with
    | last =>
      simpa only [Fin.succ_last, cubeExtendedCoordinates_last] using
        (continuous_const : Continuous (fun _ : CubeN n => (0 : ℝ)))
    | cast i =>
      simpa only [cubeExtendedCoordinates_inner] using continuous_cubeCoordinate (e i)

theorem continuous_cubeBarycentric {n : ℕ} (e : Equiv.Perm (Fin n))
    (i : Fin (n + 1)) : Continuous (fun u : CubeN n => cubeBarycentric e u i) :=
  (continuous_cubeExtendedCoordinates e i.castSucc).sub
    (continuous_cubeExtendedCoordinates e i.succ)

/-- The actual continuous inverse on the precise coordinate-order region. -/
def cubeSimplexInverse {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(↥(cubeOrderedRegion e), Simplex n) where
  toFun u := ⟨cubeBarycentric e u.val,
    ⟨cubeBarycentric_nonneg e u.val u.property, cubeBarycentric_sum e u.val⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_cubeBarycentric e i).comp continuous_subtype_val

@[simp] theorem cubeSimplexInverse_coordinate {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : ↥(cubeOrderedRegion e)) (i : Fin (n + 1)) :
    cubeSimplexInverse e u i = cubeBarycentric e u.val i := rfl

theorem cubeSimplex_sorted {n : ℕ} (e : Equiv.Perm (Fin n)) (s : Simplex n) :
    SortedCoordinates (cubeSimplex e s) e := cubeSimplex_antitone e s

/-- The affine simplex restores every point of its coordinate-order region. -/
@[simp] theorem cubeSimplex_inverse {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : ↥(cubeOrderedRegion e)) :
    cubeSimplex e (cubeSimplexInverse e u) = u.val := by
  funext k
  obtain ⟨i, rfl⟩ := e.surjective k
  apply Subtype.ext
  rw [cubeSimplex_coordinate]
  exact cubeBarycentric_tail e u.val i

/-- The successive differences restore the original barycentric simplex point. -/
@[simp] theorem cubeSimplexInverse_simplex {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : Simplex n) :
    cubeSimplexInverse e ⟨cubeSimplex e s, cubeSimplex_sorted e s⟩ = s := by
  cases n with
  | zero => exact (simplexZero_eq_vertex _).trans (simplexZero_eq_vertex s).symm
  | succ n =>
    apply Subtype.ext
    funext i
    change cubeBarycentric e (cubeSimplex e s) i = s i
    cases i using Fin.cases with
    | zero =>
      rw [cubeBarycentric_zero, cubeSimplex_coordinate_zero]
      ring
    | succ i =>
      cases i using Fin.lastCases with
      | last =>
        simpa only [Fin.succ_last, cubeBarycentric_last] using cubeSimplex_coordinate_last e s
      | cast i =>
        simpa only [← Fin.castSucc_succ, cubeBarycentric_inner]
          using cubeSimplex_adjacent_difference e s i

theorem cubeSimplex_range {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Set.range (cubeSimplex e) = cubeOrderedRegion e := by
  ext u
  constructor
  · rintro ⟨s, rfl⟩
    exact cubeSimplex_sorted e s
  · intro hu
    exact ⟨cubeSimplexInverse e ⟨u, hu⟩, cubeSimplex_inverse e ⟨u, hu⟩⟩

theorem cubeSimplex_injective {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Function.Injective (cubeSimplex e) := by
  intro s t h
  have hh : (⟨cubeSimplex e s, cubeSimplex_sorted e s⟩ : ↥(cubeOrderedRegion e)) =
      ⟨cubeSimplex e t, cubeSimplex_sorted e t⟩ := Subtype.ext h
  simpa only [cubeSimplexInverse_simplex] using congrArg (cubeSimplexInverse e) hh

/-- Each original affine simplex is a homeomorphism onto its closed order region. -/
def cubeSimplexHomeomorph {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Simplex n ≃ₜ ↥(cubeOrderedRegion e) where
  toFun s := ⟨cubeSimplex e s, cubeSimplex_sorted e s⟩
  invFun := cubeSimplexInverse e
  left_inv := cubeSimplexInverse_simplex e
  right_inv u := Subtype.ext (cubeSimplex_inverse e u)
  continuous_toFun := (cubeSimplex e).continuous.subtype_mk _
  continuous_invFun := (cubeSimplexInverse e).continuous

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
