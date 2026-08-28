import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientCellsBasic
import Mathlib.Order.Preorder.Finite

/-!
# Nonprincipal cube simplices map to the simplex boundary

A nonidentity permutation simplex has a coordinate inversion in the fixed
native order.  That inversion forces a repeated prefix minimum and hence a
zero barycentric coordinate of the quotient.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz CubeTriangulation

/-- An inversion in the fixed cube-coordinate order forces a genuine simplex face. -/
theorem simplexQuotient_boundary_of_coordinate_le {n : ℕ} (u : Fin n → I)
    (i j : Fin n) (hij : i < j) (hu : u i ≤ u j) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  refine ⟨j.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u j.val j.isLt]
  have hp : prefixMinimum u j.val ≤ u j :=
    (prefixMinimum_le_coordinate u j.val i hij).trans hu
  rw [min_eq_left hp]
  exact sub_self _

/-- Every nonidentity ordering has an inversion in the fixed native coordinate order. -/
theorem cubeSimplex_coordinate_inversion {n : ℕ} (e : Equiv.Perm (Fin n))
    (he : e ≠ Equiv.refl (Fin n)) (s : Simplex n) :
    ∃ i j : Fin n, i < j ∧ cubeSimplex e s i ≤ cubeSimplex e s j := by
  by_contra h
  have hu : StrictAnti (cubeSimplex e s) := by
    intro i j hij
    exact lt_of_not_ge (fun hle => h ⟨i, j, hij, hle⟩)
  have hm : Monotone e := by
    intro i j hij
    exact hu.le_iff_ge.mp (cubeSimplex_antitone e s hij)
  apply he
  apply Equiv.ext
  intro i
  exact (hm.strictMono_of_injective e.injective).apply_eq

/-- Every nonprincipal affine cube simplex lands in the actual simplex boundary. -/
theorem simplexQuotient_cubeSimplex_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (he : e ≠ Equiv.refl (Fin n)) (s : Simplex n) :
    simplexQuotient n (cubeSimplex e s) ∈
      SecondHurewicz.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, j, hij, hu⟩ := cubeSimplex_coordinate_inversion e he s
  exact simplexQuotient_boundary_of_coordinate_le _ i j hij hu

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
