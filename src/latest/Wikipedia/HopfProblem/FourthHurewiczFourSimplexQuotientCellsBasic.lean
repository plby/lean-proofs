import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientBasic
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationCoordinatesBasic

/-!
# The simplex quotient in ordered cube coordinates

The tails of the successive prefix-minimum differences telescope.  Thus an
ordered coordinate of any permutation simplex, evaluated on the quotient,
is exactly the corresponding prefix minimum of the original cube point.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz CubeTriangulation

/-- Ordered affine cube coordinates of the quotient are the actual prefix minima. -/
theorem cubeSimplex_quotient_coordinate {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : Fin n → I) (i : Fin n) :
    (cubeSimplex e (simplexQuotient n u) (e i) : ℝ) =
      (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [cubeSimplex_coordinate]
  have h := sum_fin_differences_tail (n + 1)
    (fun k : Fin (n + 2) => (extendedMinimum u k.val : ℝ)) i.succ
  simpa only [simplexQuotient_apply, Fin.val_castSucc, Fin.val_succ,
    Nat.succ_le_iff, Fin.val_last, extendedMinimum_last_succ,
    show ((0 : I) : ℝ) = 0 from rfl, sub_zero,
    extendedMinimum_of_le u (i.val + 1) i.isLt] using h

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
