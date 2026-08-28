import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientCellsBasic
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationCoordinates

/-!
# The principal cube simplex is a section of the quotient

An antitone list is recovered from its prefix minima.  The ordered coordinates
therefore show that the actual principal affine cube simplex is a section of
the quotient in every dimension.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz CubeTriangulation

/-- On an antitone cube point, a nonempty prefix minimum is its last coordinate. -/
theorem prefixMinimum_of_antitone {n : ℕ} (u : Fin n → I) (hu : Antitone u)
    (i : Fin n) : prefixMinimum u (i.val + 1) = u i := by
  apply le_antisymm (prefixMinimum_le_coordinate u (i.val + 1) i (Nat.lt_succ_self _))
  unfold prefixMinimum
  apply Finset.le_inf
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact hu (Nat.le_of_lt_succ hj)

/-- The principal affine simplex recovers every antitone cube point from its quotient. -/
theorem cubeSimplex_quotient_of_antitone {n : ℕ} (u : Fin n → I) (hu : Antitone u) :
    cubeSimplex (Equiv.refl (Fin n)) (simplexQuotient n u) = u := by
  funext i
  apply Subtype.ext
  simpa only [Equiv.refl_apply, prefixMinimum_of_antitone u hu i]
    using cubeSimplex_quotient_coordinate (Equiv.refl (Fin n)) u i

/-- The principal affine cube simplex is an actual section of the simplex quotient. -/
theorem simplexQuotient_cubeSimplex_refl (n : ℕ) :
    (simplexQuotient n).comp (cubeSimplex (Equiv.refl (Fin n))) =
      ContinuousMap.id (Simplex n) := by
  apply ContinuousMap.ext
  intro s
  apply cubeSimplex_injective (Equiv.refl (Fin n))
  exact cubeSimplex_quotient_of_antitone _ (cubeSimplex_antitone (Equiv.refl (Fin n)) s)

/-- The explicit native cube quotient is onto the whole standard simplex. -/
theorem simplexQuotient_surjective (n : ℕ) : Function.Surjective (simplexQuotient n) := by
  intro s
  exact ⟨cubeSimplex (Equiv.refl (Fin n)) s,
    ContinuousMap.congr_fun (simplexQuotient_cubeSimplex_refl n) s⟩

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
