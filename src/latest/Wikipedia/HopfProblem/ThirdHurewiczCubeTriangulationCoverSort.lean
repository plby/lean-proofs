import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.UnitInterval

/-!
# Sorting the coordinates of an actual three-dimensional cube

The six orders of three coordinates give the six permutation cells.
The argument applies to any linearly ordered coordinate type, including
the original closed unit interval.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation

variable {α : Type*} [LinearOrder α]

/-- Coordinates in the descending order used by a cube triangulation cell. -/
abbrev SortedCoordinates (u : Fin 3 → α) (e : Equiv.Perm (Fin 3)) : Prop :=
  u (e 2) ≤ u (e 1) ∧ u (e 1) ≤ u (e 0)

/-- Every point has a sorting permutation, including points on coordinate ties. -/
theorem exists_sortedPermutation (u : Fin 3 → α) :
    ∃ e : Equiv.Perm (Fin 3), SortedCoordinates u e := by
  rcases le_total (u 0) (u 1) with h01 | h10
  · rcases le_total (u 1) (u 2) with h12 | h21
    · refine ⟨Equiv.swap 0 2, ?_⟩
      simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h01 h12
    · rcases le_total (u 0) (u 2) with h02 | h20
      · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), ?_⟩
        simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h02 h21
      · refine ⟨Equiv.swap 0 1, ?_⟩
        simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h20 h01
  · rcases le_total (u 0) (u 2) with h02 | h20
    · refine ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1), ?_⟩
      simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h10 h02
    · rcases le_total (u 1) (u 2) with h12 | h21
      · refine ⟨Equiv.swap 1 2, ?_⟩
        simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h12 h20
      · exact ⟨Equiv.refl (Fin 3), h21, h10⟩

/-- A choice of a permutation cell containing the given cube point. -/
def sortedPermutation (u : Fin 3 → α) : Equiv.Perm (Fin 3) :=
  Classical.choose (exists_sortedPermutation u)

theorem sortedPermutation_sorted (u : Fin 3 → α) :
    SortedCoordinates u (sortedPermutation u) :=
  Classical.choose_spec (exists_sortedPermutation u)

theorem sortedPermutation_two_le_one (u : Fin 3 → α) :
    u (sortedPermutation u 2) ≤ u (sortedPermutation u 1) :=
  (sortedPermutation_sorted u).1

theorem sortedPermutation_one_le_zero (u : Fin 3 → α) :
    u (sortedPermutation u 1) ≤ u (sortedPermutation u 0) :=
  (sortedPermutation_sorted u).2

end Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation
