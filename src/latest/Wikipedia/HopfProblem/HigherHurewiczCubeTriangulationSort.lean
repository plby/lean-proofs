import Mathlib.Data.Fin.Tuple.Sort

/-!
# Sorting arbitrary finite-dimensional cube coordinates

We use Mathlib's actual tuple-sorting permutation, with the dual order
to obtain the descending coordinate order of a cube simplex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- The coordinate order of a permutation simplex, in any finite dimension. -/
abbrev SortedCoordinates (u : Fin n → α) (e : Equiv.Perm (Fin n)) : Prop :=
  Antitone (fun i => u (e i))

/-- Mathlib's sorting permutation for the descending order. -/
def sortedPermutation (u : Fin n → α) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => OrderDual.toDual (u i))

theorem sortedPermutation_sorted (u : Fin n → α) :
    SortedCoordinates u (sortedPermutation u) :=
  Tuple.monotone_sort (fun i => OrderDual.toDual (u i))

theorem exists_sortedPermutation (u : Fin n → α) :
    ∃ e : Equiv.Perm (Fin n), SortedCoordinates u e :=
  ⟨sortedPermutation u, sortedPermutation_sorted u⟩

/-- The ordered values are independent of how equal coordinates are permuted. -/
theorem sorted_values_eq (u : Fin n → α) {e f : Equiv.Perm (Fin n)}
    (he : SortedCoordinates u e) (hf : SortedCoordinates u f) :
    ∀ i : Fin n, u (e i) = u (f i) :=
  congrFun (Tuple.unique_antitone he hf)

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
