import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationCoordinates

/-!
# Exact agreement of barycentric preimages on cube-simplex overlaps

All sorting permutations of a cube point have the same ordered coordinate
values. Since the ordered coordinates of a cell are barycentric tails,
the same barycentric point represents that cube point in every such cell.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

open FirstHurewicz

variable {n : ℕ}

/-- Every order region containing a cell point uses the same barycentric preimage. -/
theorem cubeSimplex_eq_of_sorted (e f : Equiv.Perm (Fin n)) (s : Simplex n)
    (hf : SortedCoordinates (cubeSimplex e s) f) :
    cubeSimplex f s = cubeSimplex e s := by
  funext k
  obtain ⟨i, rfl⟩ := f.surjective k
  apply Subtype.ext
  calc
    (cubeSimplex f s (f i) : ℝ) =
        ∑ k : Fin (n + 1), if i.val < k.val then s k else 0 :=
      cubeSimplex_coordinate f s i
    _ = (cubeSimplex e s (e i) : ℝ) := (cubeSimplex_coordinate e s i).symm
    _ = (cubeSimplex e s (f i) : ℝ) :=
      congrArg Subtype.val (sorted_values_eq (cubeSimplex e s) (cubeSimplex_sorted e s) hf i)

/-- Equal images in any two permutation simplices have identical barycentric preimages. -/
theorem cubeSimplex_overlap_preimage (e f : Equiv.Perm (Fin n))
    (s t : Simplex n) (h : cubeSimplex e s = cubeSimplex f t) : s = t := by
  have hf : SortedCoordinates (cubeSimplex e s) f := by
    rw [h]
    exact cubeSimplex_sorted f t
  exact cubeSimplex_injective f ((cubeSimplex_eq_of_sorted e f s hf).trans h)

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
