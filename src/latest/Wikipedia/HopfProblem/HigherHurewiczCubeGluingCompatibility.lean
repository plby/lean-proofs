import Wikipedia.HopfProblem.HigherHurewiczCubeGluingBasic
import Wikipedia.HopfProblem.HigherHurewiczCubeGluingCells
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationOverlaps
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationSortTies

/-!
# Coherent simplex homotopies agree on every permutation-cell overlap

Equal cube images have identical barycentric preimages. Sorting permutations
of the same cube point differ by adjacent swaps of tied coordinates, and
each such swap is an actual common simplex face. Coface compatibility
therefore implies the geometric condition needed for continuous pasting.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeGluing

open FirstHurewicz CubeTriangulation SecondHurewicz.SimplyConnected

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

theorem coherentCubeFamily_compatible
    (H₀ : C(Simplex n, X) → C(I × Simplex n, X))
    (H₁ : C(Simplex (n + 1), X) → C(I × Simplex (n + 1), X))
    (hface : FaceCompatibleHomotopies n H₀ H₁) (p : GenLoop (Fin (n + 1)) X x) :
    CubeCompatible (fun e => H₁ (p.val.comp (cubeSimplex e))) := by
  intro e f s t h r
  have hst := cubeSimplex_overlap_preimage e f s t h
  subst t
  have hf : SortedCoordinates (cubeSimplex e s) f := by
    rw [h]
    exact cubeSimplex_sorted f s
  apply eq_of_sorted_adjacent (cubeSimplex e s)
    (fun g => H₁ (p.val.comp (cubeSimplex g)) (r, s))
    ?_ (cubeSimplex_sorted e s) hf
  intro g hg i ht
  apply coherentCubeCell_swap H₀ H₁ hface p g i r s
  apply cubeSimplex_tie g s i
  simpa only [cubeSimplex_eq_of_sorted e g s hg] using ht

end Wikipedia.HopfProblem.HigherHurewicz.CubeGluing
