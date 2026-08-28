import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexRestrictionsA
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexRestrictionsB

/-!
# The two and three surviving terms in the actual signed cube sums

All sums are indexed by the original permutations and carry their actual
signs. The seven discarded restrictions are literally constant simplices.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open Geometry

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Exactly faces three and one survive in the first actual six-term sum. -/
theorem fourSimplexTetrahedraA_sum (τ : BasedFourSimplex x) :
    ∑ e : Equiv.Perm (Fin 3), cubeOrientation e •
        basedThreeSimplexClass (fourSimplexTetrahedronA τ e) =
      basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1) := by
  rw [← cubePermutation_bijective.sum_comp
    (fun e => cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronA τ e))]
  simp [Fin.sum_univ_succ, cubeOrientation_cubePermutation,
    fourSimplexTetrahedronA_zero, fourSimplexTetrahedronA_one, fourSimplexTetrahedronA_two,
    fourSimplexTetrahedronA_three, fourSimplexTetrahedronA_four, fourSimplexTetrahedronA_five]

/-- The other three faces occur with their proven odd vertex-order signs. -/
theorem fourSimplexTetrahedraB_sum (τ : BasedFourSimplex x) :
    ∑ e : Equiv.Perm (Fin 3), cubeOrientation e •
        basedThreeSimplexClass (fourSimplexTetrahedronB τ e) =
      -(basedThreeSimplexClass (basedFourSimplexFace τ 4) +
        basedThreeSimplexClass (basedFourSimplexFace τ 2) +
        basedThreeSimplexClass (basedFourSimplexFace τ 0)) := by
  rw [← cubePermutation_bijective.sum_comp
    (fun e => cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronB τ e))]
  simp [Fin.sum_univ_succ, cubeOrientation_cubePermutation, add_assoc,
    fourSimplexTetrahedronB_zero, fourSimplexTetrahedronB_one, fourSimplexTetrahedronB_two,
    fourSimplexTetrahedronB_three, fourSimplexTetrahedronB_four, fourSimplexTetrahedronB_five,
    basedThreeSimplexSwapLast_class]
  abel

end Wikipedia.HopfProblem.ThirdHurewicz
