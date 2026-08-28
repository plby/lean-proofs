import Wikipedia.HopfProblem.FifthHurewiczSixSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplex

/-!
# The signed seven-face relation in native fifth homotopy

The dimension-generic native simplex-boundary theorem supplies this
specialization directly.  No new cubical geometry, subdivision theorem,
or homology comparison is required.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The seven original five-dimensional faces satisfy the native signed relation. -/
theorem basedSixSimplex_signed_relation (τ : BasedSixSimplex x) :
    (∑ i : Fin 7, (-1 : ℤ) ^ i.val • basedFiveSimplexClass (basedSixSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 3) τ

/-- The original facewise boundary data suffice for the native signed relation. -/
theorem sixSimplex_signed_relation_ofFaces (τ : C(Simplex 6, X))
    (h : ∀ i : Fin 7, ∀ s ∈ fiveSimplexBoundary,
      (τ.comp (simplexFace 5 i)) s = x) :
    (∑ i : Fin 7, (-1 : ℤ) ^ i.val •
      basedFiveSimplexClass (basedSixSimplexFace (BasedSixSimplex.ofFaces τ h) i)) = 0 :=
  basedSixSimplex_signed_relation (BasedSixSimplex.ofFaces τ h)

end Wikipedia.HopfProblem.FifthHurewicz
