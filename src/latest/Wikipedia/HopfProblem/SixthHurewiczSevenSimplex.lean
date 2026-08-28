import Wikipedia.HopfProblem.SixthHurewiczSevenSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplex

/-!
# The signed eight-face relation in native sixth homotopy

The dimension-generic native simplex-boundary theorem supplies this
specialization directly.  No new cubical geometry, subdivision theorem,
or homology comparison is required.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The eight original six-dimensional faces satisfy the native signed relation. -/
theorem basedSevenSimplex_signed_relation (τ : BasedSevenSimplex x) :
    (∑ i : Fin 8, (-1 : ℤ) ^ i.val • basedSixSimplexClass (basedSevenSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 4) τ

/-- The original facewise boundary data suffice for the native signed relation. -/
theorem sevenSimplex_signed_relation_ofFaces (τ : C(Simplex 7, X))
    (h : ∀ i : Fin 8, ∀ s ∈ sixSimplexBoundary,
      (τ.comp (simplexFace 6 i)) s = x) :
    (∑ i : Fin 8, (-1 : ℤ) ^ i.val •
      basedSixSimplexClass (basedSevenSimplexFace (BasedSevenSimplex.ofFaces τ h) i)) = 0 :=
  basedSevenSimplex_signed_relation (BasedSevenSimplex.ofFaces τ h)

end Wikipedia.HopfProblem.SixthHurewicz
