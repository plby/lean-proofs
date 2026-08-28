import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.EightSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplex

/-!
# The signed nine-face relation in native seventh homotopy

The dimension-generic native simplex-boundary theorem supplies this
specialization directly.  No new cubical geometry, subdivision theorem,
or homology comparison is required.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The nine original seven-dimensional faces satisfy the native signed relation. -/
theorem basedEightSimplex_signed_relation (τ : BasedEightSimplex x) :
    (∑ i : Fin 9, (-1 : ℤ) ^ i.val • basedSevenSimplexClass (basedEightSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 5) τ

/-- The original facewise boundary data suffice for the native signed relation. -/
theorem eightSimplex_signed_relation_ofFaces (τ : C(Simplex 8, X))
    (h : ∀ i : Fin 9, ∀ s ∈ sevenSimplexBoundary,
      (τ.comp (simplexFace 7 i)) s = x) :
    (∑ i : Fin 9, (-1 : ℤ) ^ i.val •
      basedSevenSimplexClass (basedEightSimplexFace (BasedEightSimplex.ofFaces τ h) i)) = 0 :=
  basedEightSimplex_signed_relation (BasedEightSimplex.ofFaces τ h)

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
