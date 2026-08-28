import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubicalBridge
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubicalBoundary

/-!
# The signed six-face relation in native fourth homotopy

The proof works in all native degrees at least two.  The actual simplex
quotient identifies its boundary value with the genuine cubical boundary
value, which vanishes by relative homotopies and loop-space induction.
The fourth-degree specialization retains every original singular face.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open CubicalBoundary

variable {X : Type*} [TopologicalSpace X] {x : X}
variable {A : Type*} [AddCommGroup A]

/-- The alternating simplex boundary vanishes under any actual cubical evaluator. -/
theorem basedSimplexBoundary_evaluation {n : ℕ} (E : CubicalEvaluator (n + 1) x A)
    (τ : BasedSimplexBoundary (n + 2) x) :
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val •
      E (basedSimplexLoop (basedSimplexBoundaryFace τ i))) = 0 := by
  rw [← simplexBoundaryCube_boundaryValue]
  exact cubicalBoundaryValue_eq_zero n E (simplexBoundaryCube τ)

/-- The original signed face relation in native homotopy, for every degree at least two. -/
theorem basedSimplexBoundary_signed_relation {n : ℕ}
    (τ : BasedSimplexBoundary (n + 3) x) :
    (∑ i : Fin (n + 4), (-1 : ℤ) ^ i.val •
      basedSimplexClass (basedSimplexBoundaryFace τ i)) = 0 :=
  basedSimplexBoundary_evaluation (nativeCubicalEvaluator n x) τ

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The six original four-dimensional faces satisfy the native signed boundary relation. -/
theorem basedFiveSimplex_signed_relation (τ : BasedFiveSimplex x) :
    (∑ i : Fin 6, (-1 : ℤ) ^ i.val • basedFourSimplexClass (basedFiveSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 2) τ

/-- Facewise boundary data suffice; the classes still use the original singular faces. -/
theorem fiveSimplex_signed_relation_ofFaces (τ : C(Simplex 5, X))
    (h : ∀ i : Fin 6, ∀ s ∈ fourSimplexBoundary,
      (τ.comp (simplexFace 4 i)) s = x) :
    (∑ i : Fin 6, (-1 : ℤ) ^ i.val •
      basedFourSimplexClass (basedFiveSimplexFace (BasedFiveSimplex.ofFaces τ h) i)) = 0 :=
  basedFiveSimplex_signed_relation (BasedFiveSimplex.ofFaces τ h)

end Wikipedia.HopfProblem.FourthHurewicz
