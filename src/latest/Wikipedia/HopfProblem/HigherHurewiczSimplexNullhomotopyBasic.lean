import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionBasic

/-!
# Native simplex and cube models for higher relative nullhomotopies

The flattened simplex is the ordinary full-dimensional simplex in `ℝⁿ`.
The cube is the ordinary coordinatewise unit interval. The boundary used
for based simplices is the existing literal union of barycentric faces.
-/

noncomputable section

open Set
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz

/-- The standard simplex after discarding its zeroth barycentric coordinate. -/
def flatSimplexSet (n : ℕ) : Set (Fin n → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1}

/-- The standard unit cube in its ordinary ambient real coordinate space. -/
def realCubeSet (n : ℕ) : Set (Fin n → ℝ) := Icc 0 1

/-- An actual singular simplex whose entire barycentric boundary is based. -/
def BasedSimplex (n : ℕ) {X : Type} [TopologicalSpace X] (x : X) :=
  {τ : C(Simplex n, X) //
    ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, τ s = x}

/-- The literal constant based simplex in every dimension. -/
def constantBasedSimplex (n : ℕ) {X : Type} [TopologicalSpace X] (x : X) :
    BasedSimplex n x :=
  ⟨ContinuousMap.const (Simplex n) x, fun _ _ => rfl⟩

end Wikipedia.HopfProblem.HigherHurewicz
