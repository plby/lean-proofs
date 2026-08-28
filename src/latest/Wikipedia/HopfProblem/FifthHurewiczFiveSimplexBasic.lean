import Wikipedia.HopfProblem.FourthHurewiczFourSimplexGenericBasic

/-!
# Actual based five-simplices in native fifth homotopy

These are specializations of the dimension-generic simplex quotient and
native homotopy class.  The entire geometric boundary of the original
singular simplex is required to be at the base point.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz

abbrev fiveSimplexBoundary : Set (Simplex 5) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 5

/-- An actual singular five-simplex with its whole boundary at the base point. -/
abbrev BasedFiveSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 5 x

/-- The dimension-generic nested-minimum quotient, on the actual five-cube. -/
abbrev fiveSimplexQuotient : C(Fin 5 → I, Simplex 5) :=
  HigherHurewicz.SimplexGeometry.simplexQuotient 5

theorem fiveSimplexQuotient_boundary (u : Fin 5 → I) (hu : u ∈ Cube.boundary (Fin 5)) :
    fiveSimplexQuotient u ∈ fiveSimplexBoundary :=
  HigherHurewicz.SimplexGeometry.simplexQuotient_boundary u hu

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

abbrev basedFiveSimplexLoop (τ : BasedFiveSimplex x) : GenLoop (Fin 5) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

/-- The class in Mathlib's original fifth homotopy group. -/
abbrev basedFiveSimplexClass (τ : BasedFiveSimplex x) : Additive (π_ 5 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

@[simp] theorem basedFiveSimplexLoop_apply (τ : BasedFiveSimplex x) (u : Fin 5 → I) :
    basedFiveSimplexLoop τ u = τ.val (fiveSimplexQuotient u) := rfl

theorem basedFiveSimplex_face (τ : BasedFiveSimplex x) (i : Fin 6) :
    τ.val.comp (simplexFace 4 i) = ContinuousMap.const (Simplex 4) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

abbrev constantBasedFiveSimplex (x : X) : BasedFiveSimplex x :=
  HigherHurewicz.SimplexGeometry.constantBasedSimplex 5 x

@[simp] theorem basedFiveSimplexLoop_constant (x : X) :
    basedFiveSimplexLoop (constantBasedFiveSimplex x) = GenLoop.const := rfl

@[simp] theorem basedFiveSimplexClass_constant (x : X) :
    basedFiveSimplexClass (constantBasedFiveSimplex x) = 0 := rfl

abbrev mapBasedFiveSimplex (f : C(X, Y)) (τ : BasedFiveSimplex x) :
    BasedFiveSimplex (f x) :=
  HigherHurewicz.SimplexGeometry.mapBasedSimplex f τ

abbrev basedFiveSimplexLoopHomotopy {τ υ : BasedFiveSimplex x}
    (H : τ.val.HomotopyRel υ.val fiveSimplexBoundary) :
    (basedFiveSimplexLoop τ).val.HomotopyRel (basedFiveSimplexLoop υ).val
      (Cube.boundary (Fin 5)) :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoopHomotopy H

theorem basedFiveSimplexClass_homotopy {τ υ : BasedFiveSimplex x}
    (H : τ.val.HomotopyRel υ.val fiveSimplexBoundary) :
    basedFiveSimplexClass τ = basedFiveSimplexClass υ :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass_homotopy H

/-- Equality on the six actual face maps supplies the whole-boundary condition. -/
def BasedFiveSimplex.ofFaces (τ : C(Simplex 5, X))
    (hτ : ∀ i : Fin 6, τ.comp (simplexFace 4 i) = ContinuousMap.const (Simplex 4) x) :
    BasedFiveSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplex.ofFaces τ hτ

@[simp] theorem BasedFiveSimplex.ofFaces_val (τ : C(Simplex 5, X))
    (hτ : ∀ i : Fin 6, τ.comp (simplexFace 4 i) = ContinuousMap.const (Simplex 4) x) :
    (BasedFiveSimplex.ofFaces τ hτ).val = τ := rfl

end Wikipedia.HopfProblem.FifthHurewicz
