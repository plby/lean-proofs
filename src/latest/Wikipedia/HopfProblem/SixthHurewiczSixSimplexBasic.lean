import Wikipedia.HopfProblem.FourthHurewiczFourSimplexGenericBasic

/-!
# Actual based six-simplices in native sixth homotopy

These definitions specialize the existing dimension-generic quotient and
native homotopy class.  The entire boundary of the original singular
six-simplex is at the base point.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz

abbrev sixSimplexBoundary : Set (Simplex 6) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 6

/-- An actual singular six-simplex with its whole boundary at the base point. -/
abbrev BasedSixSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 6 x

/-- The existing nested-minimum quotient on the original six-cube. -/
abbrev sixSimplexQuotient : C(Fin 6 → I, Simplex 6) :=
  HigherHurewicz.SimplexGeometry.simplexQuotient 6

theorem sixSimplexQuotient_boundary (u : Fin 6 → I) (hu : u ∈ Cube.boundary (Fin 6)) :
    sixSimplexQuotient u ∈ sixSimplexBoundary :=
  HigherHurewicz.SimplexGeometry.simplexQuotient_boundary u hu

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

abbrev basedSixSimplexLoop (τ : BasedSixSimplex x) : GenLoop (Fin 6) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

/-- The class in Mathlib's original sixth homotopy group. -/
abbrev basedSixSimplexClass (τ : BasedSixSimplex x) : Additive (π_ 6 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

@[simp] theorem basedSixSimplexLoop_apply (τ : BasedSixSimplex x) (u : Fin 6 → I) :
    basedSixSimplexLoop τ u = τ.val (sixSimplexQuotient u) := rfl

theorem basedSixSimplex_face (τ : BasedSixSimplex x) (i : Fin 7) :
    τ.val.comp (simplexFace 5 i) = ContinuousMap.const (Simplex 5) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

abbrev constantBasedSixSimplex (x : X) : BasedSixSimplex x :=
  HigherHurewicz.SimplexGeometry.constantBasedSimplex 6 x

@[simp] theorem basedSixSimplexLoop_constant (x : X) :
    basedSixSimplexLoop (constantBasedSixSimplex x) = GenLoop.const := rfl

@[simp] theorem basedSixSimplexClass_constant (x : X) :
    basedSixSimplexClass (constantBasedSixSimplex x) = 0 := rfl

abbrev mapBasedSixSimplex (f : C(X, Y)) (τ : BasedSixSimplex x) :
    BasedSixSimplex (f x) :=
  HigherHurewicz.SimplexGeometry.mapBasedSimplex f τ

abbrev basedSixSimplexLoopHomotopy {τ υ : BasedSixSimplex x}
    (H : τ.val.HomotopyRel υ.val sixSimplexBoundary) :
    (basedSixSimplexLoop τ).val.HomotopyRel (basedSixSimplexLoop υ).val
      (Cube.boundary (Fin 6)) :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoopHomotopy H

theorem basedSixSimplexClass_homotopy {τ υ : BasedSixSimplex x}
    (H : τ.val.HomotopyRel υ.val sixSimplexBoundary) :
    basedSixSimplexClass τ = basedSixSimplexClass υ :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass_homotopy H

/-- Equality on the seven actual face maps supplies the whole-boundary condition. -/
def BasedSixSimplex.ofFaces (τ : C(Simplex 6, X))
    (hτ : ∀ i : Fin 7, τ.comp (simplexFace 5 i) = ContinuousMap.const (Simplex 5) x) :
    BasedSixSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplex.ofFaces τ hτ

@[simp] theorem BasedSixSimplex.ofFaces_val (τ : C(Simplex 6, X))
    (hτ : ∀ i : Fin 7, τ.comp (simplexFace 5 i) = ContinuousMap.const (Simplex 5) x) :
    (BasedSixSimplex.ofFaces τ hτ).val = τ := rfl

end Wikipedia.HopfProblem.SixthHurewicz
