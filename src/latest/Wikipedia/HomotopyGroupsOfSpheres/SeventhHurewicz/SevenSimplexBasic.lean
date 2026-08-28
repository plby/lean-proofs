import Wikipedia.HopfProblem.FourthHurewiczFourSimplexGenericBasic

/-!
# Actual based seven-simplices in native seventh homotopy

These definitions specialize the existing dimension-generic quotient and
native homotopy class.  The entire boundary of the original singular
seven-simplex is at the base point.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz

abbrev sevenSimplexBoundary : Set (Simplex 7) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 7

/-- An actual singular seven-simplex with its whole boundary at the base point. -/
abbrev BasedSevenSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 7 x

/-- The existing nested-minimum quotient on the original seven-cube. -/
abbrev sevenSimplexQuotient : C(Fin 7 → I, Simplex 7) :=
  HigherHurewicz.SimplexGeometry.simplexQuotient 7

theorem sevenSimplexQuotient_boundary (u : Fin 7 → I) (hu : u ∈ Cube.boundary (Fin 7)) :
    sevenSimplexQuotient u ∈ sevenSimplexBoundary :=
  HigherHurewicz.SimplexGeometry.simplexQuotient_boundary u hu

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

abbrev basedSevenSimplexLoop (τ : BasedSevenSimplex x) : GenLoop (Fin 7) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

/-- The class in Mathlib's original seventh homotopy group. -/
abbrev basedSevenSimplexClass (τ : BasedSevenSimplex x) : Additive (π_ 7 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

@[simp] theorem basedSevenSimplexLoop_apply (τ : BasedSevenSimplex x) (u : Fin 7 → I) :
    basedSevenSimplexLoop τ u = τ.val (sevenSimplexQuotient u) := rfl

theorem basedSevenSimplex_face (τ : BasedSevenSimplex x) (i : Fin 8) :
    τ.val.comp (simplexFace 6 i) = ContinuousMap.const (Simplex 6) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

abbrev constantBasedSevenSimplex (x : X) : BasedSevenSimplex x :=
  HigherHurewicz.SimplexGeometry.constantBasedSimplex 7 x

@[simp] theorem basedSevenSimplexLoop_constant (x : X) :
    basedSevenSimplexLoop (constantBasedSevenSimplex x) = GenLoop.const := rfl

@[simp] theorem basedSevenSimplexClass_constant (x : X) :
    basedSevenSimplexClass (constantBasedSevenSimplex x) = 0 := rfl

abbrev mapBasedSevenSimplex (f : C(X, Y)) (τ : BasedSevenSimplex x) :
    BasedSevenSimplex (f x) :=
  HigherHurewicz.SimplexGeometry.mapBasedSimplex f τ

abbrev basedSevenSimplexLoopHomotopy {τ υ : BasedSevenSimplex x}
    (H : τ.val.HomotopyRel υ.val sevenSimplexBoundary) :
    (basedSevenSimplexLoop τ).val.HomotopyRel (basedSevenSimplexLoop υ).val
      (Cube.boundary (Fin 7)) :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoopHomotopy H

theorem basedSevenSimplexClass_homotopy {τ υ : BasedSevenSimplex x}
    (H : τ.val.HomotopyRel υ.val sevenSimplexBoundary) :
    basedSevenSimplexClass τ = basedSevenSimplexClass υ :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass_homotopy H

/-- Equality on the eight actual face maps supplies the whole-boundary condition. -/
def BasedSevenSimplex.ofFaces (τ : C(Simplex 7, X))
    (hτ : ∀ i : Fin 8, τ.comp (simplexFace 6 i) = ContinuousMap.const (Simplex 6) x) :
    BasedSevenSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplex.ofFaces τ hτ

@[simp] theorem BasedSevenSimplex.ofFaces_val (τ : C(Simplex 7, X))
    (hτ : ∀ i : Fin 8, τ.comp (simplexFace 6 i) = ContinuousMap.const (Simplex 6) x) :
    (BasedSevenSimplex.ofFaces τ hτ).val = τ := rfl

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
