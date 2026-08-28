import Wikipedia.HopfProblem.FourthHurewiczFourSimplexGenericBasic

/-!
# Actual based four-simplices in native fourth homotopy

The general simplex quotient specializes to the nested-minimum quotient
on the native four-cube.  Here `BasedFourSimplex` means that the entire
boundary is based, not merely a lower-dimensional skeleton.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz

abbrev fourSimplexBoundary : Set (Simplex 4) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 4

/-- An actual singular four-simplex with its whole boundary at the base point. -/
abbrev BasedFourSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 4 x

/-- The actual nested-minimum quotient of the native four-cube. -/
abbrev fourSimplexQuotient : C(Fin 4 → I, Simplex 4) :=
  HigherHurewicz.SimplexGeometry.simplexQuotient 4

theorem fourSimplexQuotient_boundary (u : Fin 4 → I) (hu : u ∈ Cube.boundary (Fin 4)) :
    fourSimplexQuotient u ∈ fourSimplexBoundary :=
  HigherHurewicz.SimplexGeometry.simplexQuotient_boundary u hu

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

abbrev basedFourSimplexLoop (τ : BasedFourSimplex x) : GenLoop (Fin 4) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

/-- The class of the original based simplex in Mathlib's native fourth homotopy group. -/
abbrev basedFourSimplexClass (τ : BasedFourSimplex x) : Additive (π_ 4 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

@[simp] theorem basedFourSimplexLoop_apply (τ : BasedFourSimplex x) (u : Fin 4 → I) :
    basedFourSimplexLoop τ u = τ.val (fourSimplexQuotient u) := rfl

theorem basedFourSimplex_face (τ : BasedFourSimplex x) (i : Fin 5) :
    τ.val.comp (simplexFace 3 i) = ContinuousMap.const (Simplex 3) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

abbrev constantBasedFourSimplex (x : X) : BasedFourSimplex x :=
  HigherHurewicz.SimplexGeometry.constantBasedSimplex 4 x

@[simp] theorem basedFourSimplexLoop_constant (x : X) :
    basedFourSimplexLoop (constantBasedFourSimplex x) = GenLoop.const := rfl

@[simp] theorem basedFourSimplexClass_constant (x : X) :
    basedFourSimplexClass (constantBasedFourSimplex x) = 0 := rfl

abbrev mapBasedFourSimplex (f : C(X, Y)) (τ : BasedFourSimplex x) :
    BasedFourSimplex (f x) :=
  HigherHurewicz.SimplexGeometry.mapBasedSimplex f τ

abbrev basedFourSimplexLoopHomotopy {τ υ : BasedFourSimplex x}
    (H : τ.val.HomotopyRel υ.val fourSimplexBoundary) :
    (basedFourSimplexLoop τ).val.HomotopyRel (basedFourSimplexLoop υ).val
      (Cube.boundary (Fin 4)) :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoopHomotopy H

theorem basedFourSimplexClass_homotopy {τ υ : BasedFourSimplex x}
    (H : τ.val.HomotopyRel υ.val fourSimplexBoundary) :
    basedFourSimplexClass τ = basedFourSimplexClass υ :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass_homotopy H

/-- Actual equality on the five face maps supplies the whole-boundary condition. -/
def BasedFourSimplex.ofFaces (τ : C(Simplex 4, X))
    (hτ : ∀ i : Fin 5, τ.comp (simplexFace 3 i) = ContinuousMap.const (Simplex 3) x) :
    BasedFourSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplex.ofFaces τ hτ

@[simp] theorem BasedFourSimplex.ofFaces_val (τ : C(Simplex 4, X))
    (hτ : ∀ i : Fin 5, τ.comp (simplexFace 3 i) = ContinuousMap.const (Simplex 3) x) :
    (BasedFourSimplex.ofFaces τ hτ).val = τ := rfl

end Wikipedia.HopfProblem.FourthHurewicz
