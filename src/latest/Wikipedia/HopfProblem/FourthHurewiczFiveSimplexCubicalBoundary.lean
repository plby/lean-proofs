import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubicalReduction
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexSquareBoundary

/-!
# The unconditional native cubical boundary relation

The square relation is an actual relative homotopy across the square.
Successive whiskering reduces every higher-dimensional case to that
relation in an iterated actual loop space.  No homology comparison,
degree calculation, or presentation theorem is assumed.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

universe u v

/-- Every genuine codimension-two-based cube has zero evaluated boundary. -/
theorem cubicalBoundaryValue_eq_zero (n : ℕ) :
    ∀ {X : Type u} [TopologicalSpace X] {x : X} {A : Type v} [AddCommGroup A]
      (E : CubicalEvaluator (n + 1) x A) (F : BasedCubicalCell (n + 2) x),
      cubicalBoundaryValue E F = 0 := by
  induction n with
  | zero =>
    intro X _ x A _ E F
    exact cubicalBoundaryValue_square E F
  | succ n ih =>
    intro X _ x A _ E F
    rw [cubicalBoundaryValue_dimension_reduction, ih E.uncurry (whiskeredCell F), neg_zero]

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The relation in Mathlib's original native homotopy groups, in every degree at least two. -/
theorem native_cubical_boundary_relation {n : ℕ} (F : BasedCubicalCell (n + 3) x) :
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val •
      (NativeSubdivision.nativeClass (cubicalUpperFace F i) -
        NativeSubdivision.nativeClass (cubicalLowerFace F i))) = 0 :=
  cubicalBoundaryValue_eq_zero (n + 1) (nativeCubicalEvaluator n x) F

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
