import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleBasic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The clockwise quarter turn of the native square

The boundary of the square is preserved literally.  This file records the
actual coordinate map and its pullback on generalized loops.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

/-- Clockwise rotation of the literal two-dimensional unit cube. -/
def quarterTurn : C(Fin 2 → I, Fin 2 → I) where
  toFun u := ![u 1, σ (u 0)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem quarterTurn_apply (u : Fin 2 → I) :
    quarterTurn u = ![u 1, σ (u 0)] := rfl

theorem quarterTurn_boundary (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    quarterTurn u ∈ Cube.boundary (Fin 2) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact ⟨1, Or.inr (by simp [hi])⟩
    · exact ⟨0, Or.inl (by simpa using hi)⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact ⟨1, Or.inl (by simp [hi])⟩
    · exact ⟨0, Or.inr (by simpa using hi)⟩

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Precomposition of an actual generalized loop by the quarter turn. -/
def rotatedSquareLoop (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp quarterTurn, fun u hu => p.property _ (quarterTurn_boundary u hu)⟩

@[simp] theorem rotatedSquareLoop_apply (p : GenLoop (Fin 2) X x) (u : Fin 2 → I) :
    rotatedSquareLoop p u = p ![u 1, σ (u 0)] := rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
