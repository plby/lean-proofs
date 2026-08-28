import Wikipedia.HopfProblem.SixthHurewiczEvaluation
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsCurryingGeometry

/-!
# Currying a native six-cube into the continuous interval-map space

The remaining five cube coordinates form an actual based generalized
loop in the compact-open space of interval maps. The frozen joint
evaluation map recovers the original six-cube with its coordinate order.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz.CubeSubdivision

open FourthHurewicz.CubeSubdivision (evalLeft)

/-- A boundary point of the remaining five-cube stays on the native six-cube boundary. -/
theorem cubeCoordinates_boundary_right (s : I) {u : Fin 5 → I}
    (hu : u ∈ Cube.boundary (Fin 5)) :
    cubeCoordinates (s, u) ∈ Cube.boundary (Fin 6) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa only [cubeCoordinates_succ] using hi⟩

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The actual curried based five-loop, retaining the first interval as its value variable. -/
def curryLoop (p : GenLoop (Fin 6) X x) :
    GenLoop (Fin 5) C(I, X) (ContinuousMap.const I x) :=
  ⟨((cubeMap p).comp ContinuousMap.prodSwap).curry, by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (cubeCoordinates_boundary_right s hu)⟩

@[simp] theorem curryLoop_apply (p : GenLoop (Fin 6) X x) (u : Fin 5 → I) (s : I) :
    curryLoop p u s = p (cubeCoordinates (s, u)) := rfl

/-- Evaluating the actual curried loop recovers the original product-coordinate six-cube map. -/
theorem evalLeft_comp_curryLoop (p : GenLoop (Fin 6) X x) :
    (evalLeft X).comp ((ContinuousMap.id I).prodMap (curryLoop p).val) = cubeMap p := by
  ext z
  rfl

@[simp] theorem curryLoop_apply_zero (p : GenLoop (Fin 6) X x) (u : Fin 5 → I) :
    curryLoop p u 0 = x := by
  exact GenLoop.boundary p _ ⟨0, Or.inl (cubeCoordinates_zero _)⟩

@[simp] theorem curryLoop_apply_one (p : GenLoop (Fin 6) X x) (u : Fin 5 → I) :
    curryLoop p u 1 = x := by
  exact GenLoop.boundary p _ ⟨0, Or.inr (cubeCoordinates_zero _)⟩

end Wikipedia.HopfProblem.SixthHurewicz.CubeSubdivision
