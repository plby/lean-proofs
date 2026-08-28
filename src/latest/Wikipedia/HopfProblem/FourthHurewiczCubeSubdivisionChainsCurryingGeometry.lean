import Wikipedia.HopfProblem.FourthHurewiczEvaluation

/-!
# Currying a native four-cube into the continuous interval-map space

The remaining three cube coordinates form an actual based generalized
loop in the compact-open space of continuous interval maps. Evaluation
recovers the original four-cube without changing any coordinates.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

/-- A boundary point in the remaining cube is still on the native four-cube boundary. -/
theorem cubeCoordinates_boundary_right (s : I) {u : Fin 3 → I}
    (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeCoordinates (s, u) ∈ Cube.boundary (Fin 4) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa only [cubeCoordinates_succ] using hi⟩

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The actual curried based three-loop, retaining the first interval as its value variable. -/
def curryLoop (p : GenLoop (Fin 4) X x) :
    GenLoop (Fin 3) C(I, X) (ContinuousMap.const I x) :=
  ⟨((cubeMap p).comp ContinuousMap.prodSwap).curry, by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (cubeCoordinates_boundary_right s hu)⟩

@[simp] theorem curryLoop_apply (p : GenLoop (Fin 4) X x) (u : Fin 3 → I) (s : I) :
    curryLoop p u s = p (cubeCoordinates (s, u)) := rfl

/-- Joint continuous evaluation, with the interval in the first product factor. -/
def evalLeft (X : Type) [TopologicalSpace X] : C(I × C(I, X), X) where
  toFun z := z.2 z.1
  continuous_toFun := by fun_prop

@[simp] theorem evalLeft_apply (s : I) (f : C(I, X)) :
    evalLeft X (s, f) = f s := rfl

/-- Evaluating the actual curried loop recovers the original product-coordinate cube map. -/
theorem evalLeft_comp_curryLoop (p : GenLoop (Fin 4) X x) :
    (evalLeft X).comp ((ContinuousMap.id I).prodMap (curryLoop p).val) = cubeMap p := by
  ext z
  rfl

@[simp] theorem curryLoop_apply_zero (p : GenLoop (Fin 4) X x) (u : Fin 3 → I) :
    curryLoop p u 0 = x := by
  exact GenLoop.boundary p _ ⟨0, Or.inl (cubeCoordinates_zero _)⟩

@[simp] theorem curryLoop_apply_one (p : GenLoop (Fin 4) X x) (u : Fin 3 → I) :
    curryLoop p u 1 = x := by
  exact GenLoop.boundary p _ ⟨0, Or.inr (cubeCoordinates_zero _)⟩

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
