import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Uncurrying actual generalized loops with a prepended inner coordinate

An outer native `n`-loop taking values in native one-loops determines a
native `(n+1)`-loop. The inner interval becomes coordinate zero, while
every outer coordinate becomes its successor. Both boundary conditions
are retained, including for actual homotopies relative to the boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

variable {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}

/-- Uncurry native one-loop-valued generalized loops, prepending the inner coordinate. -/
def uncurryLoop (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    GenLoop (Fin (n + 1)) X x :=
  ⟨⟨fun u => p (fun i => u i.succ) (fun _ => u 0), by fun_prop⟩, by
    intro u hu
    obtain ⟨i, hi⟩ := hu
    cases i using Fin.cases with
    | zero =>
        exact GenLoop.boundary (p (fun i => u i.succ)) (fun _ => u 0) ⟨0, hi⟩
    | succ j =>
        change p (fun i => u i.succ) (fun _ => u 0) = x
        rw [GenLoop.boundary p _ ⟨j, hi⟩]
        rfl⟩

@[simp] theorem uncurryLoop_apply
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) (u : Fin (n + 1) → I) :
    uncurryLoop p u = p (fun i => u i.succ) (fun _ => u 0) := rfl

@[simp] theorem uncurryLoop_const :
    uncurryLoop (GenLoop.const : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) =
      (GenLoop.const : GenLoop (Fin (n + 1)) X x) := by
  apply GenLoop.ext
  intro u
  rfl

/-- Uncurry the actual cylinder map of a homotopy relative to the outer cube boundary. -/
def uncurryLoopHomotopy
    {p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (uncurryLoop p).val.HomotopyRel (uncurryLoop q).val (Cube.boundary (Fin (n + 1))) where
  toFun z := H (z.1, fun i => z.2 i.succ) (fun _ => z.2 0)
  continuous_toFun := by fun_prop
  map_zero_left u := by
    change H (0, fun i => u i.succ) (fun _ => u 0) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    rfl
  map_one_left u := by
    change H (1, fun i => u i.succ) (fun _ => u 0) = _
    rw [ContinuousMap.HomotopyWith.apply_one]
    rfl
  prop' t u hu := by
    change H (t, fun i => u i.succ) (fun _ => u 0) = uncurryLoop p u
    rw [GenLoop.boundary (uncurryLoop p) u hu]
    obtain ⟨i, hi⟩ := hu
    cases i using Fin.cases with
    | zero =>
        exact GenLoop.boundary (H (t, fun i => u i.succ)) (fun _ => u 0) ⟨0, hi⟩
    | succ j =>
        rw [H.eq_fst t ⟨j, hi⟩]
        change p (fun i => u i.succ) (fun _ => u 0) = x
        rw [GenLoop.boundary p _ ⟨j, hi⟩]
        rfl

@[simp] theorem uncurryLoopHomotopy_apply
    {p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) (z : I × (Fin (n + 1) → I)) :
    uncurryLoopHomotopy H z = H (z.1, fun i => z.2 i.succ) (fun _ => z.2 0) := rfl

/-- The genuine native homotopy relation is preserved by uncurrying. -/
theorem uncurryLoop_homotopic
    {p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (uncurryLoop p) (uncurryLoop q) := by
  obtain ⟨H⟩ := h
  exact ⟨uncurryLoopHomotopy H⟩

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
