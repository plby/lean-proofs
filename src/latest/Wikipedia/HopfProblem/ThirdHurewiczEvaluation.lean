import Wikipedia.HopfProblem.SecondHurewiczSquare

/-!
# Evaluation of the two remaining native cube coordinates

Currying along coordinate zero leaves coordinates one and two, in that
order. Evaluation on this genuine based two-loop space recovers the
original native three-dimensional cube, and every side of the remaining
square evaluates to the basepoint.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz PeriodTorusHigherHomology

/-- The coordinates remaining after native currying at coordinate zero. -/
abbrev Remaining := {j : Fin 3 // j ≠ 0}

/-- The order-preserving identification of the remaining square coordinates. -/
def remainingCoordinates : C(Fin 2 → I, Remaining → I) where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp] theorem remainingCoordinates_succ (u : Fin 2 → I) (i : Fin 2) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by
  simp [remainingCoordinates]

theorem remainingCoordinates_boundary {u : Fin 2 → I} (h : u ∈ Cube.boundary (Fin 2)) :
    remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

variable {X : Type} [TopologicalSpace X]

/-- The actual remaining two-coordinate generalized-loop space. -/
abbrev BasedLoopSpace (x : X) := GenLoop Remaining X x

/-- Joint continuous evaluation on the remaining square. -/
def evaluation (x : X) : C(BasedLoopSpace x × (Fin 2 → I), X) where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp] theorem evaluation_apply (x : X) (p : BasedLoopSpace x) (u : Fin 2 → I) :
    evaluation x (p, u) = p (remainingCoordinates u) := rfl

theorem evaluation_boundary (x : X) (p : BasedLoopSpace x) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) : evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

@[simp] theorem evaluation_const (x : X) (u : Fin 2 → I) :
    evaluation x (GenLoop.const, u) = x := rfl

/-- A map into the boundary of the remaining square evaluates constantly. -/
theorem evaluation_comp_boundary (x : X) (f : C(I, Fin 2 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × I) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

/-- The product interval-square coordinates on Mathlib's literal cube. -/
def cubeCoordinates : C(I × (Fin 2 → I), Fin 3 → I) where
  toFun z := Cube.insertAt (0 : Fin 3) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp] theorem cubeCoordinates_zero (z : I × (Fin 2 → I)) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp] theorem cubeCoordinates_succ (z : I × (Fin 2 → I)) (i : Fin 2) :
    cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply,
    remainingCoordinates]

@[simp] theorem cubeCoordinates_one (z : I × (Fin 2 → I)) :
    cubeCoordinates z 1 = z.2 0 := cubeCoordinates_succ z 0

@[simp] theorem cubeCoordinates_two (z : I × (Fin 2 → I)) :
    cubeCoordinates z 2 = z.2 1 := cubeCoordinates_succ z 1

theorem cubeCoordinates_surjective : Function.Surjective cubeCoordinates := by
  intro z
  refine ⟨(z 0, fun i => z i.succ), ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact cubeCoordinates_zero _
  · exact cubeCoordinates_succ _ j

/-- The original native generalized loop on the interval times its remaining square. -/
def cubeMap {x : X} (p : GenLoop (Fin 3) X x) : C(I × (Fin 2 → I), X) :=
  p.val.comp cubeCoordinates

theorem evaluation_toLoop {x : X} (p : GenLoop (Fin 3) X x) (s : I) (u : Fin 2 → I) :
    evaluation x (GenLoop.toLoop (0 : Fin 3) p s, u) = cubeMap p (s, u) := rfl

theorem evaluation_comp_toLoop {x : X} (p : GenLoop (Fin 3) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 3) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 2 → I))) = cubeMap p := by
  ext z
  rfl

end Wikipedia.HopfProblem.ThirdHurewicz
