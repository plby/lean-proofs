import Wikipedia.HopfProblem.FifthHurewiczCube

/-!
# Evaluation on the remaining native five-cube

Currying a native six-dimensional generalized loop along coordinate
zero leaves coordinates one through five in their original order.
Evaluation on that genuine based five-loop space recovers the original
six-cube and sends the whole remaining-cube boundary to the basepoint.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz PeriodTorusHigherHomology

/-- The coordinates remaining after native currying at coordinate zero. -/
abbrev Remaining := {j : Fin 6 // j ≠ 0}

/-- The order-preserving reindexing of the remaining five cube coordinates. -/
def remainingCoordinates : C(Fin 5 → I, Remaining → I) where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp] theorem remainingCoordinates_succ (u : Fin 5 → I) (i : Fin 5) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by
  simp [remainingCoordinates]

theorem remainingCoordinates_boundary {u : Fin 5 → I} (h : u ∈ Cube.boundary (Fin 5)) :
    remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

variable {X : Type} [TopologicalSpace X]

/-- The actual five-coordinate based generalized-loop space. -/
abbrev BasedLoopSpace (x : X) := GenLoop Remaining X x

/-- Joint continuous evaluation on the genuine remaining cube. -/
def evaluation (x : X) : C(BasedLoopSpace x × (Fin 5 → I), X) where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp] theorem evaluation_apply (x : X) (p : BasedLoopSpace x) (u : Fin 5 → I) :
    evaluation x (p, u) = p (remainingCoordinates u) := rfl

theorem evaluation_boundary (x : X) (p : BasedLoopSpace x) (u : Fin 5 → I)
    (hu : u ∈ Cube.boundary (Fin 5)) : evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

@[simp] theorem evaluation_const (x : X) (u : Fin 5 → I) :
    evaluation x (GenLoop.const, u) = x := rfl

/-- Any continuous map into the remaining cube boundary evaluates constantly. -/
theorem evaluation_comp_boundary {A : Type} [TopologicalSpace A]
    (x : X) (f : C(A, Fin 5 → I)) (hf : ∀ a, f a ∈ Cube.boundary (Fin 5)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × A) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

/-- Product interval-five-cube coordinates on Mathlib's literal six-cube. -/
def cubeCoordinates : C(I × (Fin 5 → I), Fin 6 → I) where
  toFun z := Cube.insertAt (0 : Fin 6) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp] theorem cubeCoordinates_zero (z : I × (Fin 5 → I)) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp] theorem cubeCoordinates_succ (z : I × (Fin 5 → I)) (i : Fin 5) :
    cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply,
    remainingCoordinates]

@[simp] theorem cubeCoordinates_one (z : I × (Fin 5 → I)) :
    cubeCoordinates z 1 = z.2 0 := cubeCoordinates_succ z 0

@[simp] theorem cubeCoordinates_two (z : I × (Fin 5 → I)) :
    cubeCoordinates z 2 = z.2 1 := cubeCoordinates_succ z 1

@[simp] theorem cubeCoordinates_three (z : I × (Fin 5 → I)) :
    cubeCoordinates z 3 = z.2 2 := cubeCoordinates_succ z 2

@[simp] theorem cubeCoordinates_four (z : I × (Fin 5 → I)) :
    cubeCoordinates z 4 = z.2 3 := cubeCoordinates_succ z 3

@[simp] theorem cubeCoordinates_five (z : I × (Fin 5 → I)) :
    cubeCoordinates z 5 = z.2 4 := cubeCoordinates_succ z 4

theorem cubeCoordinates_surjective : Function.Surjective cubeCoordinates := by
  intro z
  refine ⟨(z 0, fun i => z i.succ), ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact cubeCoordinates_zero _
  · exact cubeCoordinates_succ _ j

/-- The original generalized loop on the first interval times its remaining cube. -/
def cubeMap {x : X} (p : GenLoop (Fin 6) X x) : C(I × (Fin 5 → I), X) :=
  p.val.comp cubeCoordinates

theorem evaluation_toLoop {x : X} (p : GenLoop (Fin 6) X x) (s : I) (u : Fin 5 → I) :
    evaluation x (GenLoop.toLoop (0 : Fin 6) p s, u) = cubeMap p (s, u) := rfl

theorem evaluation_comp_toLoop {x : X} (p : GenLoop (Fin 6) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 6) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 5 → I))) = cubeMap p := by
  ext z
  rfl

end Wikipedia.HopfProblem.SixthHurewicz
