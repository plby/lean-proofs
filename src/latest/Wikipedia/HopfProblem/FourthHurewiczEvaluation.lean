import Wikipedia.HopfProblem.ThirdHurewiczCube

/-!
# Evaluation on the remaining native three-cube

Currying a native four-dimensional generalized loop along coordinate zero
leaves coordinates one, two, and three, in that order. Actual evaluation
on the resulting based three-loop space recovers the original four-cube
and sends every boundary point of the remaining cube to the basepoint.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz PeriodTorusHigherHomology

/-- The coordinates remaining after currying at native coordinate zero. -/
abbrev Remaining := {j : Fin 4 // j ≠ 0}

/-- The order-preserving reindexing of the remaining three cube coordinates. -/
def remainingCoordinates : C(Fin 3 → I, Remaining → I) where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp] theorem remainingCoordinates_succ (u : Fin 3 → I) (i : Fin 3) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by
  simp [remainingCoordinates]

theorem remainingCoordinates_boundary {u : Fin 3 → I} (h : u ∈ Cube.boundary (Fin 3)) :
    remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

variable {X : Type} [TopologicalSpace X]

/-- The actual three-coordinate based generalized-loop space. -/
abbrev BasedLoopSpace (x : X) := GenLoop Remaining X x

/-- Joint continuous evaluation of the genuine remaining cube. -/
def evaluation (x : X) : C(BasedLoopSpace x × (Fin 3 → I), X) where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp] theorem evaluation_apply (x : X) (p : BasedLoopSpace x) (u : Fin 3 → I) :
    evaluation x (p, u) = p (remainingCoordinates u) := rfl

theorem evaluation_boundary (x : X) (p : BasedLoopSpace x) (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) : evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

@[simp] theorem evaluation_const (x : X) (u : Fin 3 → I) :
    evaluation x (GenLoop.const, u) = x := rfl

/-- Every continuous map into the remaining cube boundary evaluates constantly. -/
theorem evaluation_comp_boundary {A : Type} [TopologicalSpace A]
    (x : X) (f : C(A, Fin 3 → I)) (hf : ∀ a, f a ∈ Cube.boundary (Fin 3)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × A) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

/-- Product interval-three-cube coordinates on Mathlib's literal four-cube. -/
def cubeCoordinates : C(I × (Fin 3 → I), Fin 4 → I) where
  toFun z := Cube.insertAt (0 : Fin 4) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp] theorem cubeCoordinates_zero (z : I × (Fin 3 → I)) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp] theorem cubeCoordinates_succ (z : I × (Fin 3 → I)) (i : Fin 3) :
    cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply,
    remainingCoordinates]

@[simp] theorem cubeCoordinates_one (z : I × (Fin 3 → I)) :
    cubeCoordinates z 1 = z.2 0 := cubeCoordinates_succ z 0

@[simp] theorem cubeCoordinates_two (z : I × (Fin 3 → I)) :
    cubeCoordinates z 2 = z.2 1 := cubeCoordinates_succ z 1

@[simp] theorem cubeCoordinates_three (z : I × (Fin 3 → I)) :
    cubeCoordinates z 3 = z.2 2 := cubeCoordinates_succ z 2

theorem cubeCoordinates_surjective : Function.Surjective cubeCoordinates := by
  intro z
  refine ⟨(z 0, fun i => z i.succ), ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact cubeCoordinates_zero _
  · exact cubeCoordinates_succ _ j

/-- The original generalized loop on the first interval times its remaining cube. -/
def cubeMap {x : X} (p : GenLoop (Fin 4) X x) : C(I × (Fin 3 → I), X) :=
  p.val.comp cubeCoordinates

theorem evaluation_toLoop {x : X} (p : GenLoop (Fin 4) X x) (s : I) (u : Fin 3 → I) :
    evaluation x (GenLoop.toLoop (0 : Fin 4) p s, u) = cubeMap p (s, u) := rfl

theorem evaluation_comp_toLoop {x : X} (p : GenLoop (Fin 4) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 4) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 3 → I))) = cubeMap p := by
  ext z
  rfl

end Wikipedia.HopfProblem.FourthHurewicz
