import Wikipedia.HopfProblem.SixthHurewiczCube

/-!
# Evaluation on the remaining native six-cube

Currying a native seven-dimensional generalized loop along coordinate
zero leaves coordinates one through six in their original order.
Evaluation on that genuine based six-loop space recovers the original
seven-cube and sends the whole remaining-cube boundary to the basepoint.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz PeriodTorusHigherHomology

/-- The coordinates remaining after native currying at coordinate zero. -/
abbrev Remaining := {j : Fin 7 // j ≠ 0}

/-- The order-preserving reindexing of the remaining six cube coordinates. -/
def remainingCoordinates : C(Fin 6 → I, Remaining → I) where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp] theorem remainingCoordinates_succ (u : Fin 6 → I) (i : Fin 6) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by
  simp [remainingCoordinates]

theorem remainingCoordinates_boundary {u : Fin 6 → I} (h : u ∈ Cube.boundary (Fin 6)) :
    remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

variable {X : Type} [TopologicalSpace X]

/-- The actual six-coordinate based generalized-loop space. -/
abbrev BasedLoopSpace (x : X) := GenLoop Remaining X x

/-- Joint continuous evaluation on the genuine remaining cube. -/
def evaluation (x : X) : C(BasedLoopSpace x × (Fin 6 → I), X) where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp] theorem evaluation_apply (x : X) (p : BasedLoopSpace x) (u : Fin 6 → I) :
    evaluation x (p, u) = p (remainingCoordinates u) := rfl

theorem evaluation_boundary (x : X) (p : BasedLoopSpace x) (u : Fin 6 → I)
    (hu : u ∈ Cube.boundary (Fin 6)) : evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

@[simp] theorem evaluation_const (x : X) (u : Fin 6 → I) :
    evaluation x (GenLoop.const, u) = x := rfl

/-- Any continuous map into the remaining cube boundary evaluates constantly. -/
theorem evaluation_comp_boundary {A : Type} [TopologicalSpace A]
    (x : X) (f : C(A, Fin 6 → I)) (hf : ∀ a, f a ∈ Cube.boundary (Fin 6)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × A) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

/-- Product interval-six-cube coordinates on Mathlib's literal seven-cube. -/
def cubeCoordinates : C(I × (Fin 6 → I), Fin 7 → I) where
  toFun z := Cube.insertAt (0 : Fin 7) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp] theorem cubeCoordinates_zero (z : I × (Fin 6 → I)) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp] theorem cubeCoordinates_succ (z : I × (Fin 6 → I)) (i : Fin 6) :
    cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply,
    remainingCoordinates]


theorem cubeCoordinates_surjective : Function.Surjective cubeCoordinates := by
  intro z
  refine ⟨(z 0, fun i => z i.succ), ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact cubeCoordinates_zero _
  · exact cubeCoordinates_succ _ j

/-- The original generalized loop on the first interval times its remaining cube. -/
def cubeMap {x : X} (p : GenLoop (Fin 7) X x) : C(I × (Fin 6 → I), X) :=
  p.val.comp cubeCoordinates

theorem evaluation_toLoop {x : X} (p : GenLoop (Fin 7) X x) (s : I) (u : Fin 6 → I) :
    evaluation x (GenLoop.toLoop (0 : Fin 7) p s, u) = cubeMap p (s, u) := rfl

theorem evaluation_comp_toLoop {x : X} (p : GenLoop (Fin 7) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 7) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 6 → I))) = cubeMap p := by
  ext z
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
