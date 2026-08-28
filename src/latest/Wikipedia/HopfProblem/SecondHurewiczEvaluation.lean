import Wikipedia.HopfProblem.SecondHurewiczCrossUnits
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Evaluation of native generalized loops on an actual square

Mathlib curries a two-dimensional generalized loop along coordinate zero.
Evaluating the remaining coordinate identifies the resulting family with
the original map on the entire two-dimensional unit cube.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz

open FirstHurewicz PeriodTorusHigherHomology

/-- The actual remaining coordinate in Mathlib's `GenLoop.toLoop 0`. -/
abbrev Remaining := {j : Fin 2 // j ≠ 0}

variable {X : Type} [TopologicalSpace X]

/-- A native generalized loop space, with its inherited compact-open topology. -/
abbrev BasedLoopSpace (x : X) := GenLoop Remaining X x

/-- Joint continuous evaluation of the remaining interval coordinate. -/
def evaluation (x : X) : C(BasedLoopSpace x × I, X) where
  toFun z := z.1 (fun _ => z.2)
  continuous_toFun := by fun_prop

@[simp] theorem evaluation_apply (x : X) (p : BasedLoopSpace x) (t : I) :
    evaluation x (p, t) = p (fun _ => t) := rfl

@[simp] theorem evaluation_zero (x : X) (p : BasedLoopSpace x) :
    evaluation x (p, 0) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inl rfl⟩

@[simp] theorem evaluation_one (x : X) (p : BasedLoopSpace x) :
    evaluation x (p, 1) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inr rfl⟩

@[simp] theorem evaluation_const (x : X) (t : I) :
    evaluation x (GenLoop.const, t) = x := rfl

@[simp] theorem evaluation_comp_right_zero (x : X) :
    (evaluation x).comp (crossInsertRight (0 : I)) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_zero x p

@[simp] theorem evaluation_comp_right_one (x : X) :
    (evaluation x).comp (crossInsertRight (1 : I)) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_one x p

/-- The product-square coordinates on Mathlib's literal `Fin 2` unit cube. -/
def squareCoordinates : C(I × I, Fin 2 → I) where
  toFun z := Cube.insertAt (0 : Fin 2) (z.1, fun _ => z.2)
  continuous_toFun := by fun_prop

@[simp] theorem squareCoordinates_zero (z : I × I) :
    squareCoordinates z 0 = z.1 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp] theorem squareCoordinates_one (z : I × I) :
    squareCoordinates z 1 = z.2 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

theorem squareCoordinates_surjective : Function.Surjective squareCoordinates := by
  intro z
  refine ⟨(z 0, z 1), ?_⟩
  funext i
  fin_cases i <;> simp

/-- The original generalized loop written on the ordinary product square. -/
def squareMap {x : X} (p : GenLoop (Fin 2) X x) : C(I × I, X) :=
  p.val.comp squareCoordinates

theorem evaluation_toLoop {x : X} (p : GenLoop (Fin 2) X x) (s t : I) :
    evaluation x (GenLoop.toLoop (0 : Fin 2) p s, t) = squareMap p (s, t) := rfl

theorem evaluation_comp_toLoop {x : X} (p : GenLoop (Fin 2) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 2) p).toContinuousMap.prodMap (ContinuousMap.id I)) =
      squareMap p := by
  ext z
  rfl

end Wikipedia.HopfProblem.SecondHurewicz
