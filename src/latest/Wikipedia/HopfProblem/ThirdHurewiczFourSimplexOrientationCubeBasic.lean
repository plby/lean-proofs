import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronRotation

/-!
# Native three-cube coordinate permutations

These are actual continuous cube maps and their pullbacks on generalized
loops. Their homotopy signs are proved separately by embedded square rotations.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

/-- The positive three-cycle of the cube coordinates. -/
def cubeThirdCycle : C(Fin 3 → I, Fin 3 → I) where
  toFun u := ![u 1, u 2, u 0]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem cubeThirdCycle_apply (u : Fin 3 → I) :
    cubeThirdCycle u = ![u 1, u 2, u 0] := rfl

theorem cubeThirdCycle_boundary (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeThirdCycle u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · exact ⟨2, by simpa using hi⟩
  · exact ⟨0, by simpa using hi⟩
  · exact ⟨1, by simpa using hi⟩

/-- A three-cycle followed by reversal of the last output coordinate. -/
def cubeThirdCyclicReverse : C(Fin 3 → I, Fin 3 → I) where
  toFun u := ![u 1, u 2, σ (u 0)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem cubeThirdCyclicReverse_apply (u : Fin 3 → I) :
    cubeThirdCyclicReverse u = ![u 1, u 2, σ (u 0)] := rfl

theorem cubeThirdCyclicReverse_boundary (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeThirdCyclicReverse u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · change u 0 = 0 ∨ u 0 = 1 at hi
    rcases hi with hi | hi
    · exact ⟨2, Or.inr (by simp [hi])⟩
    · exact ⟨2, Or.inl (by simp [hi])⟩
  · exact ⟨0, by simpa using hi⟩
  · exact ⟨1, by simpa using hi⟩

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The original generalized loop precomposed with the three-cycle. -/
def cyclicThreeLoop (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp cubeThirdCycle, fun u hu => p.property _ (cubeThirdCycle_boundary u hu)⟩

@[simp] theorem cyclicThreeLoop_apply (p : GenLoop (Fin 3) X x) (u : Fin 3 → I) :
    cyclicThreeLoop p u = p ![u 1, u 2, u 0] := rfl

/-- The original generalized loop precomposed with the cycle and reflection. -/
def cyclicReverseThreeLoop (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp cubeThirdCyclicReverse,
    fun u hu => p.property _ (cubeThirdCyclicReverse_boundary u hu)⟩

@[simp] theorem cyclicReverseThreeLoop_apply (p : GenLoop (Fin 3) X x)
    (u : Fin 3 → I) : cyclicReverseThreeLoop p u = p ![u 1, u 2, σ (u 0)] := rfl

end Wikipedia.HopfProblem.ThirdHurewicz
