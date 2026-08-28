import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexOrientationCubeBasic

/-!
# Embedded quarter turns of the native three-cube

The previously constructed perimeter-preserving square homotopy is embedded
in each of two coordinate planes, leaving the third coordinate unchanged.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open SecondHurewicz.SimplyConnected

theorem cubeInsert01_boundary (a : Fin 2 → I) (b : I)
    (ha : a ∈ Cube.boundary (Fin 2)) : ![a 0, a 1, b] ∈ Cube.boundary (Fin 3) := by
  rcases ha with ⟨i, hi⟩
  fin_cases i
  · exact ⟨0, by simpa using hi⟩
  · exact ⟨1, by simpa using hi⟩

theorem cubeInsert12_boundary (a : I) (b : Fin 2 → I)
    (hb : b ∈ Cube.boundary (Fin 2)) : ![a, b 0, b 1] ∈ Cube.boundary (Fin 3) := by
  rcases hb with ⟨i, hi⟩
  fin_cases i
  · exact ⟨1, by simpa using hi⟩
  · exact ⟨2, by simpa using hi⟩

/-- The square rotation homotopy in coordinates zero and one. -/
def cubeQuarter01HomotopyMap : C(I × (Fin 3 → I), Fin 3 → I) where
  toFun z := ![quarterTurnHomotopyMap (z.1, ![z.2 0, z.2 1]) 0,
    quarterTurnHomotopyMap (z.1, ![z.2 0, z.2 1]) 1, z.2 2]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem cubeQuarter01HomotopyMap_zero (u : Fin 3 → I) :
    cubeQuarter01HomotopyMap (0, u) = u := by
  funext i
  fin_cases i <;> simp [cubeQuarter01HomotopyMap]

@[simp] theorem cubeQuarter01HomotopyMap_one (u : Fin 3 → I) :
    cubeQuarter01HomotopyMap (1, u) = ![u 1, σ (u 0), u 2] := by
  funext i
  fin_cases i <;> simp [cubeQuarter01HomotopyMap]

theorem cubeQuarter01HomotopyMap_boundary (t : I) (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeQuarter01HomotopyMap (t, u) ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · exact cubeInsert01_boundary _ _ (quarterTurnHomotopyMap_boundary t
      (![u 0, u 1]) ⟨0, by simpa using hi⟩)
  · exact cubeInsert01_boundary _ _ (quarterTurnHomotopyMap_boundary t
      (![u 0, u 1]) ⟨1, by simpa using hi⟩)
  · exact ⟨2, by simpa [cubeQuarter01HomotopyMap] using hi⟩

/-- The square rotation homotopy in coordinates one and two. -/
def cubeQuarter12HomotopyMap : C(I × (Fin 3 → I), Fin 3 → I) where
  toFun z := ![z.2 0, quarterTurnHomotopyMap (z.1, ![z.2 1, z.2 2]) 0,
    quarterTurnHomotopyMap (z.1, ![z.2 1, z.2 2]) 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem cubeQuarter12HomotopyMap_zero (u : Fin 3 → I) :
    cubeQuarter12HomotopyMap (0, u) = u := by
  funext i
  fin_cases i <;> simp [cubeQuarter12HomotopyMap]

@[simp] theorem cubeQuarter12HomotopyMap_one (u : Fin 3 → I) :
    cubeQuarter12HomotopyMap (1, u) = ![u 0, u 2, σ (u 1)] := by
  funext i
  fin_cases i <;> simp [cubeQuarter12HomotopyMap]

theorem cubeQuarter12HomotopyMap_boundary (t : I) (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeQuarter12HomotopyMap (t, u) ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · exact ⟨0, by simpa [cubeQuarter12HomotopyMap] using hi⟩
  · exact cubeInsert12_boundary _ _ (quarterTurnHomotopyMap_boundary t
      (![u 1, u 2]) ⟨0, by simpa using hi⟩)
  · exact cubeInsert12_boundary _ _ (quarterTurnHomotopyMap_boundary t
      (![u 1, u 2]) ⟨1, by simpa using hi⟩)

/-- Two embedded quarter turns produce the positive three-coordinate cycle. -/
def cubeThirdCycleHomotopyMap : C(I × (Fin 3 → I), Fin 3 → I) :=
  cubeQuarter12HomotopyMap.comp
    ⟨fun z => (z.1, cubeQuarter01HomotopyMap z), by fun_prop⟩

@[simp] theorem cubeThirdCycleHomotopyMap_zero (u : Fin 3 → I) :
    cubeThirdCycleHomotopyMap (0, u) = u := by
  change cubeQuarter12HomotopyMap (0, cubeQuarter01HomotopyMap (0, u)) = u
  rw [cubeQuarter01HomotopyMap_zero, cubeQuarter12HomotopyMap_zero]

@[simp] theorem cubeThirdCycleHomotopyMap_one (u : Fin 3 → I) :
    cubeThirdCycleHomotopyMap (1, u) = cubeThirdCycle u := by
  change cubeQuarter12HomotopyMap (1, cubeQuarter01HomotopyMap (1, u)) = _
  rw [cubeQuarter01HomotopyMap_one, cubeQuarter12HomotopyMap_one]
  simp

theorem cubeThirdCycleHomotopyMap_boundary (t : I) (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeThirdCycleHomotopyMap (t, u) ∈ Cube.boundary (Fin 3) :=
  cubeQuarter12HomotopyMap_boundary t _ (cubeQuarter01HomotopyMap_boundary t u hu)

end Wikipedia.HopfProblem.ThirdHurewicz
