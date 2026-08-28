import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivisionMaps

/-!
# Relative homotopies between the two triangle parametrizations

The lower product parametrization deforms directly to the lower PL triangle.
The upper product parametrization first deforms to a cone parametrization,
then to the upper PL triangle. At every intermediate time, each perimeter
edge lies on one fixed square side or on the collapsed diagonal.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

theorem subdivisionLowerProductTriangle_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionLowerProductMap u) (subdivisionLowerTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 (by simp [subdivisionLowerProductMap, h])
      (by simp [subdivisionLowerTriangleMap, h])
  · exact .one 0 (by simp [subdivisionLowerProductMap, h])
      (by simp [subdivisionLowerTriangleMap, h])
  · exact .zero 1 (by simp [subdivisionLowerProductMap, h])
      (by simp [subdivisionLowerTriangleMap, h])
  · exact .diagonal (by simp [subdivisionLowerProductMap, h])
      (by simp [subdivisionLowerTriangleMap, h,
        min_eq_left (show u 0 ≤ (1 : I) from (u 0).property.2)])

theorem subdivisionUpperProductCone_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperProductMap u) (subdivisionUpperConeMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 (by simp [subdivisionUpperProductMap, h])
      (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h])
      (by simp [subdivisionUpperConeMap, h])
  · exact .diagonal (by simp [subdivisionUpperProductMap, h])
      (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h])
      (by simp [subdivisionUpperConeMap, h])

theorem subdivisionUpperConeTriangle_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperConeMap u) (subdivisionUpperTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 (by simp [subdivisionUpperConeMap, h])
      (by simp [subdivisionUpperTriangleMap, h])
  · exact .one 1 (by simp [subdivisionUpperConeMap, h])
      (by simp [subdivisionUpperTriangleMap, h])
  · exact .diagonal (by simp [subdivisionUpperConeMap, h])
      (by simp [subdivisionUpperTriangleMap, h])
  · exact .zero 0 (by simp [subdivisionUpperConeMap, h])
      (by simp [subdivisionUpperTriangleMap, h])

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- A literal relative homotopy from the lower product square to the PL triangle. -/
def subdivisionLowerTriangleHomotopy (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    (subdivisionLowerProductLoop p hd).val.HomotopyRel
      (subdivisionLowerTriangleLoop p hd).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionLowerProductMap_based p hd)
    (subdivisionLowerTriangleMap_based p hd) subdivisionLowerProductTriangle_sides

/-- The first explicit stage of the upper triangle reparametrization. -/
def subdivisionUpperConeHomotopy (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    (subdivisionUpperProductLoop p hd).val.HomotopyRel
      (subdivisionUpperConeLoop p hd).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperProductMap_based p hd)
    (subdivisionUpperConeMap_based p hd) subdivisionUpperProductCone_sides

/-- The second explicit stage of the upper triangle reparametrization. -/
def subdivisionUpperTriangleHomotopy (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    (subdivisionUpperConeLoop p hd).val.HomotopyRel
      (subdivisionUpperTriangleLoop p hd).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperConeMap_based p hd)
    (subdivisionUpperTriangleMap_based p hd) subdivisionUpperConeTriangle_sides

theorem subdivision_toLoop_transAt (i : Fin 2) (a b : GenLoop (Fin 2) X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) =
      (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

/-- Horizontal composition in the actual path space gives the relative
homotopy between concatenated generalized loops. -/
theorem subdivision_transAt_homotopic (i : Fin 2)
    {a b c d : GenLoop (Fin 2) X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [subdivision_toLoop_transAt, subdivision_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
