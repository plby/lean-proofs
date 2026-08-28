import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexStage

/-!
# Extending coherent vertex normalization to the next dimension

The actual extension preserves the bottom map, sends every terminal vertex
to the base point, and has the prescribed lower-dimensional homotopy on
each face. The coface identities supply compatibility for the next step.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}

theorem vertexStepHomotopy_face (D : VertexHomotopyData x n) :
    FaceCompatibleHomotopies n D.homotopy (vertexStepHomotopy D) := by
  intro smp i
  ext u
  exact vertexStepHomotopy_face_apply D smp i u.1 u.2

theorem vertexStepHomotopy_one_verticesBased (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 1), X)) :
    VerticesBased x (n + 1) (timeSlice (vertexStepHomotopy D smp) 1) := by
  intro k
  obtain ⟨i, j, hij⟩ := simplexVertex_exists_face n k
  change vertexStepHomotopy D smp (1, stdSimplex.vertex k) = x
  rw [← hij, vertexStepHomotopy_face_apply]
  exact D.one_verticesBased (smp.comp (simplexFace n i)) j

/-- The constructed homotopies agree on all geometric overlaps when used
as the faces of one still higher-dimensional simplex. -/
theorem vertexStepHomotopy_faceCompatible (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 2), X)) :
    FaceCompatible (fun i => vertexStepHomotopy D (smp.comp (simplexFace (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij r u
  rw [vertexStepHomotopy_face_apply, vertexStepHomotopy_face_apply,
    PeriodTorusLineBundle.ChernCocycle.singularSimplex_face_face smp hij]

/-- The next stage is constructed, not postulated. -/
def VertexHomotopyData.next (D : VertexHomotopyData x n) : VertexHomotopyData x (n + 1) where
  homotopy := vertexStepHomotopy D
  zero := vertexStepHomotopy_zero D
  one_verticesBased := vertexStepHomotopy_one_verticesBased D
  of_verticesBased := vertexStepHomotopy_of_verticesBased D
  face_compatible := vertexStepHomotopy_faceCompatible D

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
