import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceCompatibility
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtension
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators

/-!
# One stage of coherent vertex normalization

The data in this internal inductive construction consists of genuine
continuous simplex homotopies and their proved endpoint, fixed-simplex,
and face-pasting properties. The next stage is constructed by the actual
boundary homotopy extension theorem.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

/-- Data maintained by the inductive construction of vertex normalization. -/
structure VertexHomotopyData (x : X) (n : ℕ) where
  homotopy : C(Simplex n, X) → C(I × Simplex n, X)
  zero : ∀ (smp : C(Simplex n, X)) (s : Simplex n), homotopy smp (0, s) = smp s
  one_verticesBased : ∀ smp, VerticesBased x n (timeSlice (homotopy smp) 1)
  of_verticesBased : ∀ smp, VerticesBased x n smp →
    homotopy smp = smp.comp (ContinuousMap.snd : C(I × Simplex n, Simplex n))
  face_compatible : ∀ smp : C(Simplex (n + 1), X),
    FaceCompatible (fun i => homotopy (smp.comp (simplexFace n i)))

variable {x : X} {n : ℕ}

/-- The actual boundary homotopy prescribed by all normalized lower faces. -/
def vertexBoundaryHomotopy (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 1), X)) : C(I × SimplexBoundary (n + 1), X) :=
  glueFaceHomotopies (fun i => D.homotopy (smp.comp (simplexFace n i)))
    (D.face_compatible smp)

@[simp] theorem vertexBoundaryHomotopy_face (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 1), X)) (i : Fin (n + 2)) (r : I) (s : Simplex n) :
    vertexBoundaryHomotopy D smp (r, simplexFaceBoundary n i s) =
      D.homotopy (smp.comp (simplexFace n i)) (r, s) :=
  glueFaceHomotopies_face _ _ i r s

@[simp] theorem vertexBoundaryHomotopy_zero (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 1), X)) (s : SimplexBoundary (n + 1)) :
    vertexBoundaryHomotopy D smp (0, s) = smp s.val :=
  glueFaceHomotopies_zero _ _ smp (fun i t => D.zero (smp.comp (simplexFace n i)) t) s

/-- Extend the lower-dimensional vertex homotopies, leaving already-based
simplices literally independent of time. -/
def vertexStepHomotopy (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 1), X)) : C(I × Simplex (n + 1), X) := by
  classical
  exact if VerticesBased x (n + 1) smp then
    smp.comp (ContinuousMap.snd : C(I × Simplex (n + 1), Simplex (n + 1)))
  else extendBoundaryHomotopy smp (vertexBoundaryHomotopy D smp)
    (vertexBoundaryHomotopy_zero D smp)

theorem vertexStepHomotopy_of_verticesBased (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 1), X)) (h : VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      smp.comp (ContinuousMap.snd : C(I × Simplex (n + 1), Simplex (n + 1))) := by
  classical
  simp only [vertexStepHomotopy, if_pos h]

theorem vertexStepHomotopy_of_not_verticesBased (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 1), X)) (h : ¬ VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      extendBoundaryHomotopy smp (vertexBoundaryHomotopy D smp)
        (vertexBoundaryHomotopy_zero D smp) := by
  classical
  simp only [vertexStepHomotopy, if_neg h]

@[simp] theorem vertexStepHomotopy_zero (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 1), X)) (s : Simplex (n + 1)) :
    vertexStepHomotopy D smp (0, s) = smp s := by
  classical
  by_cases h : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp h]
    rfl
  · rw [vertexStepHomotopy_of_not_verticesBased D smp h]
    exact extendBoundaryHomotopy_bottom _ _ _ s

/-- Both branches have exactly the already-constructed lower face homotopy. -/
theorem vertexStepHomotopy_face_apply (D : VertexHomotopyData x n)
    (smp : C(Simplex (n + 1), X)) (i : Fin (n + 2)) (r : I) (s : Simplex n) :
    vertexStepHomotopy D smp (r, simplexFace n i s) =
      D.homotopy (smp.comp (simplexFace n i)) (r, s) := by
  classical
  by_cases h : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp h,
      D.of_verticesBased _ (h.face i)]
    rfl
  · rw [vertexStepHomotopy_of_not_verticesBased D smp h,
      extendBoundaryHomotopy_face]
    exact vertexBoundaryHomotopy_face D smp i r s

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
