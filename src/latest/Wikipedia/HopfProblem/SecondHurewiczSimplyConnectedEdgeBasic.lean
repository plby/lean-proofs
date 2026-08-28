import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPaths
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceCompatibility
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtension

/-!
# Endpoint-fixed straightening of singular edges

An edge whose endpoints are the base point is contracted by an actual
endpoint-fixed nullhomotopy. Other edges are left unchanged. Thus every
edge homotopy fixes its original vertices, on every singular simplex.
This total construction can be extended coherently to higher simplices.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

/-- The literal time-independent homotopy of a singular simplex. -/
def stationarySimplexHomotopy (n : ℕ) (smp : C(Simplex n, X)) :
    C(I × Simplex n, X) := smp.comp (ContinuousMap.snd : C(I × Simplex n, Simplex n))

@[simp] theorem stationarySimplexHomotopy_apply (n : ℕ) (smp : C(Simplex n, X))
    (t : I) (s : Simplex n) : stationarySimplexHomotopy n smp (t, s) = smp s := rfl

@[simp] theorem timeSlice_stationarySimplexHomotopy (n : ℕ)
    (smp : C(Simplex n, X)) (t : I) :
    timeSlice (stationarySimplexHomotopy n smp) t = smp := rfl

variable [SimplyConnectedSpace X]

/-- A total edge homotopy; only edges with both endpoints at the base point
are contracted, and every vertex remains fixed. -/
def edgeStraighteningHomotopy (x : X) (smp : C(Simplex 1, X)) :
    C(I × Simplex 1, X) := by
  classical
  exact if h : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x ∧
      smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x then
    edgeNullHomotopy x smp h.1 h.2 else stationarySimplexHomotopy 1 smp

@[simp] theorem edgeStraighteningHomotopy_zero (x : X) (smp : C(Simplex 1, X))
    (s : Simplex 1) : edgeStraighteningHomotopy x smp (0, s) = smp s := by
  classical
  unfold edgeStraighteningHomotopy
  split
  · exact edgeNullHomotopy_zero x smp _ _ s
  · rfl

theorem edgeStraighteningHomotopy_one (x : X) (smp : C(Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x)
    (s : Simplex 1) : edgeStraighteningHomotopy x smp (1, s) = x := by
  classical
  have h : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x ∧
      smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x := ⟨h₀, h₁⟩
  rw [edgeStraighteningHomotopy, dif_pos h]
  exact edgeNullHomotopy_one x smp _ _ s

/-- Vertex fixing holds even when the edge does not have based endpoints. -/
theorem edgeStraighteningHomotopy_vertex (x : X) (smp : C(Simplex 1, X))
    (i : Fin 2) (t : I) :
    edgeStraighteningHomotopy x smp (t, stdSimplex.vertex (S := ℝ) i) =
      smp (stdSimplex.vertex (S := ℝ) i) := by
  classical
  unfold edgeStraighteningHomotopy
  split
  · rename_i h
    fin_cases i
    · exact (edgeNullHomotopy_vertex_zero x smp h.1 h.2 t).trans h.1.symm
    · exact (edgeNullHomotopy_vertex_one x smp h.1 h.2 t).trans h.2.symm
  · rfl

@[simp] theorem edgeStraighteningHomotopy_const (x : X) :
    edgeStraighteningHomotopy x (ContinuousMap.const (Simplex 1) x) =
      ContinuousMap.const (I × Simplex 1) x := by
  classical
  simp only [edgeStraighteningHomotopy, ContinuousMap.const_apply]
  exact edgeNullHomotopy_const x

/-- The vertex-fixed edge homotopies are literally compatible with faces. -/
theorem edgeStraighteningHomotopy_face (x : X) :
    FaceCompatibleHomotopies 0 (stationarySimplexHomotopy 0)
      (edgeStraighteningHomotopy x) := by
  intro smp i
  ext u
  rcases u with ⟨t, s⟩
  change edgeStraighteningHomotopy x smp (t, simplexFace 0 i s) =
    smp (simplexFace 0 i s)
  rw [simplexZero_eq_vertex s, simplexFace_vertex]
  exact edgeStraighteningHomotopy_vertex x smp _ t

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
