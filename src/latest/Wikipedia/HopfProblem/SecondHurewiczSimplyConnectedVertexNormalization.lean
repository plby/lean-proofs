import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexStep
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPaths

/-!
# Coherent vertex normalization in every simplex dimension

Actual chosen paths normalize zero-simplices. Inductively, the proved
finite-face pasting and simplex homotopy extension constructions extend
the normalization to every dimension. Each homotopy starts at its original
singular simplex, ends with all vertices at the chosen base point, and is
literally constant in time on an already vertex-based simplex. The entire
family is compatible with the original singular face maps.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The initial stage is the actual chosen path at each singular vertex. -/
def vertexInitialData (x : X) : VertexHomotopyData x 0 where
  homotopy := vertexHomotopy x
  zero := vertexHomotopy_zero x
  one_verticesBased smp i := vertexHomotopy_one x smp (stdSimplex.vertex i)
  of_verticesBased smp h := by
    have hs : smp = ContinuousMap.const (Simplex 0) x := verticesBased_zero_iff.mp h
    rw [hs, vertexHomotopy_const]
    rfl
  face_compatible smp := faceCompatible_zero
    (fun i => vertexHomotopy x (smp.comp (simplexFace 0 i)))

/-- All stages are obtained by iteration of the proved extension step. -/
def vertexStraighteningData (x : X) : (n : ℕ) → VertexHomotopyData x n
  | 0 => vertexInitialData x
  | n + 1 => (vertexStraighteningData x n).next

/-- A genuine continuous vertex-straightening homotopy for each actual singular simplex. -/
def vertexStraighteningHomotopy (x : X) (n : ℕ) (smp : C(Simplex n, X)) :
    C(I × Simplex n, X) :=
  (vertexStraighteningData x n).homotopy smp

@[simp] theorem vertexStraighteningHomotopy_zero_dimension (x : X)
    (smp : C(Simplex 0, X)) :
    vertexStraighteningHomotopy x 0 smp = vertexHomotopy x smp := rfl

/-- The bottom of the normalization is exactly the original singular simplex. -/
@[simp] theorem vertexStraighteningHomotopy_zero (x : X) (n : ℕ)
    (smp : C(Simplex n, X)) (s : Simplex n) :
    vertexStraighteningHomotopy x n smp (0, s) = smp s :=
  (vertexStraighteningData x n).zero smp s

@[simp] theorem vertexStraighteningHomotopy_timeSlice_zero (x : X) (n : ℕ)
    (smp : C(Simplex n, X)) :
    timeSlice (vertexStraighteningHomotopy x n smp) 0 = smp := by
  ext s
  exact vertexStraighteningHomotopy_zero x n smp s

/-- Exact compatibility with the native singular face maps, in every adjacent degree. -/
theorem vertexStraighteningHomotopy_face (x : X) (n : ℕ) :
    FaceCompatibleHomotopies n
      (vertexStraighteningHomotopy x n) (vertexStraighteningHomotopy x (n + 1)) :=
  vertexStepHomotopy_face (vertexStraighteningData x n)

theorem vertexStraighteningHomotopy_face_apply (x : X) (n : ℕ)
    (smp : C(Simplex (n + 1), X)) (i : Fin (n + 2)) (r : I) (s : Simplex n) :
    vertexStraighteningHomotopy x (n + 1) smp (r, simplexFace n i s) =
      vertexStraighteningHomotopy x n (smp.comp (simplexFace n i)) (r, s) :=
  DFunLike.congr_fun (vertexStraighteningHomotopy_face x n smp i) (r, s)

theorem vertexStraighteningHomotopy_timeSlice_face (x : X) (n : ℕ)
    (smp : C(Simplex (n + 1), X)) (i : Fin (n + 2)) (r : I) :
    (timeSlice (vertexStraighteningHomotopy x (n + 1) smp) r).comp (simplexFace n i) =
      timeSlice (vertexStraighteningHomotopy x n (smp.comp (simplexFace n i))) r :=
  timeSlice_face (vertexStraighteningHomotopy_face x n) smp i r

/-- Every terminal vertex is the chosen base point. -/
theorem vertexStraighteningHomotopy_one_verticesBased (x : X) (n : ℕ)
    (smp : C(Simplex n, X)) :
    VerticesBased x n (timeSlice (vertexStraighteningHomotopy x n smp) 1) :=
  (vertexStraighteningData x n).one_verticesBased smp

/-- An already vertex-based simplex is left literally constant in time. -/
theorem vertexStraighteningHomotopy_of_verticesBased (x : X) (n : ℕ)
    (smp : C(Simplex n, X)) (h : VerticesBased x n smp) :
    vertexStraighteningHomotopy x n smp =
      smp.comp (ContinuousMap.snd : C(I × Simplex n, Simplex n)) :=
  (vertexStraighteningData x n).of_verticesBased smp h

theorem vertexStraighteningHomotopy_timeSlice_of_verticesBased (x : X) (n : ℕ)
    (smp : C(Simplex n, X)) (h : VerticesBased x n smp) (r : I) :
    timeSlice (vertexStraighteningHomotopy x n smp) r = smp := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n smp h]
  rfl

@[simp] theorem vertexStraighteningHomotopy_const (x : X) (n : ℕ) :
    vertexStraighteningHomotopy x n (ContinuousMap.const (Simplex n) x) =
      ContinuousMap.const (I × Simplex n) x := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n _ (verticesBased_const x n)]
  rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
