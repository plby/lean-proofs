import Wikipedia.NoExoticSixSphere.SimplexHomotopySubspace

/-!
# Coherent vertex normalization preserving the actual subspace

Choose paths inside the subspace for its points and ambient paths for
the other points. The basepoint path is literally constant. The proved
simplex extension step produces coherent vertex normalization in every
degree, and its subspace preservation keeps all relative chains valid.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeVertexNormalization

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (U : Set X) [PathConnectedSpace U] (a : U)

def basePath (x : X) : Path x a.val := by
  classical
  exact if h : x = a.val then (Path.refl a.val).cast h rfl
    else if hx : x ∈ U then
      (PathConnectedSpace.somePath (⟨x, hx⟩ : U) a).map continuous_subtype_val
    else PathConnectedSpace.somePath x a.val

theorem basePath_self : basePath U a a.val = Path.refl a.val := by
  classical
  simp only [basePath, dif_pos rfl]
  rfl

theorem basePath_mem (x : X) (hx : x ∈ U) (t : I) : basePath U a x t ∈ U := by
  classical
  unfold basePath
  split
  · exact a.property
  · exact (PathConnectedSpace.somePath (⟨x, hx⟩ : U) a t).property

def vertexHomotopy (smp : C(Simplex 0, X)) : C(I × Simplex 0, X) :=
  (basePath U a (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).toContinuousMap.comp
    (ContinuousMap.fst : C(I × Simplex 0, I))

theorem vertexHomotopy_zero (smp : C(Simplex 0, X)) (s : Simplex 0) :
    vertexHomotopy U a smp (0, s) = smp s := by
  change basePath U a (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1))) 0 = smp s
  rw [Path.source, simplexZero_eq_vertex s]

theorem vertexHomotopy_one (smp : C(Simplex 0, X)) (s : Simplex 0) :
    vertexHomotopy U a smp (1, s) = a.val :=
  (basePath U a (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).target

theorem vertexHomotopy_const : vertexHomotopy U a (ContinuousMap.const (Simplex 0) a.val) =
    ContinuousMap.const (I × Simplex 0) a.val := by
  ext p
  change basePath U a a.val p.1 = a.val
  rw [basePath_self]
  rfl

def initialData : VertexHomotopyData a.val 0 where
  homotopy := vertexHomotopy U a
  zero := vertexHomotopy_zero U a
  one_verticesBased smp i := vertexHomotopy_one U a smp (stdSimplex.vertex i)
  of_verticesBased smp h := by
    rw [verticesBased_zero_iff.mp h, vertexHomotopy_const]
    rfl
  face_compatible smp := faceCompatible_zero
    (fun i ↦ vertexHomotopy U a (smp.comp (simplexFace 0 i)))

def data : (n : ℕ) → VertexHomotopyData a.val n
  | 0 => initialData U a
  | n + 1 => (data n).next

def homotopy (n : ℕ) (smp : C(Simplex n, X)) : C(I × Simplex n, X) :=
  (data U a n).homotopy smp

theorem homotopy_zero (n : ℕ) (smp : C(Simplex n, X)) (s : Simplex n) :
    homotopy U a n smp (0, s) = smp s := (data U a n).zero smp s

theorem homotopy_face (n : ℕ) :
    FaceCompatibleHomotopies n (homotopy U a n) (homotopy U a (n + 1)) :=
  vertexStepHomotopy_face (data U a n)

theorem homotopy_mem (n : ℕ) : ∀ smp : C(Simplex n, X), (∀ s, smp s ∈ U) →
    ∀ p, homotopy U a n smp p ∈ U := by
  induction n with
  | zero =>
      intro smp hs p
      exact basePath_mem U a _ (hs (stdSimplex.vertex (S := ℝ) (0 : Fin 1))) p.1
  | succ n ih =>
      intro smp hs p
      exact SimplexHomotopySubspace.vertex_step_mem U (data U a n) ih smp hs p

theorem homotopy_of_verticesBased (n : ℕ) (smp : C(Simplex n, X))
    (h : VerticesBased a.val n smp) :
    homotopy U a n smp = stationarySimplexHomotopy n smp :=
  (data U a n).of_verticesBased smp h

def endpoint (n : ℕ) (smp : C(Simplex n, X)) : C(Simplex n, X) :=
  timeSlice (homotopy U a n smp) 1

theorem endpoint_verticesBased (n : ℕ) (smp : C(Simplex n, X)) :
    VerticesBased a.val n (endpoint U a n smp) := (data U a n).one_verticesBased smp

theorem endpoint_face (n : ℕ) (smp : C(Simplex (n + 1), X)) (i : Fin (n + 2)) :
    (endpoint U a (n + 1) smp).comp (simplexFace n i) =
      endpoint U a n (smp.comp (simplexFace n i)) :=
  timeSlice_face (homotopy_face U a n) smp i 1

theorem endpoint_mem (n : ℕ) (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U) (s : Simplex n) :
    endpoint U a n smp s ∈ U := homotopy_mem U a n smp hs (1, s)

end NoExoticSixSphere.RelativeVertexNormalization
