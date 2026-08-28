import Wikipedia.NoExoticSixSphere.RelativeBasedNormalization
import Wikipedia.NoExoticSixSphere.BasedSimplexSubspaceCompression

/-!
# Coherent compression of the actual two-skeleton into the subspace

First normalize vertices and edges while preserving the subspace. Next
lift based triangles using the original second-homotopy surjectivity.
The boundary-fixed lifting homotopies extend coherently to every higher
simplex. The terminal two-simplices lie in the actual subspace, and the
terminal three-simplices have their entire boundary there.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected ThirdHurewicz

namespace NoExoticSixSphere.RelativeTwoSkeletonNormalization

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (U : Set X) [SimplyConnectedSpace U] (a : U)
    (hπ : Function.Surjective
      (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

def triangleInitialData : RelativeSimplexHomotopyFamily.Stage U 1 where
  lower := stationarySimplexHomotopy 1
  upper := BasedSimplexSubspaceCompression.homotopy U a 2 hπ
  lower_zero _ _ := rfl
  upper_zero := BasedSimplexSubspaceCompression.homotopy_zero U a 2 hπ
  face := BasedSimplexSubspaceCompression.homotopy_face U a 1 hπ
  lower_mem smp hs p := hs p.2
  upper_mem := BasedSimplexSubspaceCompression.homotopy_mem U a 2 hπ

def triangleData : (k : ℕ) → RelativeSimplexHomotopyFamily.Stage U (k + 1)
  | 0 => triangleInitialData U a hπ
  | k + 1 => (triangleData k).next

def triangleHomotopy : (n : ℕ) → C(Simplex n, X) → C(I × Simplex n, X)
  | 0 => stationarySimplexHomotopy 0
  | n + 1 => (triangleData U a hπ n).lower

theorem triangleHomotopy_zero (n : ℕ) (smp : C(Simplex n, X)) (s : Simplex n) :
    triangleHomotopy U a hπ n smp (0, s) = smp s := by
  cases n with
  | zero => rfl
  | succ n => exact (triangleData U a hπ n).lower_zero smp s

theorem triangleHomotopy_face (n : ℕ) :
    FaceCompatibleHomotopies n (triangleHomotopy U a hπ n) (triangleHomotopy U a hπ (n + 1)) := by
  cases n with
  | zero => intro smp i; ext p; rfl
  | succ n => exact (triangleData U a hπ n).face

theorem triangleHomotopy_mem (n : ℕ) (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U)
    (p : I × Simplex n) : triangleHomotopy U a hπ n smp p ∈ U := by
  cases n with
  | zero => exact hs p.2
  | succ n => exact (triangleData U a hπ n).lower_mem smp hs p

def homotopy (n : ℕ) (smp : C(Simplex n, X)) : C(I × Simplex n, X) :=
  composeSimplexHomotopies (RelativeBasedNormalization.homotopy U a n)
    (triangleHomotopy U a hπ n) (RelativeBasedNormalization.homotopy_zero U a n)
    (triangleHomotopy_zero U a hπ n) smp

theorem homotopy_zero (n : ℕ) (smp : C(Simplex n, X)) (s : Simplex n) :
    homotopy U a hπ n smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

theorem homotopy_face (n : ℕ) :
    FaceCompatibleHomotopies n (homotopy U a hπ n) (homotopy U a hπ (n + 1)) :=
  composeSimplexHomotopies_face _ _ _ _ _ _ _ _
    (RelativeBasedNormalization.homotopy_face U a n) (triangleHomotopy_face U a hπ n)

theorem homotopy_mem (n : ℕ) (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U)
    (p : I × Simplex n) : homotopy U a hπ n smp p ∈ U :=
  RelativeSimplexHomotopyFamily.compose_mem U _ _ _ _
    (RelativeBasedNormalization.homotopy_mem U a n) (triangleHomotopy_mem U a hπ n) smp hs p

def endpoint (n : ℕ) (smp : C(Simplex n, X)) : C(Simplex n, X) :=
  timeSlice (homotopy U a hπ n smp) 1

theorem endpoint_face (n : ℕ) (smp : C(Simplex (n + 1), X)) (i : Fin (n + 2)) :
    (endpoint U a hπ (n + 1) smp).comp (simplexFace n i) =
      endpoint U a hπ n (smp.comp (simplexFace n i)) :=
  timeSlice_face (homotopy_face U a hπ n) smp i 1

theorem endpoint_mem (n : ℕ) (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U) (s : Simplex n) :
    endpoint U a hπ n smp s ∈ U := homotopy_mem U a hπ n smp hs (1, s)

theorem endpoint_verticesBased (n : ℕ) (smp : C(Simplex n, X)) :
    VerticesBased a.val n (endpoint U a hπ n smp) := by
  induction n with
  | zero =>
    intro i
    change composeSimplexHomotopies _ _ _ _ smp (1, stdSimplex.vertex i) = a.val
    rw [composeSimplexHomotopies_one]
    change RelativeBasedNormalization.endpoint U a 0 smp (stdSimplex.vertex i) = a.val
    change composeSimplexHomotopies _ _ _ _ smp (1, stdSimplex.vertex i) = a.val
    rw [composeSimplexHomotopies_one]
    exact RelativeVertexNormalization.endpoint_verticesBased U a 0 smp i
  | succ n ih =>
    apply verticesBased_of_faces
    intro i
    rw [endpoint_face]
    exact ih (smp.comp (simplexFace n i))

theorem endpoint_edge (smp : C(Simplex 1, X)) :
    endpoint U a hπ 1 smp = ContinuousMap.const (Simplex 1) a.val := by
  ext s
  change composeSimplexHomotopies _ _ _ _ smp (1, s) = a.val
  rw [composeSimplexHomotopies_one]
  exact congrArg (fun f : C(Simplex 1, X) ↦ f s)
    (RelativeBasedNormalization.endpoint_edge U a smp)

theorem endpoint_triangle_mem (smp : C(Simplex 2, X)) (s : Simplex 2) :
    endpoint U a hπ 2 smp s ∈ U := by
  change composeSimplexHomotopies _ _ _ _ smp (1, s) ∈ U
  rw [composeSimplexHomotopies_one]
  exact BasedSimplexSubspaceCompression.homotopy_one_mem U a 2 hπ
    (RelativeBasedNormalization.endpoint U a 2 smp)
    (RelativeBasedNormalization.endpoint_triangle_boundary U a smp) s

theorem endpoint_tetrahedron_boundary (smp : C(Simplex 3, X)) (s : Simplex 3)
    (hs : s ∈ simplexBoundary 3) : endpoint U a hπ 3 smp s ∈ U := by
  obtain ⟨i, t, ht⟩ := simplexBoundary_exists_face 2 (⟨s, hs⟩ : SimplexBoundary 3)
  have he : simplexFace 2 i t = s := congrArg Subtype.val ht
  rw [← he]
  have hf := congrArg (fun f : C(Simplex 2, X) ↦ f t) (endpoint_face U a hπ 2 smp i)
  change ((endpoint U a hπ (2 + 1) smp).comp (simplexFace 2 i)) t ∈ U
  rw [hf]
  exact endpoint_triangle_mem U a hπ (smp.comp (simplexFace 2 i)) t

end NoExoticSixSphere.RelativeTwoSkeletonNormalization
