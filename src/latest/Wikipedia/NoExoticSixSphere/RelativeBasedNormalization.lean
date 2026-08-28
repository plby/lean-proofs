import Wikipedia.NoExoticSixSphere.RelativeVertexNormalization
import Wikipedia.NoExoticSixSphere.RelativeEdgeNormalization
import Wikipedia.NoExoticSixSphere.RelativeSimplexHomotopyFamily

/-!
# Coherent based-triangle normalization for an actual simply connected pair

Subspace-preserving vertex motion is followed by subspace-preserving
edge contraction and its actual coherent extensions. The resulting
families start at the original simplex, preserve the subspace, and are
exactly compatible with all faces in every degree. Every terminal edge
is constant, so every terminal triangle has its full boundary based.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SecondHurewicz.SimplyConnected ThirdHurewicz

namespace NoExoticSixSphere.RelativeBasedNormalization

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (U : Set X) [SimplyConnectedSpace U] (a : U)

def edgeInitialData : RelativeSimplexHomotopyFamily.Stage U 0 where
  lower := stationarySimplexHomotopy 0
  upper := RelativeEdgeNormalization.homotopy U a
  lower_zero _ _ := rfl
  upper_zero := RelativeEdgeNormalization.homotopy_zero U a
  face := RelativeEdgeNormalization.homotopy_face U a
  lower_mem smp hs p := hs p.2
  upper_mem := RelativeEdgeNormalization.homotopy_mem U a

def edgeData : (n : ℕ) → RelativeSimplexHomotopyFamily.Stage U n
  | 0 => edgeInitialData U a
  | n + 1 => (edgeData n).next

def edgeHomotopy (n : ℕ) (smp : C(Simplex n, X)) : C(I × Simplex n, X) :=
  (edgeData U a n).lower smp

theorem edgeHomotopy_zero (n : ℕ) (smp : C(Simplex n, X)) (s : Simplex n) :
    edgeHomotopy U a n smp (0, s) = smp s := (edgeData U a n).lower_zero smp s

theorem edgeHomotopy_face (n : ℕ) :
    FaceCompatibleHomotopies n (edgeHomotopy U a n) (edgeHomotopy U a (n + 1)) :=
  (edgeData U a n).face

theorem edgeHomotopy_mem (n : ℕ) (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U)
    (p : I × Simplex n) : edgeHomotopy U a n smp p ∈ U :=
  (edgeData U a n).lower_mem smp hs p

def homotopy (n : ℕ) (smp : C(Simplex n, X)) : C(I × Simplex n, X) :=
  composeSimplexHomotopies (RelativeVertexNormalization.homotopy U a n) (edgeHomotopy U a n)
    (RelativeVertexNormalization.homotopy_zero U a n) (edgeHomotopy_zero U a n) smp

theorem homotopy_zero (n : ℕ) (smp : C(Simplex n, X)) (s : Simplex n) :
    homotopy U a n smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

theorem homotopy_face (n : ℕ) :
    FaceCompatibleHomotopies n (homotopy U a n) (homotopy U a (n + 1)) :=
  composeSimplexHomotopies_face _ _ _ _ _ _ _ _
    (RelativeVertexNormalization.homotopy_face U a n) (edgeHomotopy_face U a n)

theorem homotopy_mem (n : ℕ) (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U)
    (p : I × Simplex n) : homotopy U a n smp p ∈ U :=
  RelativeSimplexHomotopyFamily.compose_mem U _ _ _ _
    (RelativeVertexNormalization.homotopy_mem U a n) (edgeHomotopy_mem U a n) smp hs p

def endpoint (n : ℕ) (smp : C(Simplex n, X)) : C(Simplex n, X) :=
  timeSlice (homotopy U a n smp) 1

theorem endpoint_face (n : ℕ) (smp : C(Simplex (n + 1), X)) (i : Fin (n + 2)) :
    (endpoint U a (n + 1) smp).comp (simplexFace n i) =
      endpoint U a n (smp.comp (simplexFace n i)) :=
  timeSlice_face (homotopy_face U a n) smp i 1

theorem endpoint_mem (n : ℕ) (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U) (s : Simplex n) :
    endpoint U a n smp s ∈ U := homotopy_mem U a n smp hs (1, s)

theorem endpoint_edge (smp : C(Simplex 1, X)) :
    endpoint U a 1 smp = ContinuousMap.const (Simplex 1) a.val := by
  ext s
  change composeSimplexHomotopies _ _ _ _ smp (1, s) = a.val
  rw [composeSimplexHomotopies_one]
  exact RelativeEdgeNormalization.homotopy_one U a
    (RelativeVertexNormalization.endpoint U a 1 smp)
    (RelativeVertexNormalization.endpoint_verticesBased U a 1 smp) s

theorem endpoint_triangle_boundary (smp : C(Simplex 2, X)) (s : Simplex 2)
    (hs : s ∈ simplexBoundary 2) : endpoint U a 2 smp s = a.val := by
  obtain ⟨i, t, ht⟩ := simplexBoundary_exists_face 1 (⟨s, hs⟩ : SimplexBoundary 2)
  have he : simplexFace 1 i t = s := congrArg Subtype.val ht
  rw [← he]
  have hf := congrArg (fun f : C(Simplex 1, X) ↦ f t) (endpoint_face U a 1 smp i)
  exact hf.trans (congrArg (fun f : C(Simplex 1, X) ↦ f t)
    (endpoint_edge U a (smp.comp (simplexFace 1 i))))

end NoExoticSixSphere.RelativeBasedNormalization
