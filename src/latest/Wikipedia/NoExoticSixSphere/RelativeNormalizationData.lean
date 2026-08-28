import Wikipedia.NoExoticSixSphere.RelativeNormalizedHomology
import Wikipedia.NoExoticSixSphere.SimplexFirstEdge
import Wikipedia.NoExoticSixSphere.SimplexHomotopyVertexFixing
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceCover

/-!
# Actual coherent relative normalization data

The data records a continuous simplex homotopy family and its literal
identities. The low-skeleton endpoint lies in the given subspace. No
homology isomorphism or homotopy-detection result is a field.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeNormalization

variable {X : Type} [TopologicalSpace X]

structure Data (U : Set X) (a : U) (n : ℕ) where
  homotopy : ∀ k, C(Simplex k, X) → C(I × Simplex k, X)
  initial : ∀ k smp s, homotopy k smp (0, s) = smp s
  face : ∀ k, FaceCompatibleHomotopies k (homotopy k) (homotopy (k + 1))
  preserves : ∀ k smp, (∀ s, smp s ∈ U) → ∀ p, homotopy k smp p ∈ U
  vertices : ∀ k smp, VerticesBased a.val k (timeSlice (homotopy k smp) 1)
  edge : ∀ smp, timeSlice (homotopy 1 smp) 1 = ContinuousMap.const (Simplex 1) a.val
  lower_mem : ∀ smp : C(Simplex (n + 2), X), ∀ s, timeSlice (homotopy (n + 2) smp) 1 s ∈ U
  constant_zero : homotopy 0 (ContinuousMap.const (Simplex 0) a.val) =
    ContinuousMap.const (I × Simplex 0) a.val

namespace Data

variable {U : Set X} {a : U} {n : ℕ} (D : Data U a n)

def endpoint (k : ℕ) (smp : C(Simplex k, X)) : C(Simplex k, X) :=
  timeSlice (D.homotopy k smp) 1

theorem endpoint_face (k : ℕ) (smp : C(Simplex (k + 1), X)) (i : Fin (k + 2)) :
    (D.endpoint (k + 1) smp).comp (simplexFace k i) =
      D.endpoint k (smp.comp (simplexFace k i)) :=
  timeSlice_face (D.face k) smp i 1

theorem endpoint_mem (k : ℕ) (smp : C(Simplex k, X)) (hs : ∀ s, smp s ∈ U) (s : Simplex k) :
    D.endpoint k smp s ∈ U := D.preserves k smp hs (1, s)

theorem endpoint_boundary (smp : C(Simplex (n + 3), X)) (s : Simplex (n + 3))
    (hs : s ∈ simplexBoundary (n + 3)) : D.endpoint (n + 3) smp s ∈ U := by
  obtain ⟨i, z, hz⟩ := simplexBoundary_exists_face (n + 2)
    (⟨s, hs⟩ : SimplexBoundary (n + 3))
  have he : simplexFace (n + 2) i z = s := congrArg Subtype.val hz
  rw [← he]
  change ((D.endpoint (n + 3) smp).comp (simplexFace (n + 2) i)) z ∈ U
  rw [D.endpoint_face]
  exact D.lower_mem (smp.comp (simplexFace (n + 2) i)) z

theorem homotopy_vertex (k : ℕ) (smp : C(Simplex k, X)) (i : Fin (k + 1))
    (hi : smp (stdSimplex.vertex (S := ℝ) i) = a.val) (t : I) :
    D.homotopy k smp (t, stdSimplex.vertex i) = a.val :=
  SimplexHomotopyVertexFixing.vertex_fixed D.homotopy D.face a.val D.constant_zero k smp i hi t

theorem homotopy_boundary (k : ℕ) (smp : C(Simplex (k + 1), X))
    (hU : ∀ s ∈ simplexBoundary (k + 1), smp s ∈ U)
    (t : I) (s : Simplex (k + 1)) (hs : s ∈ simplexBoundary (k + 1)) :
    D.homotopy (k + 1) smp (t, s) ∈ U := by
  obtain ⟨i, z, hz⟩ := simplexBoundary_exists_face k (⟨s, hs⟩ : SimplexBoundary (k + 1))
  have he : simplexFace k i z = s := congrArg Subtype.val hz
  rw [← he]
  have hf : D.homotopy (k + 1) smp (t, simplexFace k i z) =
      D.homotopy k (smp.comp (simplexFace k i)) (t, z) :=
    congrArg (fun F : C(I × Simplex k, X) ↦ F (t, z)) (D.face k smp i)
  rw [hf]
  exact D.preserves k (smp.comp (simplexFace k i))
    (fun q ↦ hU (simplexFace k i q) (simplexFace_mem_boundary k i q)) (t, z)

def pairHomotopy (k : ℕ) (smp : C(Simplex k, X)) : smp.Homotopy (D.endpoint k smp) :=
  ThirdHurewicz.simplexFamilyHomotopy (D.homotopy k) (D.initial k) smp

theorem endpoint_firstEdgePath (smp : C(Simplex (n + 4), X)) (r : I) :
    D.endpoint (n + 4) smp (SimplexFirstEdge.path (n + 3) r) = a.val := by
  have he : (D.endpoint (n + 4) smp).comp (SimplexFirstEdge.inclusion (n + 3)) =
      ContinuousMap.const (Simplex 1) a.val :=
    (SimplexFirstEdge.endpoint_comp D.homotopy D.face (n + 3) smp).trans (D.edge _)
  exact congrArg (fun f : C(Simplex 1, X) ↦ f (stdSimplexHomeomorphUnitInterval.symm r)) he

end Data

end NoExoticSixSphere.RelativeNormalization
