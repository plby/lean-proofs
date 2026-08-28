import Wikipedia.NoExoticSixSphere.RelativeTwoSkeletonNormalization
import Wikipedia.NoExoticSixSphere.SimplexHomotopyVertexFixing

/-!
# The original normalization is a pair homotopy fixing based vertices

On a relative simplex every boundary face stays in the subspace by the
proved lower-dimensional support preservation. A vertex already at the
chosen point is fixed throughout, not merely returned there at the end.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected ThirdHurewicz

namespace NoExoticSixSphere.RelativeTwoSkeletonNormalization

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)
  (hπ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

theorem homotopy_const_zero : homotopy U a hπ 0 (ContinuousMap.const (Simplex 0) a.val) =
    ContinuousMap.const (I × Simplex 0) a.val := by
  apply composeSimplexHomotopies_const
  · apply composeSimplexHomotopies_const
    · exact RelativeVertexNormalization.vertexHomotopy_const U a
    · rfl
  · rfl

theorem homotopy_vertex (n : ℕ) (smp : C(Simplex n, X)) (i : Fin (n + 1))
    (hi : smp (stdSimplex.vertex (S := ℝ) i) = a.val) (t : I) :
    homotopy U a hπ n smp (t, stdSimplex.vertex i) = a.val :=
  SimplexHomotopyVertexFixing.vertex_fixed (homotopy U a hπ) (homotopy_face U a hπ)
    a.val (homotopy_const_zero U a hπ) n smp i hi t

theorem homotopy_boundary (n : ℕ) (smp : C(Simplex (n + 1), X))
    (hU : ∀ s ∈ simplexBoundary (n + 1), smp s ∈ U)
    (t : I) (s : Simplex (n + 1)) (hs : s ∈ simplexBoundary (n + 1)) :
    homotopy U a hπ (n + 1) smp (t, s) ∈ U := by
  obtain ⟨i, z, hz⟩ := simplexBoundary_exists_face n (⟨s, hs⟩ : SimplexBoundary (n + 1))
  have he : simplexFace n i z = s := congrArg Subtype.val hz
  rw [← he]
  have hf : homotopy U a hπ (n + 1) smp (t, simplexFace n i z) =
      homotopy U a hπ n (smp.comp (simplexFace n i)) (t, z) :=
    congrArg (fun F : C(I × Simplex n, X) ↦ F (t, z)) (homotopy_face U a hπ n smp i)
  rw [hf]
  exact homotopy_mem U a hπ n (smp.comp (simplexFace n i))
    (fun q ↦ hU (simplexFace n i q) (simplexFace_mem_boundary n i q)) (t, z)

def pairHomotopy (n : ℕ) (smp : C(Simplex n, X)) : smp.Homotopy (endpoint U a hπ n smp) :=
  simplexFamilyHomotopy (homotopy U a hπ n) (homotopy_zero U a hπ n) smp

end NoExoticSixSphere.RelativeTwoSkeletonNormalization
