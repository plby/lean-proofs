import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexStep
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdgeExtension

/-!
# The actual simplex homotopy extensions preserve subspaces

The explicit cylinder retraction takes values in the bottom or side.
Thus extension preserves any target subset containing both prescribed
images. Face pasting has the same property. These facts make the actual
coherent normalization constructions available for relative chains.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.SimplexHomotopySubspace

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem extend_mem {n : ℕ} (f : C(Simplex n, X))
    (h : C(I × SimplexBoundary n, X)) (h₀ : ∀ s, h (0, s) = f s.val)
    (hf : ∀ s, f s ∈ U) (hh : ∀ p, h p ∈ U) (p : I × Simplex n) :
    extendBoundaryHomotopy f h h₀ p ∈ U := by
  let q := cylinderRetraction n p
  change gluedBoundaryMap f h h₀ q ∈ U
  rcases q.property with hq | hq
  · have he : bottomInclusion n q.val.2 = q := by
      apply Subtype.ext
      exact Prod.ext hq.symm rfl
    rw [← he, gluedBoundaryMap_bottomInclusion]
    exact hf q.val.2
  · have he : sideInclusion n (q.val.1, ⟨q.val.2, hq⟩) = q := rfl
    rw [← he, gluedBoundaryMap_sideInclusion]
    exact hh _

theorem glue_faces_mem {n : ℕ} (F : Fin (n + 2) → C(I × Simplex n, X))
    (hF : FaceCompatible F) (hU : ∀ i p, F i p ∈ U)
    (p : I × SimplexBoundary (n + 1)) : glueFaceHomotopies F hF p ∈ U := by
  obtain ⟨i, s, hs⟩ := simplexBoundary_exists_face n p.2
  have hp : p = (p.1, simplexFaceBoundary n i s) := Prod.ext rfl hs.symm
  rw [hp, glueFaceHomotopies_face]
  exact hU i _

theorem vertex_step_mem {n : ℕ} {x : X} (D : VertexHomotopyData x n)
    (hD : ∀ smp : C(Simplex n, X), (∀ s, smp s ∈ U) → ∀ p, D.homotopy smp p ∈ U)
    (smp : C(Simplex (n + 1), X)) (hs : ∀ s, smp s ∈ U) (p : I × Simplex (n + 1)) :
    vertexStepHomotopy D smp p ∈ U := by
  by_cases hb : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp hb]
    exact hs p.2
  · rw [vertexStepHomotopy_of_not_verticesBased D smp hb]
    apply extend_mem U _ _ _ hs
    intro q
    exact glue_faces_mem U _ _
      (fun i z ↦ hD (smp.comp (simplexFace n i)) (fun s ↦ hs (simplexFace n i s)) z) q

theorem coherent_extension_mem {n : ℕ}
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (hU : ∀ smp : SingularSimplex X (n + 1), (∀ s, smp s ∈ U) → ∀ p, H' smp p ∈ U)
    (smp : SingularSimplex X (n + 2)) (hs : ∀ s, smp s ∈ U) (p : I × Simplex (n + 2)) :
    extendCoherentSimplexHomotopy H H' h h₀ smp p ∈ U := by
  apply extend_mem U _ _ _ hs
  intro q
  exact glue_faces_mem U _ _
    (fun i z ↦ hU (smp.comp (simplexFace (n + 1) i))
      (fun s ↦ hs (simplexFace (n + 1) i s)) z) q

end NoExoticSixSphere.SimplexHomotopySubspace
