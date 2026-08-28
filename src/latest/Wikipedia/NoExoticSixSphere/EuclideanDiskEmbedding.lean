import Wikipedia.NoExoticSixSphere.CompactDiskEmbedding
import Wikipedia.NoExoticSixSphere.StabilizedEmbedding

/-!
# Relative disk embeddings in actual Euclidean coordinates

The extra scalar and source coordinates are identified with a Euclidean
coordinate block. On the retained collar, this identification is exactly
the original zero-coordinate stabilization. A four-dimensional source needs
five added ambient coordinates.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.DiskGraph

def scalarCoordinates : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ))).symm

def extraCoordinates (d : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin d)) ≃L[ℝ] EuclideanSpace ℝ (Fin (1 + d)) :=
  (scalarCoordinates.prodCongr
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)))).trans
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := d)).symm

def coordinateEquiv (N d : ℕ) :
    (EuclideanSpace ℝ (Fin N) × (ℝ × EuclideanSpace ℝ (Fin d))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + (1 + d))) :=
  ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))).prodCongr
    (extraCoordinates d)).trans
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1 + d)).symm

theorem coordinateEquiv_old (N d : ℕ) (y : EuclideanSpace ℝ (Fin N)) :
    coordinateEquiv N d (y, 0) = appendZeroMap N (1 + d) y := by
  change (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1 + d)).symm
    (y, extraCoordinates d 0) =
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1 + d)).symm (y, 0)
  rw [map_zero]

/-- The actual Euclidean disk is embedded and immersive, with the original collar and avoidance. -/
theorem exists_euclidean_embedding_rel_sphere_avoiding {d N : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N)}
    (hf : ContDiff ℝ ∞ f) (hi : InjOn f (sphere 0 1))
    (hd : ∀ x ∈ sphere 0 1, Injective (fderiv ℝ f x))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hSU : sphere 0 1 ⊆ U)
    (S : Set (EuclideanSpace ℝ (Fin N))) (ha : ∀ x ∈ U ∩ ball 0 1, f x ∉ S) :
    ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (N + (1 + d))),
      ContDiff ℝ ∞ G ∧
      IsClosedEmbedding (fun x : closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ↦ G x.val) ∧
      (∀ x ∈ closedBall 0 1, Injective (fderiv ℝ G x)) ∧
      (∀ x ∈ ball 0 1, G x ∉ appendZeroMap N (1 + d) '' S) ∧
      ∃ V : Set (EuclideanSpace ℝ (Fin d)), IsOpen V ∧ sphere 0 1 ⊆ V ∧ V ⊆ U ∧
        ∀ x ∈ V, G x = appendZeroMap N (1 + d) (f x) := by
  obtain ⟨g, hg, hge, hgd, hga, V, hV, hSV, hVU, hVg⟩ :=
    exists_embedding_rel_sphere_avoiding hf hi hd hU hSU S ha
  let L := coordinateEquiv N d
  refine ⟨L ∘ g, L.contDiff.comp hg, L.toHomeomorph.isClosedEmbedding.comp hge,
    ?_, ?_, V, hV, hSV, hVU, ?_⟩
  · intro x hx
    rw [(L.hasFDerivAt.comp x ((hg.differentiable (by simp) x).hasFDerivAt)).fderiv]
    exact L.injective.comp (hgd x hx)
  · intro x hx h
    obtain ⟨y, hy, heq⟩ := h
    have hgxy : g x = (y, 0) := L.injective (by
      rw [coordinateEquiv_old]
      exact heq.symm)
    exact hga x hx (by rw [hgxy]; exact ⟨hy, rfl⟩)
  · intro x hx
    change L (g x) = _
    rw [hVg x hx]
    exact coordinateEquiv_old N d (f x)

end NoExoticSixSphere.DiskGraph
