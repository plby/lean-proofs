import Wikipedia.NoExoticSixSphere.SphereCollapseRegularValue
import Wikipedia.NoExoticSixSphere.CompactifiedEmbeddingDifferential
import Wikipedia.NoExoticSixSphere.RegularFiberIdentification

/-!
# The candidate sphere as an actual smooth regular fiber

The previously constructed regular collapse identifies the embedded candidate
with the distinguished fiber as a set. The regular-fiber atlas now gives a
diffeomorphism from the candidate, with its independently specified atlas,
onto this fiber. Its underlying map is exactly the compactified embedding.
This is not a diffeomorphism from the candidate to the standard six-sphere.
-/

open scoped Manifold ContDiff
open Module

namespace NoExoticSixSphere

theorem exists_sixSphereDiffeomorphicRegularFiber {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      ∃ g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - 6)),
        ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) ∞ g ∧
        (∀ y, g y = sphereZero (e.ambientDimension - 6) →
          Function.Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) g y)) ∧
        ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin 6))
            {y : Sphere e.ambientDimension // g y = sphereZero (e.ambientDimension - 6)},
          letI := c;
          IsManifold (𝓡 6) ∞
            {y : Sphere e.ambientDimension // g y = sphereZero (e.ambientDimension - 6)} ∧
          ContMDiff (𝓡 6) (𝓡 e.ambientDimension) ∞
            (Subtype.val : {y : Sphere e.ambientDimension //
              g y = sphereZero (e.ambientDimension - 6)} → Sphere e.ambientDimension) ∧
          ∃ D : M ≃ₘ⟮𝓡 6, 𝓡 6⟯
              {y : Sphere e.ambientDimension // g y = sphereZero (e.ambientDimension - 6)},
            ∀ x, (D x).val = e.compactifiedEmbedding x := by
  let : Nonempty (Sphere 6) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let : Nonempty M := h.toEquiv.nonempty
  obtain ⟨e, g, hg, hfiber, hreg⟩ := exists_sixSphereRegularCollapse h
  have hn : 6 ≤ e.ambientDimension := e.dimension_le_ambient (Classical.choice inferInstance)
  have hd : finrank ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) =
      finrank ℝ (EuclideanSpace ℝ (Fin (e.ambientDimension - 6))) + 6 := by
    simp only [finrank_euclideanSpace_fin]
    omega
  let b := sphereZero (e.ambientDimension - 6)
  refine ⟨e, g, hg, hreg, regularFiberAtlas g hg b hreg 6 hd, ?_⟩
  let := regularFiberAtlas g hg b hreg 6 hd
  refine ⟨regularFiber_isManifold g hg b hreg 6 hd,
    regularFiber_contMDiff_subtype_val g hg b hreg 6 hd, ?_⟩
  exact ⟨diffeomorphToRegularFiber g hg b hreg 6 hd e.compactifiedEmbedding
      e.contMDiff_compactifiedEmbedding e.compactifiedEmbedding_isEmbedding.injective
      e.injective_mfderiv_compactifiedEmbedding hfiber,
    diffeomorphToRegularFiber_val g hg b hreg 6 hd e.compactifiedEmbedding
      e.contMDiff_compactifiedEmbedding e.compactifiedEmbedding_isEmbedding.injective
      e.injective_mfderiv_compactifiedEmbedding hfiber⟩

end NoExoticSixSphere
