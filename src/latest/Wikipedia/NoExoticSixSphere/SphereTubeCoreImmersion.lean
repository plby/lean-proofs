import Wikipedia.NoExoticSixSphere.AmbientSphereTube

/-!
# The ambient tube's core differential parametrizes the original tangent image

The sphere derivative and its actual internal normal frame are
orthogonal and injective. Their combined native derivative is therefore
injective, and its entire range is exactly the original manifold
tangent image. The tangent image is not supplied as an independent plane.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector q →L[ℝ] Vector e.ambientDimension)
  (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector q →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)

include hf hd in
theorem injective_mfderiv_embeddedSphere (s : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s) := by
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  exact (e.injective_mfderiv (f s)).comp (hd s)

include hf in
theorem range_mfderiv_embeddedSphere_le (s : Sphere 3) :
    (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).range ≤ e.tangentImage (f s) := by
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

include hf hC hd hiC hCr in
theorem injective_mfderiv_ambientSphereTube_core (s : Sphere 3) :
    Injective (mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
      (e.ambientSphereTube f C) (s, 0)) := by
  rw [e.mfderiv_ambientSphereTube_core f C hf hC s]
  let B : Vector 3 →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s
  have horth : (C s).range ≤ B.rangeᗮ := by
    rw [hCr s]
    exact inf_le_right
  change Injective (B.toLinearMap.coprod (C s).toLinearMap)
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_coprod_of_disjoint_range _ _
    (B.range.orthogonal_disjoint.mono_right horth),
    LinearMap.ker_eq_bot.mpr (show Injective B from e.injective_mfderiv_embeddedSphere f hf hd s),
    LinearMap.ker_eq_bot.mpr (hiC s), Submodule.prod_bot]

include hf hC hd hiC hCr in
theorem range_mfderiv_ambientSphereTube_core (s : Sphere 3) :
    (mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
      (e.ambientSphereTube f C) (s, 0)).range = e.tangentImage (f s) := by
  let B : Vector 3 →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s
  let G : (Vector 3 × Vector q) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension) (e.ambientSphereTube f C) (s, 0)
  have hG : G = B.coprod (C s) := e.mfderiv_ambientSphereTube_core f C hf hC s
  have hB : B.range ≤ e.tangentImage (f s) := e.range_mfderiv_embeddedSphere_le f hf s
  change G.range = e.tangentImage (f s)
  rw [hG]
  change (B.toLinearMap.coprod (C s).toLinearMap).range = _
  rw [LinearMap.range_coprod, hCr s]
  change B.range ⊔ (e.tangentImage (f s) ⊓ B.rangeᗮ) = e.tangentImage (f s)
  rw [inf_comm (e.tangentImage (f s)) B.rangeᗮ,
    ← sup_inf_assoc_of_le B.rangeᗮ hB,
    B.range.isCompl_orthogonal.sup_eq_top, top_inf_eq]

end NoExoticSixSphere.EuclideanEmbedding
