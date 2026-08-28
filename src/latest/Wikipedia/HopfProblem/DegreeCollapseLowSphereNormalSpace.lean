import Wikipedia.HopfProblem.DegreeCollapseLowFramedProduct

/-!

# The original internal normal directions for low-dimensional spheres

The internal normal space uses the actual derivative and the original
seven-manifold tangent image. The native chain rule and injectivity compute
its rank as 7-d, without supplying a replacement normal-plane field.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : NoExoticSixSphere.Sphere d → M)

def sphereNormalSpace (s : NoExoticSixSphere.Sphere d) :
    Submodule ℝ (Vector e.ambientDimension) :=
  e.tangentImage (f s) ⊓ (mfderiv (𝓡 d) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ

theorem sphere_dimension_le_seven
    (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
    (s : NoExoticSixSphere.Sphere d) : d ≤ 7 := by
  let L : Vector d →L[ℝ] Vector 7 := mfderiv (𝓡 d) (𝓡 7) f s
  have hi : Injective L := hd s
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := L.toLinearMap) hi
  simpa only [finrank_euclideanSpace_fin] using h

theorem range_mfderiv_embeddedSphere_le (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
    (s : NoExoticSixSphere.Sphere d) :
    (mfderiv (𝓡 d) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).range ≤
      e.tangentImage (f s) := by
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

theorem injective_mfderiv_embeddedSphere (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
    (s : NoExoticSixSphere.Sphere d) :
    Injective (mfderiv (𝓡 d) (𝓡 e.ambientDimension) (e.toFun ∘ f) s) := by
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  exact (e.injective_mfderiv (f s)).comp (hd s)

theorem finrank_sphereNormalSpace (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
    (s : NoExoticSixSphere.Sphere d) :
    Module.finrank ℝ (sphereNormalSpace e f s) = 7 - d := by
  let B : Vector d →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 d) (𝓡 e.ambientDimension) (e.toFun ∘ f) s
  have hi : Injective B := injective_mfderiv_embeddedSphere e f hf hd s
  have hle : B.range ≤ e.tangentImage (f s) := range_mfderiv_embeddedSphere_le e f hf s
  have h := Submodule.finrank_add_inf_finrank_orthogonal
    (K₁ := B.range) (K₂ := e.tangentImage (f s)) hle
  rw [LinearMap.finrank_range_of_inj hi,
    finrank_euclideanSpace_fin, e.finrank_tangentImage, inf_comm] at h
  change d + Module.finrank ℝ (sphereNormalSpace e f s) = 7 at h
  omega

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
