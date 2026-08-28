import Wikipedia.HopfProblem.DegreeCollapseSevenManifoldFramedSphere

/-!
# The actual four-dimensional internal normal space of a three-sphere

The space is the original seven-manifold tangent image intersected with
the orthogonal complement of the actual sphere differential. The chain
rule and injectivity compute its dimension; no abstract four-plane or
independent normal-space hypothesis is supplied.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : NoExoticSixSphere.Sphere 3 → M)

def sphereNormalSpace (s : NoExoticSixSphere.Sphere 3) :
    Submodule ℝ (Vector e.ambientDimension) :=
  e.tangentImage (f s) ⊓ (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ

theorem range_mfderiv_embeddedSphere_le (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (s : NoExoticSixSphere.Sphere 3) :
    (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).range ≤
      e.tangentImage (f s) := by
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

theorem injective_mfderiv_embeddedSphere (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
    (s : NoExoticSixSphere.Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s) := by
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  exact (e.injective_mfderiv (f s)).comp (hd s)

theorem finrank_sphereNormalSpace (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
    (s : NoExoticSixSphere.Sphere 3) :
    Module.finrank ℝ (sphereNormalSpace e f s) = 4 := by
  let B : Vector 3 →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s
  have hi : Injective B := injective_mfderiv_embeddedSphere e f hf hd s
  have hle : B.range ≤ e.tangentImage (f s) := range_mfderiv_embeddedSphere_le e f hf s
  have h := Submodule.finrank_add_inf_finrank_orthogonal
    (K₁ := B.range) (K₂ := e.tangentImage (f s)) hle
  rw [LinearMap.finrank_range_of_inj hi,
    finrank_euclideanSpace_fin, e.finrank_tangentImage, inf_comm] at h
  change 3 + Module.finrank ℝ (sphereNormalSpace e f s) = 7 at h
  omega

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
