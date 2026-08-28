import Wikipedia.NoExoticSixSphere.ManifoldSphereParity
import Wikipedia.NoExoticSixSphere.FamilySpanningDisk
import Wikipedia.NoExoticSixSphere.FramedSphereFamily

/-!
# The original framed-manifold sphere parity is invariant under smooth isotopy

Only the jointly smooth sphere family and its slice embeddings and immersions
are supplied. A compatible jointly smooth spanning-disk family is constructed,
and the original normal framing supplies all varying boundary columns.

This theorem does not turn an arbitrary homotopy into an isotopy and does not
yet descend the parity to homology.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereParity_eq_of_smooth_family (f : ℝ → Sphere 3 → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (hi : ∀ t : unitInterval, Injective (f (t : ℝ)))
    (hd : ∀ t : unitInterval, ∀ s,
      Injective (mfderiv (𝓡 3) (𝓡 6) (f (t : ℝ)) s)) :
    e.sphereParity a (f 0) (hf.comp (contMDiff_const.prodMk contMDiff_id)) (hi 0) (hd 0) =
      e.sphereParity a (f 1) (hf.comp (contMDiff_const.prodMk contMDiff_id)) (hi 1) (hd 1) := by
  have hs (t : ℝ) : ContMDiff (𝓡 3) (𝓡 6) ∞ (f t) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  let F : ℝ → Sphere 3 → Vector e.ambientDimension := fun t ↦ e.toFun ∘ f t
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 e.ambientDimension) ∞ (uncurry F) :=
    e.smooth.comp hf
  have hFi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (F t) :=
    fun t ht ↦ e.closedEmbedding.injective.comp (hi ⟨t, ht⟩)
  have hFd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s,
      Injective (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (F t) s) := by
    intro t ht s
    rw [show F t = e.toFun ∘ f t from rfl,
      mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
        ((hs t).mdifferentiableAt (by simp))]
    exact (e.injective_mfderiv (f t s)).comp (hd ⟨t, ht⟩ s)
  obtain ⟨G, hG, hGe, hGi, hGb, hGa, V, hV, hSV, hGc⟩ :=
    exists_family_spanningDisk isCompact_Icc (pole 3) F hF hFi hFd
  let D (t : unitInterval) : DiskData (pole 3) (F (t : ℝ)) :=
    { toFun := G t
      smooth := hG.comp (contDiff_const.prodMk contDiff_id)
      embedded := hGe t t.property
      immersive := hGi t t.property
      boundary := hGb t t.property
      avoids := hGa t t.property
      collar_eq := ⟨V, hV, hSV, hGc t t.property⟩ }
  have has : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3))
      𝓘(ℝ, Vector (e.ambientDimension - 6) →L[ℝ] Vector e.ambientDimension) ∞
      (fun q : ℝ × Sphere 3 ↦ (e.normalFrameOnSphere a (f q.1) q.2).val) :=
    a.contMDiff_orthonormal.comp hf
  have hN : e.ambientDimension = (e.ambientDimension - 6) + 6 :=
    (Nat.sub_add_cancel (e.dimension_le_ambient (f 0 (pole 3)))).symm
  have hp := DiskData.parityOfDimension_eq_of_sphere_family hN (pole 3) F
    (fun t ↦ e.smooth.comp (hs t)) (fun t ↦ e.normalFrameOnSphere a (f t)) has
    (fun t ↦ e.normalFrameOnSphere_normal a (f t) (hs t)) D G hG (fun _ ↦ rfl)
  rw [e.sphereParity_eq a (f 0) (hs 0) (hi 0) (hd 0) (D 0),
    e.sphereParity_eq a (f 1) (hs 1) (hi 1) (hd 1) (D 1)]
  exact hp

end NoExoticSixSphere.EuclideanEmbedding
