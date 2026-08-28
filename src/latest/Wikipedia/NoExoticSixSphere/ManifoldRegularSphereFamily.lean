import Wikipedia.NoExoticSixSphere.ManifoldSphereParity
import Wikipedia.NoExoticSixSphere.RegularFamilySpanningDisk
import Wikipedia.NoExoticSixSphere.FramedRegularSphereFamily

/-!
# Original-manifold sphere parity is invariant under regular homotopy

The sphere family is jointly smooth and every unit-interval slice is
immersive. Only its two endpoints must be injective. Compatible immersed
spanning disks with embedded endpoints are constructed, allowing
self-intersections throughout the intervening homotopy.

Existence of a regular homotopy between general homologous embeddings is not
asserted here.
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

theorem sphereParity_eq_of_regular_family (f : ℝ → Sphere 3 → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (hi₀ : Injective (f 0)) (hi₁ : Injective (f 1))
    (hd : ∀ t : unitInterval, ∀ s,
      Injective (mfderiv (𝓡 3) (𝓡 6) (f (t : ℝ)) s)) :
    e.sphereParity a (f 0) (hf.comp (contMDiff_const.prodMk contMDiff_id)) hi₀ (hd 0) =
      e.sphereParity a (f 1) (hf.comp (contMDiff_const.prodMk contMDiff_id)) hi₁ (hd 1) := by
  have hs (t : ℝ) : ContMDiff (𝓡 3) (𝓡 6) ∞ (f t) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  let F : ℝ → Sphere 3 → Vector e.ambientDimension := fun t ↦ e.toFun ∘ f t
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 e.ambientDimension) ∞ (uncurry F) :=
    e.smooth.comp hf
  have hFi : ∀ t ∈ ({0, 1} : Set ℝ), Injective (F t) := by
    intro t ht
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact e.closedEmbedding.injective.comp hi₀
    · exact e.closedEmbedding.injective.comp hi₁
  have hFd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s,
      Injective (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (F t) s) := by
    intro t ht s
    rw [show F t = e.toFun ∘ f t from rfl,
      mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
        ((hs t).mdifferentiableAt (by simp))]
    exact (e.injective_mfderiv (f t s)).comp (hd ⟨t, ht⟩ s)
  have hB : IsCompact ({0, 1} : Set ℝ) := isCompact_singleton.insert 0
  have hBK : ({0, 1} : Set ℝ) ⊆ Icc 0 1 := by
    intro t ht
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> norm_num
  obtain ⟨G, hG, hGe, hGi, hGb, hGa, V, hV, hSV, hGc⟩ :=
    exists_regular_family_spanningDisk isCompact_Icc hB hBK (pole 3) F hF hFi hFd
  let D (t : unitInterval) (ht : (t : ℝ) ∈ ({0, 1} : Set ℝ)) :
      DiskData (pole 3) (F (t : ℝ)) :=
    { toFun := G t
      smooth := hG.comp (contDiff_const.prodMk contDiff_id)
      embedded := hGe t ht
      immersive := hGi t t.property
      boundary := hGb t t.property
      avoids := hGa t t.property
      collar_eq := ⟨V, hV, hSV, hGc t t.property⟩ }
  let D₀ := D 0 (by simp)
  let D₁ := D 1 (by simp)
  have has : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3))
      𝓘(ℝ, Vector (e.ambientDimension - 6) →L[ℝ] Vector e.ambientDimension) ∞
      (fun q : ℝ × Sphere 3 ↦ (e.normalFrameOnSphere a (f q.1) q.2).val) :=
    a.contMDiff_orthonormal.comp hf
  have hN : e.ambientDimension = (e.ambientDimension - 6) + 6 :=
    (Nat.sub_add_cancel (e.dimension_le_ambient (f 0 (pole 3)))).symm
  have hp := DiskData.parityOfDimension_eq_of_regular_sphere_family hN (pole 3) F
    (fun t ↦ e.smooth.comp (hs t)) (fun t ↦ e.normalFrameOnSphere a (f t)) has
    (fun t ↦ e.normalFrameOnSphere_normal a (f t) (hs t)) D₀ D₁ G hG
    (fun t ↦ hGi t t.property) rfl rfl hV hSV (fun t ↦ hGc t t.property)
  rw [e.sphereParity_eq a (f 0) (hs 0) hi₀ (hd 0) D₀,
    e.sphereParity_eq a (f 1) (hs 1) hi₁ (hd 1) D₁]
  exact hp

end NoExoticSixSphere.EuclideanEmbedding
