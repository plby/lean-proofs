import Wikipedia.NoExoticSixSphere.EmbeddedCompactSphereTube
import Wikipedia.NoExoticSixSphere.InjectiveLocalDiffeomorph
import Wikipedia.NoExoticSixSphere.SmoothCompressedProductTube

/-!
# A smooth whole-normal-coordinate sphere tube inside a prescribed open set

Restrict the actual compact-image tube to a common injective neighborhood
of the original zero section, retaining the chosen open target. Smooth
radial compression gives unrestricted normal coordinates and a smooth
partial inverse. The original sphere is fixed pointwise at the core.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector q →L[ℝ] Vector e.ambientDimension)
  (r : e.RetractionNear (range f))
  (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f) (hi : Injective f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector q →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)

include r hf hi hC hd hiC hCr in
theorem exists_compactSphereSmoothOpenTube_in_open (U : Set M) (hU : IsOpen U)
    (hfU : ∀ s, f s ∈ U) :
    ∃ Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 q)) (𝓡 n) (Sphere 3 × Vector q) M ∞,
      Φ.source = univ ∧ Φ.target ⊆ U ∧ ∀ s, Φ (s, 0) = f s := by
  let K : Set (Sphere 3 × Vector q) := univ ×ˢ {0}
  let W : Set (Sphere 3 × Vector q) :=
    e.compactSphereTubeDomain f C r ∩ (e.compactSphereTube f C r) ⁻¹' U
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hKi : InjOn (e.compactSphereTube f C r) K := by
    rintro ⟨s, v⟩ ⟨_, hv⟩ ⟨s', v'⟩ ⟨_, hv'⟩ he
    rcases mem_singleton_iff.mp hv with rfl
    rcases mem_singleton_iff.mp hv' with rfl
    exact Prod.ext (hi (by simpa only [e.compactSphereTube_core] using he)) rfl
  have hKl : ∀ p ∈ K, IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 q)) (𝓡 n) ∞
      (e.compactSphereTube f C r) p := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact e.isLocalDiffeomorphAt_compactSphereTube_core f C r hf hC hd hiC hCr s
  have hW : IsOpen W :=
    (e.contMDiffOn_compactSphereTube f C r hf hC).continuousOn.isOpen_inter_preimage
      (e.isOpen_compactSphereTubeDomain f C r hf hC) hU
  have hKW : K ⊆ W := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    refine ⟨e.core_mem_compactSphereTubeDomain f C r s, ?_⟩
    change e.compactSphereTube f C r (s, 0) ∈ U
    rw [e.compactSphereTube_core]
    exact hfU s
  obtain ⟨V, hV, hKV, hVW, hVi, hVl⟩ :=
    exists_injective_localDiffeomorph_neighborhood hK hKi hKl hW hKW
  have hl : IsLocalDiffeomorphOn ((𝓡 3).prod (𝓡 q)) (𝓡 n) ∞
      (e.compactSphereTube f C r) V := fun p ↦ hVl p p.property
  let Ψ := injectiveLocalPartialDiffeomorph hV hVi hl
  obtain ⟨ε, hε, hεV⟩ := exists_uniform_closedProductTube hV
    (fun s ↦ hKV ⟨mem_univ s, rfl⟩)
  refine ⟨CompressedProductTube.smoothTube Ψ ε hε,
    CompressedProductTube.smoothTube_source Ψ ε hε hεV, ?_, ?_⟩
  · intro y hy
    have hyΨ : y ∈ Ψ.target := hy.1
    change y ∈ e.compactSphereTube f C r '' V at hyΨ
    obtain ⟨x, hx, rfl⟩ := hyΨ
    exact (hVW hx).2
  · intro s
    exact (CompressedProductTube.smoothTube_zero Ψ ε hε s).trans
      (e.compactSphereTube_core f C r s)

end NoExoticSixSphere.EuclideanEmbedding
