import Wikipedia.NoExoticSixSphere.EmbeddedInternalSphereTube
import Wikipedia.NoExoticSixSphere.LocalHomeomorphOnPartial
import Wikipedia.NoExoticSixSphere.CompressedProductTube

/-!
# A whole-normal-coordinate open tube in the original manifold

The genuine internal sphere tube is injective and locally invertible
on one open neighborhood of its compact zero section. Package that
same map as a partial homeomorphism and compress the normal coordinate
into a uniform product ball. This constructs an open embedding of the
entire normal product with exactly the original sphere as its core.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 3 →L[ℝ] Vector e.ambientDimension) (r : TubularRetraction e)
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)

include r hf hi hC hd hiC hCr in
/-- A constructed actual open tube whose zero section is the original framed embedded sphere. -/
theorem exists_internalSphereOpenTube :
    ∃ τ : C(Sphere 3 × Vector 3, M), IsOpenEmbedding τ ∧ ∀ s, τ (s, 0) = f s := by
  let K : Set (Sphere 3 × Vector 3) := univ ×ˢ {0}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hKi : InjOn (e.internalSphereTube f C r) K := by
    rintro ⟨s, v⟩ ⟨_, hv⟩ ⟨t, w⟩ ⟨_, hw⟩ he
    rcases mem_singleton_iff.mp hv with rfl
    rcases mem_singleton_iff.mp hw with rfl
    exact Prod.ext (hi (by simpa only [e.internalSphereTube_core] using he)) rfl
  have hKl : ∀ p ∈ K, IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞
      (e.internalSphereTube f C r) p := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact e.isLocalDiffeomorphAt_internalSphereTube_core f C r hf hC hd hiC hCr s
  have hKU : K ⊆ e.sphereTubeDomain f C r := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact e.core_mem_sphereTubeDomain f C r s
  obtain ⟨V, hV, hKV, _hVU, hVi, hVl⟩ :=
    exists_injective_localDiffeomorph_neighborhood hK hKi hKl
      (e.isOpen_sphereTubeDomain f C r hf hC) hKU
  have hl : IsLocalDiffeomorphOn ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞
      (e.internalSphereTube f C r) V := fun p => hVl p p.property
  let Φ := LocalHomeomorphOnPartial.partialHomeomorph (e.internalSphereTube f C r)
    V hV hl.isLocalHomeomorphOn hVi
  obtain ⟨ε, hε, hεV⟩ := exists_uniform_closedProductTube hV
    (fun s => hKV ⟨mem_univ s, rfl⟩)
  have hτ := CompressedProductTube.isOpenEmbedding_map Φ ε hε hεV
  refine ⟨⟨CompressedProductTube.map Φ ε, hτ.continuous⟩, hτ, ?_⟩
  intro s
  exact (CompressedProductTube.map_zero Φ ε s).trans (e.internalSphereTube_core f C r s)

end NoExoticSixSphere.EuclideanEmbedding
