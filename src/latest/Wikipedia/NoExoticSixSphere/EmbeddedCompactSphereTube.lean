import Wikipedia.NoExoticSixSphere.CompactSphereTube
import Wikipedia.NoExoticSixSphere.CompactLocalDiffeomorph
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# A genuine embedded sphere product from a compact-image retraction

The actual internal tube is a local diffeomorphism on the compact zero section.
Compact injectivity and the product tube lemma give one positive closed-ball
radius on which it embeds and remains a local diffeomorphism. The tube stays
inside the actual local retraction domain and retains the original manifold
atlas. The manifold itself need not be compact.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector q →L[ℝ] Vector e.ambientDimension) (r : e.RetractionNear (range f))
  (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f) (hi : Injective f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector q →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)

include hf hi hC hd hiC hCr in
theorem exists_embedded_compactSphereTube :
    ∃ ε : ℝ, 0 < ε ∧
      IsClosedEmbedding (fun p : Sphere 3 × closedBall (0 : Vector q) ε ↦
        e.compactSphereTube f C r (p.1, p.2.val)) ∧
      ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector q) ε,
        (s, v) ∈ e.compactSphereTubeDomain f C r ∧
          IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 q)) (𝓡 n) ∞
            (e.compactSphereTube f C r) (s, v) := by
  let K : Set (Sphere 3 × Vector q) := univ ×ˢ {0}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hKi : InjOn (e.compactSphereTube f C r) K := by
    rintro ⟨s, v⟩ ⟨_, hv⟩ ⟨t, w⟩ ⟨_, hw⟩ he
    rcases mem_singleton_iff.mp hv with rfl
    rcases mem_singleton_iff.mp hw with rfl
    exact Prod.ext (hi (by simpa only [e.compactSphereTube_core] using he)) rfl
  have hKl : ∀ p ∈ K, IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 q)) (𝓡 n) ∞
      (e.compactSphereTube f C r) p := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact e.isLocalDiffeomorphAt_compactSphereTube_core f C r hf hC hd hiC hCr s
  have hKU : K ⊆ e.compactSphereTubeDomain f C r := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact e.core_mem_compactSphereTubeDomain f C r s
  obtain ⟨V, hV, hKV, hVU, hVi, hVl⟩ := exists_injective_localDiffeomorph_neighborhood hK hKi hKl
    (e.isOpen_compactSphereTubeDomain f C r hf hC) hKU
  obtain ⟨ε, hε, hεV⟩ := exists_uniform_closedProductTube hV (fun s ↦ hKV ⟨mem_univ s, rfl⟩)
  have hmem (s : Sphere 3) (v : Vector q) (hv : v ∈ closedBall (0 : Vector q) ε) : (s, v) ∈ V :=
    hεV s v (by simpa only [mem_closedBall, dist_zero_right] using hv)
  let j : Sphere 3 × closedBall (0 : Vector q) ε → Sphere 3 × Vector q :=
    fun p ↦ (p.1, p.2.val)
  have hj : Continuous j := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun p : Sphere 3 × closedBall (0 : Vector q) ε ↦
      e.compactSphereTube f C r (p.1, p.2.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := j)
      (hVl (p.1, p.2.val) (hmem p.1 p.2 p.2.property)).contMDiffAt.continuousAt hj.continuousAt
  refine ⟨ε, hε, hc.isClosedEmbedding ?_, ?_⟩
  · intro p z hpz
    have h := hVi (hmem p.1 p.2 p.2.property) (hmem z.1 z.2 z.2.property) hpz
    exact Prod.ext (congrArg (Prod.fst : Sphere 3 × Vector q → Sphere 3) h)
      (Subtype.ext (congrArg (Prod.snd : Sphere 3 × Vector q → Vector q) h))
  · intro s v hv
    exact ⟨hVU (hmem s v hv), hVl (s, v) (hmem s v hv)⟩

include hf hi hC hd hiC hCr in
theorem exists_compactSphereTube :
    ∃ R : e.RetractionNear (range f), ∃ ε : ℝ, 0 < ε ∧
      IsClosedEmbedding (fun p : Sphere 3 × closedBall (0 : Vector q) ε ↦
        e.compactSphereTube f C R (p.1, p.2.val)) ∧
      ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector q) ε,
        (s, v) ∈ e.compactSphereTubeDomain f C R ∧
          IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 q)) (𝓡 n) ∞
            (e.compactSphereTube f C R) (s, v) := by
  let : Nonempty M := ⟨f (Stiefel.pole 3)⟩
  obtain ⟨R⟩ := e.nonempty_retractionNear (isCompact_range hf.continuous)
  obtain ⟨ε, hε, he, hl⟩ := e.exists_embedded_compactSphereTube f C R hf hi hC hd hiC hCr
  exact ⟨R, ε, hε, he, hl⟩

end NoExoticSixSphere.EuclideanEmbedding
