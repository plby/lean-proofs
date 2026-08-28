import Wikipedia.HopfProblem.DegreeCollapseLowInternalSphereTube
import Wikipedia.HopfProblem.DegreeCollapseLowBoundaryTransverse
import Wikipedia.NoExoticSixSphere.CompactLocalDiffeomorph
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!

# Actual embedded low-dimensional tubes in the original manifold

Compactness of the original sphere and the actual native local inverses
supply one positive closed transverse radius. The entire embedded tube
lies in the actual retraction domain and remains a local diffeomorphism
at every point. No new atlas or abstract tube is substituted.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M) (f : NoExoticSixSphere.Sphere d → M)
  (C : NoExoticSixSphere.Sphere d → Vector (7 - d) →L[ℝ] Vector e.ambientDimension)
  (r : EuclideanEmbedding.TubularRetraction e)
  (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
  (hC : ContMDiff (𝓡 d) 𝓘(ℝ, Vector (7 - d) →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = sphereNormalSpace e f s)

include hf hi hC hd hiC hCr in
theorem exists_embedded_internalSphereTube :
    ∃ ε : ℝ, 0 < ε ∧
      IsClosedEmbedding (fun p : NoExoticSixSphere.Sphere d × closedBall (0 : Vector (7 - d)) ε ↦
        internalSphereTube e f C r (p.1, p.2.val)) ∧
      ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) ε,
        (s, v) ∈ sphereTubeDomain e f C r ∧
          IsLocalDiffeomorphAt ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) ∞
            (internalSphereTube e f C r) (s, v) := by
  let K : Set (NoExoticSixSphere.Sphere d × Vector (7 - d)) := univ ×ˢ {0}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hKi : InjOn (internalSphereTube e f C r) K := by
    rintro ⟨s, v⟩ ⟨_, hv⟩ ⟨t, w⟩ ⟨_, hw⟩ he
    rcases mem_singleton_iff.mp hv with rfl
    rcases mem_singleton_iff.mp hw with rfl
    exact Prod.ext (hi (by simpa only [internalSphereTube_core e] using he)) rfl
  have hKl : ∀ p ∈ K, IsLocalDiffeomorphAt ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) ∞
      (internalSphereTube e f C r) p := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact isLocalDiffeomorphAt_internalSphereTube_core e f C r hf hC hd hiC hCr s
  have hKU : K ⊆ sphereTubeDomain e f C r := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact core_mem_sphereTubeDomain e f C r s
  obtain ⟨V, hV, hKV, hVU, hVi, hVl⟩ := exists_injective_localDiffeomorph_neighborhood hK hKi hKl
    (isOpen_sphereTubeDomain e f C r hf hC) hKU
  obtain ⟨ε, hε, hεV⟩ := exists_uniform_closedProductTube hV (fun s ↦ hKV ⟨mem_univ s, rfl⟩)
  have hmem (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d))
      (hv : v ∈ closedBall (0 : Vector (7 - d)) ε) : (s, v) ∈ V :=
    hεV s v (by simpa only [mem_closedBall, dist_zero_right] using hv)
  let j : NoExoticSixSphere.Sphere d × closedBall (0 : Vector (7 - d)) ε →
      NoExoticSixSphere.Sphere d × Vector (7 - d) :=
    fun p ↦ (p.1, p.2.val)
  have hj : Continuous j := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun p : NoExoticSixSphere.Sphere d × closedBall (0 : Vector (7 - d)) ε ↦
      internalSphereTube e f C r (p.1, p.2.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := j)
      (hVl (p.1, p.2.val) (hmem p.1 p.2 p.2.property)).contMDiffAt.continuousAt hj.continuousAt
  refine ⟨ε, hε, hc.isClosedEmbedding ?_, ?_⟩
  · intro p q hpq
    have h := hVi (hmem p.1 p.2 p.2.property) (hmem q.1 q.2 q.2.property) hpq
    exact Prod.ext (congrArg (Prod.fst : NoExoticSixSphere.Sphere d × Vector (7 - d) →
        NoExoticSixSphere.Sphere d) h)
      (Subtype.ext (congrArg (Prod.snd : NoExoticSixSphere.Sphere d × Vector (7 - d) →
        Vector (7 - d)) h))
  · intro s v hv
    exact ⟨hVU (hmem s v hv), hVl (s, v) (hmem s v hv)⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
