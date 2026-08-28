import Wikipedia.HopfProblem.DegreeCollapseSevenInternalSphereTube
import Wikipedia.HopfProblem.DegreeCollapseSevenBoundaryTransverse
import Wikipedia.NoExoticSixSphere.CompactLocalDiffeomorph
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# The original seven-manifold tube and its genuine local inverses

Retraction of the actual ambient tube retains the native atlas. The exact
core derivative is invertible, and compactness of the original sphere
supplies a positive embedded closed product in the actual retraction domain.
The retraction is supplied explicitly; no filling is inferred.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 4 →L[ℝ] Vector e.ambientDimension)
  (r : EuclideanEmbedding.TubularRetraction e)
  (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = SevenSurgery.sphereNormalSpace e f s)

include hf hi hC hd hiC hCr in
theorem exists_embedded_internalSphereTube :
    ∃ ε : ℝ, 0 < ε ∧
      IsClosedEmbedding (fun p : Sphere 3 × closedBall (0 : Vector 4) ε ↦
        SevenSurgery.internalSphereTube e f C r (p.1, p.2.val)) ∧
      ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) ε,
        (s, v) ∈ SevenSurgery.sphereTubeDomain e f C r ∧
          IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞
            (SevenSurgery.internalSphereTube e f C r) (s, v) := by
  let K : Set (Sphere 3 × Vector 4) := univ ×ˢ {0}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hKi : InjOn (SevenSurgery.internalSphereTube e f C r) K := by
    rintro ⟨s, v⟩ ⟨_, hv⟩ ⟨t, w⟩ ⟨_, hw⟩ he
    rcases mem_singleton_iff.mp hv with rfl
    rcases mem_singleton_iff.mp hw with rfl
    exact Prod.ext (hi (by simpa only [SevenSurgery.internalSphereTube_core e] using he)) rfl
  have hKl : ∀ p ∈ K, IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞
      (SevenSurgery.internalSphereTube e f C r) p := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact SevenSurgery.isLocalDiffeomorphAt_internalSphereTube_core e f C r hf hC hd hiC hCr s
  have hKU : K ⊆ SevenSurgery.sphereTubeDomain e f C r := by
    rintro ⟨s, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact SevenSurgery.core_mem_sphereTubeDomain e f C r s
  obtain ⟨V, hV, hKV, hVU, hVi, hVl⟩ := exists_injective_localDiffeomorph_neighborhood hK hKi hKl
    (SevenSurgery.isOpen_sphereTubeDomain e f C r hf hC) hKU
  obtain ⟨ε, hε, hεV⟩ := exists_uniform_closedProductTube hV (fun s ↦ hKV ⟨mem_univ s, rfl⟩)
  have hmem (s : Sphere 3) (v : Vector 4) (hv : v ∈ closedBall (0 : Vector 4) ε) : (s, v) ∈ V :=
    hεV s v (by simpa only [mem_closedBall, dist_zero_right] using hv)
  let j : Sphere 3 × closedBall (0 : Vector 4) ε → Sphere 3 × Vector 4 :=
    fun p ↦ (p.1, p.2.val)
  have hj : Continuous j := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun p : Sphere 3 × closedBall (0 : Vector 4) ε ↦
      SevenSurgery.internalSphereTube e f C r (p.1, p.2.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := j)
      (hVl (p.1, p.2.val) (hmem p.1 p.2 p.2.property)).contMDiffAt.continuousAt hj.continuousAt
  refine ⟨ε, hε, hc.isClosedEmbedding ?_, ?_⟩
  · intro p q hpq
    have h := hVi (hmem p.1 p.2 p.2.property) (hmem q.1 q.2 q.2.property) hpq
    exact Prod.ext (congrArg (Prod.fst : Sphere 3 × Vector 4 → Sphere 3) h)
      (Subtype.ext (congrArg (Prod.snd : Sphere 3 × Vector 4 → Vector 4) h))
  · intro s v hv
    exact ⟨hVU (hmem s v hv), hVl (s, v) (hmem s v hv)⟩

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
