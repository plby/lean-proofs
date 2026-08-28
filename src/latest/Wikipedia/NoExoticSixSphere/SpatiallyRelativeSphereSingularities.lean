import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereGenericParameter
import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereProtectedDerivative
import Wikipedia.NoExoticSixSphere.ManifoldAffineSingularities

/-!
# Isolated native singularities outside the protected source region

The relative chartwise rank theorem isolates every active singularity.
When the original maps are immersive on the zero set of a nonnegative cutoff,
the proved native derivative equality excludes protected singularities too.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SpatiallyRelativeSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (p : Parameters e)

theorem injective_chartJet_iff
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f χ p)))
    (s : SourceChart) (c : TargetChart n M) (x : ℝ × Vector 3)
    (hx : (p, x) ∈ chartDomain e r f χ hf hχ s c) :
    Injective (chartJet e r f χ s c (p, x)) ↔
      Injective (mfderiv (𝓡 3) (𝓡 n) (map e r f χ p x.1) (s.symm x.2)) := by
  have hslice : ContMDiff (𝓡 3) (𝓡 n) ∞ (map e r f χ p x.1) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  exact ManifoldCoordinates.injective_fderiv_in_charts_iff
    (map e r f χ p x.1) s c x.2 hx.1.1.1 hx.2 (hslice.mdifferentiableAt (by simp))

theorem isDiscrete_active_singularParameters
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f χ p)))
    (S : Set SourceChart) (C : Set (TargetChart n M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hp : ∀ t x, ambient e f χ p t x ∈ r.domain)
    (hgen : GenericInCharts e r f χ hf hχ S C p) :
    IsDiscrete ({q : ℝ × Sphere 3 | q.1 ∈ Ioo (0 : ℝ) 1 ∧ χ q.2 ≠ 0} ∩
      singularParameters (n := n) (map e r f χ p)) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hS x.2
  obtain ⟨c, hc, hxc⟩ := hC (map e r f χ p x.1 x.2)
  let T := (OpenPartialHomeomorph.refl ℝ).prod s.toOpenPartialHomeomorph
  let U : Set (ℝ × Vector 3) := {z | (p, z) ∈ activeChartDomain e r f χ hf hχ s c}
  let D : ℝ × Vector 3 → Vector 3 →L[ℝ] Vector n := fun z ↦ chartJet e r f χ s c (p, z)
  have hU : IsOpen U :=
    (activeChartDomain e r f χ hf hχ s c).isOpen.preimage
      (continuous_const.prodMk continuous_id)
  have hxT : x ∈ T.source := ⟨mem_univ _, hxs⟩
  have hleft : s.symm (s x.2) = x.2 := s.left_inv hxs
  have hxU : T x ∈ U := by
    change (((s x.2 ∈ s.target ∧ x.1 ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f χ p x.1 (s.symm (s x.2)) ∈ r.domain) ∧
        map e r f χ p x.1 (s.symm (s x.2)) ∈ c.source) ∧ χ (s.symm (s x.2)) ≠ 0
    rw [hleft]
    exact ⟨⟨⟨⟨s.map_source hxs, hx.1.1⟩, hp _ _⟩, hxc⟩, hx.1.2⟩
  have hcompare (y : ℝ × Sphere 3) (hyT : y ∈ T.source) (hyU : T y ∈ U) :
      Injective (D (T y)) ↔
        Injective (mfderiv (𝓡 3) (𝓡 n) (map e r f χ p y.1) y.2) := by
    have h := injective_chartJet_iff e r f χ hf hχ p hg s c (T y) hyU.1
    change Injective (D (T y)) ↔
      Injective (mfderiv (𝓡 3) (𝓡 n) (map e r f χ p y.1) (s.symm (s y.2))) at h
    have hlefty : s.symm (s y.2) = y.2 := s.left_inv hyT.2
    rw [hlefty] at h
    exact h
  have hxD : ¬ Injective (D (T x)) := (hcompare x hxT hxU).not.mpr hx.2
  have hdis : IsDiscrete (U ∩ {z | ¬ Injective (D z)}) := (hgen.1 s hs c hc).isolated
  obtain ⟨V, hV, hVe⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdis (T x) ⟨hxU, hxD⟩
  have hxV : T x ∈ V := by
    have hm : T x ∈ V ∩ (U ∩ {z | ¬ Injective (D z)}) := by
      rw [hVe]
      exact mem_singleton _
    exact hm.1
  refine ⟨T.source ∩ T ⁻¹' (U ∩ V),
    T.continuousOn.isOpen_inter_preimage T.open_source (hU.inter hV), ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyT, hyU, hyV⟩, hy⟩
    have hyD : ¬ Injective (D (T y)) := (hcompare y hyT hyU).not.mpr hy.2
    have he : T y = T x := by
      apply mem_singleton_iff.mp
      rw [← hVe]
      exact ⟨hyV, hyU, hyD⟩
    exact mem_singleton_iff.mpr (T.injOn hyT hxT he)
  · rintro rfl
    exact ⟨⟨hxT, hxU, hxV⟩, hx⟩

theorem isDiscrete_interior_singularParameters [IsManifold (𝓡 n) ∞ M]
    (hn : ∀ z, 0 ≤ χ z)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f χ p)))
    (S : Set SourceChart) (C : Set (TargetChart n M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hp : ∀ t x, ambient e f χ p t x ∈ r.domain)
    (hgen : GenericInCharts e r f χ hf hχ S C p)
    (hi : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, χ x = 0 →
      Injective (mfderiv (𝓡 3) (𝓡 n) (f t) x)) :
    IsDiscrete ({q : ℝ × Sphere 3 | q.1 ∈ Ioo (0 : ℝ) 1} ∩
      singularParameters (n := n) (map e r f χ p)) := by
  have he : ({q : ℝ × Sphere 3 | q.1 ∈ Ioo (0 : ℝ) 1} ∩
      singularParameters (n := n) (map e r f χ p)) =
      ({q : ℝ × Sphere 3 | q.1 ∈ Ioo (0 : ℝ) 1 ∧ χ q.2 ≠ 0} ∩
        singularParameters (n := n) (map e r f χ p)) := by
    ext q
    constructor
    · rintro ⟨ht, hsing⟩
      refine ⟨⟨ht, ?_⟩, hsing⟩
      intro hzero
      apply hsing
      rw [mfderiv_map_of_zero_cutoff e r f χ hf hχ hn p q.1 q.2 hzero]
      exact hi q.1 ht q.2 hzero
    · exact fun h ↦ ⟨h.1.1, h.2⟩
  rw [he]
  exact isDiscrete_active_singularParameters e r f χ hf hχ p hg S C hS hC hp hgen

end NoExoticSixSphere.SpatiallyRelativeSphereFamily
