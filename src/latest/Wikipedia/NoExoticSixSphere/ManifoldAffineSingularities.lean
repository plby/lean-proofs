import Wikipedia.NoExoticSixSphere.ManifoldChartDerivative
import Wikipedia.NoExoticSixSphere.ManifoldAffineGenericParameter

/-!
# Intrinsic singularities of the actual generic manifold family

The singular set uses the manifold derivative for the original sphere and
target atlases. Coordinate injectivity is equivalent to intrinsic injectivity.
The proved chartwise isolation therefore gives isolation on the actual source
manifold, rather than only a statement about coordinate representatives.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization

namespace SphereFamily

def singularParameters {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Vector n) M] (g : ℝ → Sphere 3 → M) : Set (ℝ × Sphere 3) :=
  {q | ¬ Injective (mfderiv (𝓡 3) (𝓡 n) (g q.1) q.2)}

end SphereFamily

namespace ManifoldAffineSphereFamily

open EuclideanEmbedding SphereFamily

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (p : Parameters e)

theorem injective_chartJet_iff
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f p)))
    (s : SourceChart) (c : TargetChart n M) (x : ℝ × Vector 3)
    (hx : (p, x) ∈ chartDomain e r f hf s c) :
    Injective (chartJet e r f s c (p, x)) ↔
      Injective (mfderiv (𝓡 3) (𝓡 n) (map e r f p x.1) (s.symm x.2)) := by
  have hslice : ContMDiff (𝓡 3) (𝓡 n) ∞ (map e r f p x.1) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  exact ManifoldCoordinates.injective_fderiv_in_charts_iff
    (map e r f p x.1) s c x.2 hx.1.1.1 hx.2 (hslice.mdifferentiableAt (by simp))

theorem isDiscrete_interior_singularParameters
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f p)))
    (S : Set SourceChart) (C : Set (TargetChart n M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hp : ∀ t x, ambient e f p t x ∈ r.domain)
    (hgen : GenericInCharts e r f hf S C p) :
    IsDiscrete ({q : ℝ × Sphere 3 | q.1 ∈ Ioo (0 : ℝ) 1} ∩
      singularParameters (n := n) (map e r f p)) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hS x.2
  obtain ⟨c, hc, hxc⟩ := hC (map e r f p x.1 x.2)
  let T := (OpenPartialHomeomorph.refl ℝ).prod s.toOpenPartialHomeomorph
  let U : Set (ℝ × Vector 3) := {z | (p, z) ∈ chartDomain e r f hf s c}
  let D : ℝ × Vector 3 → Vector 3 →L[ℝ] Vector n := fun z ↦ chartJet e r f s c (p, z)
  have hU : IsOpen U :=
    (chartDomain e r f hf s c).isOpen.preimage (continuous_const.prodMk continuous_id)
  have hxT : x ∈ T.source := ⟨mem_univ _, hxs⟩
  have hleft : s.symm (s x.2) = x.2 := s.left_inv hxs
  have hxU : T x ∈ U := by
    change ((s x.2 ∈ s.target ∧ x.1 ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f p x.1 (s.symm (s x.2)) ∈ r.domain) ∧
        map e r f p x.1 (s.symm (s x.2)) ∈ c.source
    rw [hleft]
    exact ⟨⟨⟨s.map_source hxs, hx.1⟩, hp _ _⟩, hxc⟩
  have hcompare (y : ℝ × Sphere 3) (hyT : y ∈ T.source) (hyU : T y ∈ U) :
      Injective (D (T y)) ↔
        Injective (mfderiv (𝓡 3) (𝓡 n) (map e r f p y.1) y.2) := by
    have h := injective_chartJet_iff e r f hf p hg s c (T y) hyU
    change Injective (D (T y)) ↔
      Injective (mfderiv (𝓡 3) (𝓡 n) (map e r f p y.1) (s.symm (s y.2))) at h
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

theorem injective_mfderiv_map_outside
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x : Sphere 3,
      Injective (mfderiv (𝓡 3) (𝓡 n) (f t) x))
    {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 n) (map e r f p t) x) := by
  have he : map e r f p t = f t := funext (map_eq_outside e r f p ht)
  rw [he]
  exact hext t ht x

theorem singularParameters_time_mem_Ioo
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x : Sphere 3,
      Injective (mfderiv (𝓡 3) (𝓡 n) (f t) x))
    {q : ℝ × Sphere 3} (hq : q ∈ singularParameters (n := n) (map e r f p)) :
    q.1 ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · by_contra ht
    exact hq (injective_mfderiv_map_outside e r f p hext (Or.inl (le_of_not_gt ht)) q.2)
  · by_contra ht
    exact hq (injective_mfderiv_map_outside e r f p hext (Or.inr (le_of_not_gt ht)) q.2)

theorem isDiscrete_singularParameters
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f p)))
    (S : Set SourceChart) (C : Set (TargetChart n M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hp : ∀ t x, ambient e f p t x ∈ r.domain)
    (hgen : GenericInCharts e r f hf S C p)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x : Sphere 3,
      Injective (mfderiv (𝓡 3) (𝓡 n) (f t) x)) :
    IsDiscrete (singularParameters (n := n) (map e r f p)) := by
  have he : {q : ℝ × Sphere 3 | q.1 ∈ Ioo (0 : ℝ) 1} ∩
      singularParameters (n := n) (map e r f p) = singularParameters (n := n) (map e r f p) := by
    ext q
    exact ⟨fun hq ↦ hq.2, fun hq ↦
      ⟨singularParameters_time_mem_Ioo e r f p hext hq, hq⟩⟩
  rw [← he]
  exact isDiscrete_interior_singularParameters e r f hf p hg S C hS hC hp hgen

end ManifoldAffineSphereFamily
end NoExoticSixSphere
