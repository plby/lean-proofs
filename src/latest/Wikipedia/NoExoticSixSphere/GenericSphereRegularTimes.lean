import Wikipedia.NoExoticSixSphere.ManifoldAffineGenericParameter
import Wikipedia.NoExoticSixSphere.SpatialIntersectionNativeTransversality

/-!
# Spatially transverse double points at almost every time

For a generic actual manifold family, each off-diagonal chart difference
has regular zeros in the joint time and spatial variables. Parametric Sard,
now using time as its parameter, makes its spatial zeros regular for almost
every time. Countable chart intersection and the native derivative formula
give self-transversality of the original sphere map at those times.
-/

noncomputable section

open Set Function TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (p : Parameters e)

def fixedParameterPairDomain (s z : SourceChart) (c : TargetChart n M) :
    Opens (ℝ × (Vector 3 × Vector 3)) :=
  ⟨(fun q ↦ (p, q)) ⁻¹' (pairDomain e r f hf s z c : Set _),
    (pairDomain e r f hf s z c).isOpen.preimage (continuous_const.prodMk continuous_id)⟩

theorem contDiffOn_fixedParameterDifference (s z : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (fun q ↦ chartDifference e r f s z c (p, q))
      (fixedParameterPairDomain e r f hf p s z c) :=
  (contDiffOn_chartDifference e r f hf s z c).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hq ↦ hq)

def RegularTimeInCharts (S : Set SourceChart) (C : Set (TargetChart n M)) (t : ℝ) : Prop :=
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : Vector 3 × Vector 3,
    (p, (t, x)) ∈ pairDomain e r f hf s z c →
    chartDifference e r f s z c (p, (t, x)) = 0 →
      Surjective (fderiv ℝ (fun y ↦ chartDifference e r f s z c (p, (t, y))) x)

theorem ae_regular_time_in_charts (μ : Measure ℝ) [IsAddHaarMeasure μ]
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable)
    (hgen : GenericInCharts e r f hf S C p) :
    ∀ᵐ t ∂μ, RegularTimeInCharts e r f hf p S C t := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ t ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : Vector 3 × Vector 3,
      (p, (t, x)) ∈ pairDomain e r f hf s.val z.val c.val →
      chartDifference e r f s.val z.val c.val (p, (t, x)) = 0 →
        Surjective (fderiv ℝ
          (fun y ↦ chartDifference e r f s.val z.val c.val (p, (t, y))) x) := by
    apply ae_all_iff.mpr
    intro s
    apply ae_all_iff.mpr
    intro z
    apply ae_all_iff.mpr
    intro c
    exact ParametricRegular.ae_parameters_on μ
      (fun q ↦ chartDifference e r f s.val z.val c.val (p, q))
      (fixedParameterPairDomain e r f hf p s.val z.val c.val)
      (contDiffOn_fixedParameterDifference e r f hf p s.val z.val c.val)
      (hgen.2 s.val s.property z.val z.property c.val c.property)
  exact h.mono fun t ht s hs z hz c hc ↦ ht ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩

end NoExoticSixSphere.ManifoldAffineSphereFamily

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (p : Parameters e)

theorem self_transverse_of_regular_time
    (hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)))
    (S : Set SourceChart) (C : Set (TargetChart 6 M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hmem : ∀ x, ambient e f p t x ∈ r.domain)
    (hreg : RegularTimeInCharts e r f hf p S C t) :
    ∀ x y : Sphere 3, x ≠ y → map e r f p t x = map e r f p t y →
      Surjective ((mfderiv (𝓡 3) (𝓡 6) (map e r f p t) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (map e r f p t) y)) := by
  intro x y hne hxy
  obtain ⟨s, hs, hxs⟩ := hS x
  obtain ⟨z, hz, hyz⟩ := hS y
  obtain ⟨c, hc, hxc⟩ := hC (map e r f p t x)
  have hyc : map e r f p t y ∈ c.source := hxy ▸ hxc
  have hx' : s.symm (s x) = x := s.left_inv hxs
  have hy' : z.symm (z y) = y := z.left_inv hyz
  have hq : (p, (t, (s x, z y))) ∈ pairDomain e r f hf s z c := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ((s x ∈ s.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
        ambient e f p t (s.symm (s x)) ∈ r.domain) ∧ map e r f p t (s.symm (s x)) ∈ c.source
      rw [hx']
      exact ⟨⟨⟨s.map_source hxs, ht⟩, hmem x⟩, hxc⟩
    · change ((z y ∈ z.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
        ambient e f p t (z.symm (z y)) ∈ r.domain) ∧ map e r f p t (z.symm (z y)) ∈ c.source
      rw [hy']
      exact ⟨⟨⟨z.map_source hyz, ht⟩, hmem y⟩, hyc⟩
    · change s.symm (s x) ≠ z.symm (z y)
      rwa [hx', hy']
  have hzero : chartDifference e r f s z c (p, (t, (s x, z y))) = 0 := by
    apply (chartDifference_zero_iff e r f hf s z c _ hq).mpr
    rwa [hx', hy']
  have hsp := hreg s hs z hz c hc (s x, z y) hq hzero
  exact IntersectionTrace.native_transverse_of_spatial_regular
    (map e r f p) (map e r f p) hP hP t x y s z c hxs hyz hxc hxy hsp

end NoExoticSixSphere.ManifoldAffineSphereFamily
