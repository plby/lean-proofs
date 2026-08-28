import Wikipedia.NoExoticSixSphere.RelativeSphereIntersectionGeneric
import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereProtectedDerivative
import Wikipedia.NoExoticSixSphere.SpatialIntersectionNativeTransversality

/-!
# Spatially transverse relative intersections at almost every time

Time-parametric Sard makes the actual active intersections spatially regular.
On the cutoff zero set, exact native derivative preservation retains any
specified transversality with the unchanged second sphere.
-/

noncomputable section

open Set Function TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RelativeSphereIntersectionFamily

open GLOrthonormalization EuclideanEmbedding
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f g : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
  (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (p : Parameters e)

def fixedParameterDomain (s z : SourceChart) (c : TargetChart n M) :
    Opens (ℝ × (Vector 3 × Vector 3)) :=
  ⟨(fun q ↦ (p, q)) ⁻¹' (domain e r f g χ hf hg hχ s z c : Set _),
    (domain e r f g χ hf hg hχ s z c).isOpen.preimage
      (continuous_const.prodMk continuous_id)⟩

theorem contDiffOn_fixedParameterDifference (s z : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (fun q ↦ difference e r f g χ s z c (p, q))
      (fixedParameterDomain e r f g χ hf hg hχ p s z c) :=
  (contDiffOn_difference e r f g χ hf hg hχ s z c).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hq ↦ hq)

def RegularTimeInCharts (S : Set SourceChart) (C : Set (TargetChart n M)) (t : ℝ) : Prop :=
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : Vector 3 × Vector 3,
    (p, (t, x)) ∈ domain e r f g χ hf hg hχ s z c →
    difference e r f g χ s z c (p, (t, x)) = 0 →
      Surjective (fderiv ℝ (fun y ↦ difference e r f g χ s z c (p, (t, y))) x)

theorem ae_regular_time_in_charts (μ : Measure ℝ) [IsAddHaarMeasure μ]
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable)
    (hgen : GenericInCharts e r f g χ hf hg hχ S C p) :
    ∀ᵐ t ∂μ, RegularTimeInCharts e r f g χ hf hg hχ p S C t := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ t ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : Vector 3 × Vector 3,
      (p, (t, x)) ∈ domain e r f g χ hf hg hχ s.val z.val c.val →
      difference e r f g χ s.val z.val c.val (p, (t, x)) = 0 →
      Surjective (fderiv ℝ
        (fun y ↦ difference e r f g χ s.val z.val c.val (p, (t, y))) x) := by
    apply ae_all_iff.mpr
    intro s
    apply ae_all_iff.mpr
    intro z
    apply ae_all_iff.mpr
    intro c
    exact ParametricRegular.ae_parameters_on μ
      (fun q ↦ difference e r f g χ s.val z.val c.val (p, q))
      (fixedParameterDomain e r f g χ hf hg hχ p s.val z.val c.val)
      (contDiffOn_fixedParameterDifference e r f g χ hf hg hχ p s.val z.val c.val)
      (hgen s.val s.property z.val z.property c.val c.property)
  exact h.mono fun t ht s hs z hz c hc ↦ ht ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩

end NoExoticSixSphere.RelativeSphereIntersectionFamily

namespace NoExoticSixSphere.RelativeSphereIntersectionFamily

open GLOrthonormalization EuclideanEmbedding
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)
  (f g : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (hn : ∀ z, 0 ≤ χ z) (p : Parameters e)

include hn in
theorem pair_transverse_of_regular_time
    (hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞
      (uncurry (SpatiallyRelativeSphereFamily.map e r f χ p)))
    (S : Set SourceChart) (C : Set (TargetChart 6 M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hmem : ∀ x, SpatiallyRelativeSphereFamily.ambient e f χ p t x ∈ r.domain)
    (hreg : RegularTimeInCharts e r f g χ hf hg hχ p S C t)
    (hprotected : ∀ x y : Sphere 3, χ x = 0 → f t x = g t y →
      Surjective ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g t) y))) :
    ∀ x y : Sphere 3, SpatiallyRelativeSphereFamily.map e r f χ p t x = g t y →
      Surjective ((mfderiv (𝓡 3) (𝓡 6) (SpatiallyRelativeSphereFamily.map e r f χ p t) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g t) y)) := by
  intro x y hxy
  by_cases hxχ : χ x = 0
  · rw [SpatiallyRelativeSphereFamily.map_eq_zero_cutoff e r f χ p t x hxχ] at hxy
    rw [SpatiallyRelativeSphereFamily.mfderiv_map_of_zero_cutoff e r f χ hf hχ hn p t x hxχ]
    exact hprotected x y hxχ hxy
  obtain ⟨s, hs, hxs⟩ := hS x
  obtain ⟨z, hz, hyz⟩ := hS y
  obtain ⟨c, hc, hxc⟩ := hC (SpatiallyRelativeSphereFamily.map e r f χ p t x)
  have hyc : g t y ∈ c.source := hxy ▸ hxc
  have hq := mem_domain_of_charts e r f g χ hf hg hχ s z c p t x y ht hxχ hxs hyz
    (hmem x) hxc hyc
  have hx' : s.symm (s x) = x := s.left_inv hxs
  have hy' : z.symm (z y) = y := z.left_inv hyz
  have hzero : difference e r f g χ s z c (p, t, s x, z y) = 0 := by
    rw [difference_apply, hx', hy', hxy, sub_self]
  have hsp := hreg s hs z hz c hc (s x, z y) hq hzero
  have heq : (fun q : Vector 3 × Vector 3 ↦ difference e r f g χ s z c (p, t, q)) =
      fun q ↦ c (SpatiallyRelativeSphereFamily.map e r f χ p t (s.symm q.1)) -
        c (g t (z.symm q.2)) := by
    funext q
    exact difference_apply e r f g χ s z c (p, t, q)
  rw [heq] at hsp
  exact IntersectionTrace.native_transverse_of_spatial_regular
    (SpatiallyRelativeSphereFamily.map e r f χ p) g hP hg t x y s z c hxs hyz hxc hxy hsp

end NoExoticSixSphere.RelativeSphereIntersectionFamily
