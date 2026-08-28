import Wikipedia.NoExoticSixSphere.SpatialIntersectionGenericParameter
import Wikipedia.NoExoticSixSphere.SpatialIntersectionNativeTransversality

/-!
# A smooth sphere map has an actual transverse representative in its homotopy class

A fixed-time generic affine parameter makes the first map transverse to the
unchanged second map. The parameter is chosen in a uniform tubular ball.
Scaling it to zero stays in that ball and gives a genuine continuous homotopy
from the original map, not only an assertion about a chosen generic model.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldIntersectionFamily

open GLOrthonormalization EuclideanEmbedding ManifoldAffineSphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

theorem native_transverse_of_spatial_generic (S : Set SourceChart) (C : Set (TargetChart 6 M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source) (t : ℝ) (ht : t ∈ Ioo 0 1)
    (p : Parameters e) (hp : ∀ x, ambient e f p t x ∈ r.domain)
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞
      (uncurry (ManifoldAffineSphereFamily.map e r f p)))
    (hgen : SpatialGenericInCharts e r f g hf hg S C t p) :
    ∀ x y, ManifoldAffineSphereFamily.map e r f p t x = g t y →
      Surjective ((mfderiv (𝓡 3) (𝓡 6) (ManifoldAffineSphereFamily.map e r f p t) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g t) y)) := by
  intro x y hxy
  obtain ⟨s, hs, hxs⟩ := hS x
  obtain ⟨z, hz, hyz⟩ := hS y
  obtain ⟨c, hc, hxc⟩ := hC (ManifoldAffineSphereFamily.map e r f p t x)
  have hyc : g t y ∈ c.source := hxy ▸ hxc
  have hq : (p, (s x, z y)) ∈ spatialDomain e r f g hf hg s z c t :=
    mem_domain_of_charts e r f g hf hg s z c p t x y ht hxs hyz (hp x) hxc hyc
  have hx' : s.symm (s x) = x := s.left_inv hxs
  have hy' : z.symm (z y) = y := z.left_inv hyz
  have hzero : spatialDifference e r f g s z c t (p, (s x, z y)) = 0 := by
    change difference e r f g s z c (p, (t, (s x, z y))) = 0
    rw [difference_apply, hx', hy', hxy, sub_self]
  have hd := hgen s hs z hz c hc (s x, z y) hq hzero
  have heq : (fun q ↦ spatialDifference e r f g s z c t (p, q)) =
      fun q ↦ IntersectionTrace.coordinateDifference
        (ManifoldAffineSphereFamily.map e r f p) g s z c (t, q) := by
    funext q
    exact difference_apply e r f g s z c (p, (t, q))
  rw [heq] at hd
  exact IntersectionTrace.native_transverse_of_spatial_regular
    (ManifoldAffineSphereFamily.map e r f p) g hF hg t x y s z c hxs hyz hxc hxy hd

end NoExoticSixSphere.ManifoldIntersectionFamily

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization ManifoldAffineSphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_smooth_transverse_homotopic (f g : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) :
    ∃ F : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ F ∧ f.Homotopic F ∧
      ∀ x y, F x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) F x).coprod (mfderiv (𝓡 3) (𝓡 6) g y)) := by
  let f₀ : ℝ → Sphere 3 → M := fun _ x ↦ f x
  let g₀ : ℝ → Sphere 3 → M := fun _ x ↦ g x
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f₀) :=
    hf.comp contMDiff_snd
  have hg₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g₀) :=
    hg.comp contMDiff_snd
  obtain ⟨S, hS, hScov⟩ := exists_finite_chart_cover 3 (Sphere 3)
  obtain ⟨C, hC, hCcov⟩ := exists_finite_chart_cover 6 M
  obtain ⟨δ, hδ, hmem, hsmooth⟩ := exists_smooth_parameter_ball e r f₀ hf₀
  obtain ⟨p, hp, hgen⟩ := ManifoldIntersectionFamily.exists_small_spatial_generic_in_charts
    e r f₀ g₀ hf₀ hg₀ S hS.countable C hC.countable (1 / 2) hδ
  have hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞
      (uncurry (ManifoldAffineSphereFamily.map e r f₀ p)) :=
    hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ hp)
  have hF : ContMDiff (𝓡 3) (𝓡 6) ∞
      (ManifoldAffineSphereFamily.map e r f₀ p (1 / 2)) :=
    hP.comp (contMDiff_const.prodMk contMDiff_id)
  let F : C(Sphere 3, M) := ⟨ManifoldAffineSphereFamily.map e r f₀ p (1 / 2), hF.continuous⟩
  have hsmall (s : unitInterval) : ‖(s : ℝ) • p‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg s.property.1]
    exact (mul_le_of_le_one_left (norm_nonneg p) s.property.2).trans_lt hp
  have hparam : Continuous (fun q : unitInterval × Sphere 3 ↦
      ((q.1 : ℝ) • p, ((1 / 2 : ℝ), q.2))) :=
    ((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk
      (continuous_const.prodMk continuous_snd)
  have hH : Continuous (fun q : unitInterval × Sphere 3 ↦
      ManifoldAffineSphereFamily.map e r f₀ ((q.1 : ℝ) • p) (1 / 2) q.2) :=
    hsmooth.continuousOn.comp_continuous hparam (fun q ↦ hsmall q.1)
  have H : f.Homotopy F := {
    toFun q := ManifoldAffineSphereFamily.map e r f₀ ((q.1 : ℝ) • p) (1 / 2) q.2
    continuous_toFun := hH
    map_zero_left x := by
      change ManifoldAffineSphereFamily.map e r f₀ ((0 : ℝ) • p) (1 / 2) x = f x
      rw [zero_smul, map_zero_parameter]
    map_one_left x := by
      change ManifoldAffineSphereFamily.map e r f₀ ((1 : ℝ) • p) (1 / 2) x = F x
      rw [one_smul]
      rfl }
  refine ⟨F, hF, ⟨H⟩, ?_⟩
  exact ManifoldIntersectionFamily.native_transverse_of_spatial_generic e r f₀ g₀ hf₀ hg₀
    S C hScov hCcov (1 / 2) (by constructor <;> norm_num) p (hmem p hp (1 / 2)) hP hgen

end NoExoticSixSphere.EuclideanEmbedding
