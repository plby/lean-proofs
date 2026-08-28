import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereChartDomain
import Wikipedia.NoExoticSixSphere.ManifoldIntersectionPerturbation

/-!
# Actual intersection domains for a relative moving sphere and a fixed sphere

Only the moving sphere needs a nonzero spatial cutoff. The second sphere is
unchanged, and its source point is independent, with no diagonal exclusion.
All chart and tubular conditions are retained in the coupled open domain.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RelativeSphereIntersectionFamily

open GLOrthonormalization EuclideanEmbedding
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart pairLeft contDiff_pairLeft)
open ManifoldIntersectionFamily (fixedRight contDiff_fixedRight)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f g : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)

def domain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M) :
    Opens (Parameters e × (ℝ × (Vector 3 × Vector 3))) :=
  ⟨pairLeft e ⁻¹' (SpatiallyRelativeSphereFamily.activeChartDomain e r f χ hf hχ s c : Set _) ∩
      fixedRight e ⁻¹' (ManifoldAffineSphereFamily.chartDomain e r g hg z c : Set _),
    ((SpatiallyRelativeSphereFamily.activeChartDomain e r f χ hf hχ s c).isOpen.preimage
      (contDiff_pairLeft e).continuous).inter
      ((ManifoldAffineSphereFamily.chartDomain e r g hg z c).isOpen.preimage
        (contDiff_fixedRight e).continuous)⟩

def difference (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3))) : Vector n :=
  SpatiallyRelativeSphereFamily.chartCoordinates e r f χ s c (pairLeft e q) -
    ManifoldAffineSphereFamily.chartCoordinates e r g z c (fixedRight e q)

theorem difference_apply (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3))) :
    difference e r f g χ s z c q =
      c (SpatiallyRelativeSphereFamily.map e r f χ q.1 q.2.1 (s.symm q.2.2.1)) -
        c (g q.2.1 (z.symm q.2.2.2)) := by
  change c (SpatiallyRelativeSphereFamily.map e r f χ q.1 q.2.1 (s.symm q.2.2.1)) -
    c (ManifoldAffineSphereFamily.map e r g 0 q.2.1 (z.symm q.2.2.2)) = _
  rw [ManifoldAffineSphereFamily.map_zero_parameter]

theorem contDiffOn_difference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (difference e r f g χ s z c) (domain e r f g χ hf hg hχ s z c) :=
  ((SpatiallyRelativeSphereFamily.contDiffOn_chartCoordinates e r f χ hf hχ s c).comp
    (contDiff_pairLeft e).contDiffOn (fun _ hq ↦ hq.1.1)).sub
      ((ManifoldAffineSphereFamily.contDiffOn_chartCoordinates e r g hg z c).comp
        (contDiff_fixedRight e).contDiffOn (fun _ hq ↦ hq.2))

theorem difference_zero_iff
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3)))
    (hq : q ∈ domain e r f g χ hf hg hχ s z c) :
    difference e r f g χ s z c q = 0 ↔
      SpatiallyRelativeSphereFamily.map e r f χ q.1 q.2.1 (s.symm q.2.2.1) =
        g q.2.1 (z.symm q.2.2.2) := by
  rw [difference_apply, sub_eq_zero]
  have hright : g q.2.1 (z.symm q.2.2.2) ∈ c.source := by
    have h := hq.2.2
    change ManifoldAffineSphereFamily.map e r g 0 q.2.1 (z.symm q.2.2.2) ∈ c.source at h
    rwa [ManifoldAffineSphereFamily.map_zero_parameter] at h
  exact ⟨fun h ↦ c.injOn hq.1.1.2 hright h, congrArg c⟩

theorem mem_domain_of_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M) (p : Parameters e)
    (t : ℝ) (x y : Sphere 3) (ht : t ∈ Ioo 0 1) (hχx : χ x ≠ 0)
    (hx : x ∈ s.source) (hy : y ∈ z.source)
    (hp : SpatiallyRelativeSphereFamily.ambient e f χ p t x ∈ r.domain)
    (hleft : SpatiallyRelativeSphereFamily.map e r f χ p t x ∈ c.source)
    (hright : g t y ∈ c.source) :
    (p, t, s x, z y) ∈ domain e r f g χ hf hg hχ s z c := by
  have hs : s.symm (s x) = x := s.left_inv hx
  have hz : z.symm (z y) = y := z.left_inv hy
  constructor
  · change (((s x ∈ s.target ∧ t ∈ Ioo 0 1) ∧
      SpatiallyRelativeSphereFamily.ambient e f χ p t (s.symm (s x)) ∈ r.domain) ∧
      SpatiallyRelativeSphereFamily.map e r f χ p t (s.symm (s x)) ∈ c.source) ∧
      χ (s.symm (s x)) ≠ 0
    rw [hs]
    exact ⟨⟨⟨⟨s.map_source hx, ht⟩, hp⟩, hleft⟩, hχx⟩
  · change ((z y ∈ z.target ∧ t ∈ Ioo 0 1) ∧
      ManifoldAffineSphereFamily.ambient e g 0 t (z.symm (z y)) ∈ r.domain) ∧
      ManifoldAffineSphereFamily.map e r g 0 t (z.symm (z y)) ∈ c.source
    rw [hz, ManifoldAffineSphereFamily.map_zero_parameter]
    have hzero : ManifoldAffineSphereFamily.ambient e g 0 t y = e.toFun (g t y) := by
      simp only [ManifoldAffineSphereFamily.ambient, AffinePerturbation.value,
        Prod.fst_zero, Prod.snd_zero, zero_apply, add_zero, smul_zero]
    rw [hzero]
    exact ⟨⟨⟨z.map_source hy, ht⟩, r.contains (mem_range_self _)⟩, hright⟩

end NoExoticSixSphere.RelativeSphereIntersectionFamily
