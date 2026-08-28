import Wikipedia.NoExoticSixSphere.ManifoldAffinePairDomain

/-!
# Perturbing one of two manifold-valued sphere families

The first family is perturbed through the actual tubular retraction. The
second family is fixed. Their source points are independent, so no diagonal
exclusion is needed. The coupled open domain records two actual source charts,
the tubular condition for the moving sheet, and a shared target chart.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldIntersectionFamily

open GLOrthonormalization EuclideanEmbedding ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f g : ℝ → Sphere 3 → M)

def fixedRight (q : Parameters e × (ℝ × (Vector 3 × Vector 3))) :
    Parameters e × (ℝ × Vector 3) := (0, q.2.1, q.2.2.2)

theorem contDiff_fixedRight : ContDiff ℝ ∞ (fixedRight e) := by unfold fixedRight; fun_prop

def domain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (s z : SourceChart) (c : TargetChart n M) :
    Opens (Parameters e × (ℝ × (Vector 3 × Vector 3))) :=
  ⟨pairLeft e ⁻¹' (chartDomain e r f hf s c : Set _) ∩
      fixedRight e ⁻¹' (chartDomain e r g hg z c : Set _),
    ((chartDomain e r f hf s c).isOpen.preimage (contDiff_pairLeft e).continuous).inter
      ((chartDomain e r g hg z c).isOpen.preimage (contDiff_fixedRight e).continuous)⟩

def difference (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3))) : Vector n :=
  chartCoordinates e r f s c (pairLeft e q) - chartCoordinates e r g z c (fixedRight e q)

theorem difference_apply (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3))) :
    difference e r f g s z c q =
      c (ManifoldAffineSphereFamily.map e r f q.1 q.2.1 (s.symm q.2.2.1)) -
        c (g q.2.1 (z.symm q.2.2.2)) := by
  change c (ManifoldAffineSphereFamily.map e r f q.1 q.2.1 (s.symm q.2.2.1)) -
    c (ManifoldAffineSphereFamily.map e r g 0 q.2.1 (z.symm q.2.2.2)) = _
  rw [map_zero_parameter]

theorem contDiffOn_difference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (s z : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (difference e r f g s z c) (domain e r f g hf hg s z c) :=
  ((contDiffOn_chartCoordinates e r f hf s c).comp (contDiff_pairLeft e).contDiffOn
    (fun _ hq ↦ hq.1)).sub
      ((contDiffOn_chartCoordinates e r g hg z c).comp (contDiff_fixedRight e).contDiffOn
        (fun _ hq ↦ hq.2))

theorem difference_zero_iff
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3)))
    (hq : q ∈ domain e r f g hf hg s z c) :
    difference e r f g s z c q = 0 ↔
      ManifoldAffineSphereFamily.map e r f q.1 q.2.1 (s.symm q.2.2.1) =
        g q.2.1 (z.symm q.2.2.2) := by
  rw [difference_apply, sub_eq_zero]
  have hright : g q.2.1 (z.symm q.2.2.2) ∈ c.source := by
    have h := hq.2.2
    change ManifoldAffineSphereFamily.map e r g 0 q.2.1 (z.symm q.2.2.2) ∈ c.source at h
    rwa [map_zero_parameter] at h
  exact ⟨fun h ↦ c.injOn hq.1.2 hright h, congrArg c⟩

theorem mem_domain_of_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (s z : SourceChart) (c : TargetChart n M) (p : Parameters e)
    (t : ℝ) (x y : Sphere 3) (ht : t ∈ Ioo 0 1)
    (hx : x ∈ s.source) (hy : y ∈ z.source)
    (hp : ambient e f p t x ∈ r.domain)
    (hleft : ManifoldAffineSphereFamily.map e r f p t x ∈ c.source)
    (hright : g t y ∈ c.source) :
    (p, t, s x, z y) ∈ domain e r f g hf hg s z c := by
  have hs : s.symm (s x) = x := s.left_inv hx
  have hz : z.symm (z y) = y := z.left_inv hy
  change (((s x ∈ s.target ∧ t ∈ Ioo 0 1) ∧
    ambient e f p t (s.symm (s x)) ∈ r.domain) ∧
    ManifoldAffineSphereFamily.map e r f p t (s.symm (s x)) ∈ c.source) ∧
    (((z y ∈ z.target ∧ t ∈ Ioo 0 1) ∧
    ambient e g 0 t (z.symm (z y)) ∈ r.domain) ∧
    ManifoldAffineSphereFamily.map e r g 0 t (z.symm (z y)) ∈ c.source)
  rw [hs, hz, map_zero_parameter]
  have hzero : ambient e g 0 t y = e.toFun (g t y) := by
    simp only [ambient, AffinePerturbation.value, Prod.fst_zero, Prod.snd_zero,
      zero_apply, add_zero, smul_zero]
  rw [hzero]
  constructor
  · exact ⟨⟨⟨s.map_source hx, ht⟩, hp⟩, hleft⟩
  · exact ⟨⟨⟨z.map_source hy, ht⟩, r.contains (mem_range_self _)⟩, hright⟩

end NoExoticSixSphere.ManifoldIntersectionFamily
