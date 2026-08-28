import Wikipedia.HopfProblem.DegreeCollapseParametricAvoidance
import Wikipedia.NoExoticSixSphere.ManifoldAffineGenericDoublePoints

/-!
# Generic affine sphere perturbations have no double points above dimension six

Fix an interior time of the original endpoint-relative perturbation.
The original chart difference is submersive in the affine parameter.
Its spatial source has dimension six, so parametric avoidance makes
every off-diagonal chart difference nonzero for almost every parameter.
The final comparison retains the original manifold maps and chart domains.
-/

noncomputable section

open Function Set TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSphereParameters

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f)) (t : ℝ)

def pairSliceDomain (s z : SourceChart) (c : TargetChart n M) :
    Opens (Parameters e × (Vector 3 × Vector 3)) :=
  ⟨(fun q ↦ (q.1, (t, q.2))) ⁻¹' (pairDomain e r f hf s z c : Set _),
    (pairDomain e r f hf s z c).isOpen.preimage
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))⟩

def pairSliceDifference (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (Vector 3 × Vector 3)) : Vector n :=
  chartDifference e r f s z c (q.1, (t, q.2))

theorem contDiffOn_pairSliceDifference (s z : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (pairSliceDifference e r f t s z c) (pairSliceDomain e r f hf t s z c) :=
  (contDiffOn_chartDifference e r f hf s z c).comp
    (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn (fun _ hq ↦ hq)

theorem surjective_pairSliceDifference_parameter (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (Vector 3 × Vector 3)) (hq : q ∈ pairSliceDomain e r f hf t s z c) :
    Surjective (fderiv ℝ (fun p : Parameters e ↦ pairSliceDifference e r f t s z c (p, q.2))
      q.1) :=
  surjective_fderiv_chartDifference_parameter e r f hf s z c (q.1, (t, q.2)) hq

theorem ae_pairSliceDifference_ne_zero [MeasurableSpace (Parameters e)]
    [BorelSpace (Parameters e)] (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hn : 6 < n) (s z : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : Vector 3 × Vector 3, (p, x) ∈ pairSliceDomain e r f hf t s z c →
      pairSliceDifference e r f t s z c (p, x) ≠ 0 :=
  ParametricAvoidance.ae_avoid_zero_of_parameter μ (pairSliceDifference e r f t s z c)
    (pairSliceDomain e r f hf t s z c) (contDiffOn_pairSliceDifference e r f hf t s z c)
    (surjective_pairSliceDifference_parameter e r f hf t s z c)
    (by simpa [GLOrthonormalization.Vector] using hn)

def AvoidPairsInCharts (S : Set SourceChart) (C : Set (TargetChart n M))
    (p : Parameters e) : Prop :=
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : Vector 3 × Vector 3,
    (p, x) ∈ pairSliceDomain e r f hf t s z c → pairSliceDifference e r f t s z c (p, x) ≠ 0

theorem ae_avoidPairsInCharts [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ] (hn : 6 < n)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, AvoidPairsInCharts e r f hf t S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ p ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : Vector 3 × Vector 3,
      (p, x) ∈ pairSliceDomain e r f hf t s.val z.val c.val →
        pairSliceDifference e r f t s.val z.val c.val (p, x) ≠ 0 :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun z ↦ ae_all_iff.mpr fun c ↦
      ae_pairSliceDifference_ne_zero e r f hf t μ hn s.val z.val c.val
  exact h.mono fun p hp s hs z hz c hc ↦ hp ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩

theorem injective_slice_of_avoidPairs (p : Parameters e) (ht : t ∈ Ioo (0 : ℝ) 1)
    (S : Set SourceChart) (C : Set (TargetChart n M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hmem : ∀ x, ambient e f p t x ∈ r.domain)
    (havoid : AvoidPairsInCharts e r f hf t S C p) :
    Injective (ManifoldAffineSphereFamily.map e r f p t) := by
  intro x y hxy
  by_contra hne
  obtain ⟨s, hs, hxs⟩ := hS x
  obtain ⟨z, hz, hyz⟩ := hS y
  obtain ⟨c, hc, hxc⟩ := hC (ManifoldAffineSphereFamily.map e r f p t x)
  have hyc : ManifoldAffineSphereFamily.map e r f p t y ∈ c.source := hxy ▸ hxc
  have hx' : s.symm (s x) = x := s.left_inv hxs
  have hy' : z.symm (z y) = y := z.left_inv hyz
  have hq : (p, (s x, z y)) ∈ pairSliceDomain e r f hf t s z c := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ((s x ∈ s.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
        ambient e f p t (s.symm (s x)) ∈ r.domain) ∧
          ManifoldAffineSphereFamily.map e r f p t (s.symm (s x)) ∈ c.source
      rw [hx']
      exact ⟨⟨⟨s.map_source hxs, ht⟩, hmem x⟩, hxc⟩
    · change ((z y ∈ z.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
        ambient e f p t (z.symm (z y)) ∈ r.domain) ∧
          ManifoldAffineSphereFamily.map e r f p t (z.symm (z y)) ∈ c.source
      rw [hy']
      exact ⟨⟨⟨z.map_source hyz, ht⟩, hmem y⟩, hyc⟩
    · change s.symm (s x) ≠ z.symm (z y)
      rwa [hx', hy']
  apply havoid s hs z hz c hc (s x, z y) hq
  apply (chartDifference_zero_iff e r f hf s z c (p, (t, (s x, z y))) hq).mpr
  rwa [hx', hy']

end Wikipedia.HopfProblem.DegreeCollapse.SevenSphereParameters
