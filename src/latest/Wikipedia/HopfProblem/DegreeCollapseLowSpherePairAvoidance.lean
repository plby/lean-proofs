import Wikipedia.HopfProblem.DegreeCollapseParametricAvoidance
import Wikipedia.HopfProblem.DegreeCollapseLowSphereAffinePairParameter

/-!

# Generic low-dimensional sphere perturbations have no double points

At an interior time the actual chart difference is submersive in the affine
parameter. The spatial source has dimension twice the sphere dimension, so
parametric avoidance excludes all off-diagonal coincidences whenever the
original target dimension is larger. The maps and atlases are unchanged.
-/

noncomputable section

open Function Set TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSphereParameters

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding LowSphereAffine

variable {d n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere d → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f)) (t : ℝ)

def pairSliceDomain (s z : (SourceChart d)) (c : TargetChart n M) :
    Opens (Parameters e d × (Vector d × Vector d)) :=
  ⟨(fun q ↦ (q.1, (t, q.2))) ⁻¹' (pairDomain e r f hf s z c : Set _),
    (pairDomain e r f hf s z c).isOpen.preimage
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))⟩

def pairSliceDifference (s z : (SourceChart d)) (c : TargetChart n M)
    (q : Parameters e d × (Vector d × Vector d)) : Vector n :=
  chartDifference e r f s z c (q.1, (t, q.2))

theorem contDiffOn_pairSliceDifference (s z : (SourceChart d)) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (pairSliceDifference e r f t s z c) (pairSliceDomain e r f hf t s z c) :=
  (contDiffOn_chartDifference e r f hf s z c).comp
    (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn (fun _ hq ↦ hq)

theorem surjective_pairSliceDifference_parameter (s z : (SourceChart d)) (c : TargetChart n M)
    (q : Parameters e d × (Vector d × Vector d)) (hq : q ∈ pairSliceDomain e r f hf t s z c) :
    Surjective (fderiv ℝ (fun p : Parameters e d ↦ pairSliceDifference e r f t s z c (p, q.2))
      q.1) :=
  surjective_fderiv_chartDifference_parameter e r f hf s z c (q.1, (t, q.2)) hq

theorem ae_pairSliceDifference_ne_zero [MeasurableSpace (Parameters e d)]
    [BorelSpace (Parameters e d)] (μ : Measure (Parameters e d)) [IsAddHaarMeasure μ]
    (hn : 2 * d < n) (s z : (SourceChart d)) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : Vector d × Vector d, (p, x) ∈ pairSliceDomain e r f hf t s z c →
      pairSliceDifference e r f t s z c (p, x) ≠ 0 :=
  ParametricAvoidance.ae_avoid_zero_of_parameter μ (pairSliceDifference e r f t s z c)
    (pairSliceDomain e r f hf t s z c) (contDiffOn_pairSliceDifference e r f hf t s z c)
    (surjective_pairSliceDifference_parameter e r f hf t s z c)
    (by simpa [GLOrthonormalization.Vector, two_mul] using hn)

def AvoidPairsInCharts (S : Set (SourceChart d)) (C : Set (TargetChart n M))
    (p : Parameters e d) : Prop :=
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : Vector d × Vector d,
    (p, x) ∈ pairSliceDomain e r f hf t s z c → pairSliceDifference e r f t s z c (p, x) ≠ 0

theorem ae_avoidPairsInCharts [MeasurableSpace (Parameters e d)] [BorelSpace (Parameters e d)]
    (μ : Measure (Parameters e d)) [IsAddHaarMeasure μ] (hn : 2 * d < n)
    (S : Set (SourceChart d)) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, AvoidPairsInCharts e r f hf t S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ p ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : Vector d × Vector d,
      (p, x) ∈ pairSliceDomain e r f hf t s.val z.val c.val →
        pairSliceDifference e r f t s.val z.val c.val (p, x) ≠ 0 :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun z ↦ ae_all_iff.mpr fun c ↦
      ae_pairSliceDifference_ne_zero e r f hf t μ hn s.val z.val c.val
  exact h.mono fun p hp s hs z hz c hc ↦ hp ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩

theorem injective_slice_of_avoidPairs (p : Parameters e d) (ht : t ∈ Ioo (0 : ℝ) 1)
    (S : Set (SourceChart d)) (C : Set (TargetChart n M))
    (hS : ∀ x : Sphere d, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hmem : ∀ x, ambient e f p t x ∈ r.domain)
    (havoid : AvoidPairsInCharts e r f hf t S C p) :
    Injective (LowSphereAffine.map e r f p t) := by
  intro x y hxy
  by_contra hne
  obtain ⟨s, hs, hxs⟩ := hS x
  obtain ⟨z, hz, hyz⟩ := hS y
  obtain ⟨c, hc, hxc⟩ := hC (LowSphereAffine.map e r f p t x)
  have hyc : LowSphereAffine.map e r f p t y ∈ c.source := hxy ▸ hxc
  have hx' : s.symm (s x) = x := s.left_inv hxs
  have hy' : z.symm (z y) = y := z.left_inv hyz
  have hq : (p, (s x, z y)) ∈ pairSliceDomain e r f hf t s z c := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ((s x ∈ s.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
        ambient e f p t (s.symm (s x)) ∈ r.domain) ∧
          LowSphereAffine.map e r f p t (s.symm (s x)) ∈ c.source
      rw [hx']
      exact ⟨⟨⟨s.map_source hxs, ht⟩, hmem x⟩, hxc⟩
    · change ((z y ∈ z.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
        ambient e f p t (z.symm (z y)) ∈ r.domain) ∧
          LowSphereAffine.map e r f p t (z.symm (z y)) ∈ c.source
      rw [hy']
      exact ⟨⟨⟨z.map_source hyz, ht⟩, hmem y⟩, hyc⟩
    · change s.symm (s x) ≠ z.symm (z y)
      rwa [hx', hy']
  apply havoid s hs z hz c hc (s x, z y) hq
  apply (chartDifference_zero_iff e r f hf s z c (p, (t, (s x, z y))) hq).mpr
  rwa [hx', hy']

end Wikipedia.HopfProblem.DegreeCollapse.LowSphereParameters
