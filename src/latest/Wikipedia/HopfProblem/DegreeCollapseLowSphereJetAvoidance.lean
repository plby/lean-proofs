import Wikipedia.HopfProblem.DegreeCollapseLowSpherePairAvoidance
import Wikipedia.HopfProblem.DegreeCollapseLowSphereAffineJetCoordinates

/-!

# Generic low-dimensional sphere perturbations have injective derivatives

Evaluate the actual spatial jet on a nonzero coordinate vector. The proved
parameter submersion for the jet makes this equation submersive. Its spatial
variables are the chart point and vector, so parametric avoidance excludes
every nonzero kernel when the target dimension exceeds twice the source
sphere dimension. The conclusion uses the original manifold derivatives.
-/

noncomputable section

open Function Set TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSphereParameters

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding LowSphereAffine

theorem evaluation_surjective {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : E) (hv : v ≠ 0) :
    Surjective (ContinuousLinearMap.apply ℝ F v) := by
  intro y
  refine ⟨(innerSL ℝ v).smulRight ((‖v‖ ^ 2)⁻¹ • y), ?_⟩
  change (inner ℝ v v) • ((‖v‖ ^ 2)⁻¹ • y) = y
  rw [real_inner_self_eq_norm_sq, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)), one_smul]

variable {d n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere d → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f)) (t : ℝ)

def directionSliceDomain (s : (SourceChart d)) (c : TargetChart n M) :
    Opens (Parameters e d × (Vector d × Vector d)) :=
  ⟨{q | (q.1, (t, q.2.1)) ∈ chartDomain e r f hf s c ∧ q.2.2 ≠ 0},
    ((chartDomain e r f hf s c).isOpen.preimage
      (continuous_fst.prodMk (continuous_const.prodMk (continuous_fst.comp continuous_snd)))).inter
        (isOpen_ne.preimage (continuous_snd.comp continuous_snd))⟩

def directionSliceMap (s : (SourceChart d)) (c : TargetChart n M)
    (q : Parameters e d × (Vector d × Vector d)) : Vector n :=
  chartJet e r f s c (q.1, (t, q.2.1)) q.2.2

theorem contDiffOn_directionSliceMap (s : (SourceChart d)) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (directionSliceMap e r f t s c) (directionSliceDomain e r f hf t s c) :=
  ((contDiffOn_chartJet e r f hf s c).comp
    (contDiff_fst.prodMk
      (contDiff_const.prodMk (contDiff_fst.comp contDiff_snd))).contDiffOn
        (fun _ hq ↦ hq.1)).clm_apply (contDiff_snd.comp contDiff_snd).contDiffOn

theorem surjective_directionSliceMap_parameter (s : (SourceChart d)) (c : TargetChart n M)
    (q : Parameters e d × (Vector d × Vector d)) (hq : q ∈ directionSliceDomain e r f hf t s c) :
    Surjective (fderiv ℝ (fun p : Parameters e d ↦ directionSliceMap e r f t s c (p, q.2))
      q.1) := by
  have hx := hq.1
  have hJ := surjective_fderiv_chart_spatial_parameter e r f hf s c q.1 t q.2.1
    hx.1.1.2 hx.1.1.1 hx.1.2 hx.2
  change Surjective (fderiv ℝ (fun p : Parameters e d ↦ chartJet e r f s c (p, (t, q.2.1)))
    q.1) at hJ
  have hfull : ContDiffAt ℝ ∞ (chartJet e r f s c) (q.1, (t, q.2.1)) :=
    (contDiffOn_chartJet e r f hf s c).contDiffAt
      ((chartDomain e r f hf s c).isOpen.mem_nhds hx)
  have hlift : HasFDerivAt (fun p : Parameters e d ↦ (p, (t, q.2.1)))
      (ContinuousLinearMap.inl ℝ (Parameters e d) (ℝ × Vector d)) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const (t, q.2.1) q.1)
  have hcomp := ((hfull.differentiableAt (by simp)).hasFDerivAt.comp q.1 hlift)
  have hJd : DifferentiableAt ℝ
      (fun p : Parameters e d ↦ chartJet e r f s c (p, (t, q.2.1))) q.1 :=
    hcomp.differentiableAt
  let ev := ContinuousLinearMap.apply ℝ (Vector n) q.2.2
  have he := (ev.hasFDerivAt.comp q.1 hJd.hasFDerivAt).fderiv
  change fderiv ℝ (fun p : Parameters e d ↦ directionSliceMap e r f t s c (p, q.2)) q.1 = _ at he
  rw [he]
  exact (evaluation_surjective q.2.2 hq.2).comp hJ

theorem ae_directionSliceMap_ne_zero [MeasurableSpace (Parameters e d)]
    [BorelSpace (Parameters e d)] (μ : Measure (Parameters e d)) [IsAddHaarMeasure μ]
    (hn : 2 * d < n) (s : (SourceChart d)) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : Vector d × Vector d, (p, x) ∈ directionSliceDomain e r f hf t s c →
      directionSliceMap e r f t s c (p, x) ≠ 0 :=
  ParametricAvoidance.ae_avoid_zero_of_parameter μ (directionSliceMap e r f t s c)
    (directionSliceDomain e r f hf t s c) (contDiffOn_directionSliceMap e r f hf t s c)
    (surjective_directionSliceMap_parameter e r f hf t s c)
    (by simpa [GLOrthonormalization.Vector, two_mul] using hn)

def AvoidDirectionsInCharts (S : Set (SourceChart d)) (C : Set (TargetChart n M))
    (p : Parameters e d) : Prop :=
  ∀ s ∈ S, ∀ c ∈ C, ∀ x : Vector d × Vector d,
    (p, x) ∈ directionSliceDomain e r f hf t s c → directionSliceMap e r f t s c (p, x) ≠ 0

theorem ae_avoidDirectionsInCharts [MeasurableSpace (Parameters e d)] [BorelSpace (Parameters e d)]
    (μ : Measure (Parameters e d)) [IsAddHaarMeasure μ] (hn : 2 * d < n)
    (S : Set (SourceChart d)) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, AvoidDirectionsInCharts e r f hf t S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ p ∂μ, ∀ s : S, ∀ c : C, ∀ x : Vector d × Vector d,
      (p, x) ∈ directionSliceDomain e r f hf t s.val c.val →
        directionSliceMap e r f t s.val c.val (p, x) ≠ 0 :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun c ↦
      ae_directionSliceMap_ne_zero e r f hf t μ hn s.val c.val
  exact h.mono fun p hp s hs c hc ↦ hp ⟨s, hs⟩ ⟨c, hc⟩

theorem injective_mfderiv_slice_of_avoidDirections (p : Parameters e d)
    (hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞
      (uncurry (LowSphereAffine.map e r f p)))
    (ht : t ∈ Ioo (0 : ℝ) 1) (S : Set (SourceChart d)) (C : Set (TargetChart n M))
    (hS : ∀ x : Sphere d, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hmem : ∀ x, ambient e f p t x ∈ r.domain)
    (havoid : AvoidDirectionsInCharts e r f hf t S C p) (x : Sphere d) :
    Injective (mfderiv (𝓡 d) (𝓡 n) (LowSphereAffine.map e r f p t) x) := by
  obtain ⟨s, hs, hxs⟩ := hS x
  obtain ⟨c, hc, hxc⟩ := hC (LowSphereAffine.map e r f p t x)
  have hx' : s.symm (s x) = x := s.left_inv hxs
  have hq : (p, (t, s x)) ∈ chartDomain e r f hf s c := by
    change ((s x ∈ s.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f p t (s.symm (s x)) ∈ r.domain) ∧
        LowSphereAffine.map e r f p t (s.symm (s x)) ∈ c.source
    rw [hx']
    exact ⟨⟨⟨s.map_source hxs, ht⟩, hmem x⟩, hxc⟩
  have hJ : Injective (chartJet e r f s c (p, (t, s x))) := by
    intro v w hvw
    by_contra hne
    have hz : chartJet e r f s c (p, (t, s x)) (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    exact havoid s hs c hc (s x, v - w) ⟨hq, sub_ne_zero.mpr hne⟩ hz
  have hi := (injective_chartJet_iff e r f hf p hP s c (t, s x) hq).mp hJ
  rwa [hx'] at hi

end Wikipedia.HopfProblem.DegreeCollapse.LowSphereParameters
