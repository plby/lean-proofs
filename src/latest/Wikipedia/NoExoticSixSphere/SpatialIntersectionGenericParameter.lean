import Wikipedia.NoExoticSixSphere.ManifoldIntersectionGenericParameter

/-!
# Generic spatial intersections at a fixed time

Fixing time leaves the affine parameter derivative surjective. Parametric
Sard is applied to the actual six-dimensional pair source, so it gives
spatial transversality, not merely regularity in space-time. One arbitrarily
small parameter works simultaneously in every chart of finite covers.
-/

noncomputable section

open Set Function TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldIntersectionFamily

open GLOrthonormalization EuclideanEmbedding ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))

def timeSlice (t : ℝ) (q : Parameters e × (Vector 3 × Vector 3)) :
    Parameters e × (ℝ × (Vector 3 × Vector 3)) := (q.1, t, q.2)

theorem contDiff_timeSlice (t : ℝ) : ContDiff ℝ ∞ (timeSlice e t) :=
  contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)

def spatialDomain (s z : SourceChart) (c : TargetChart n M) (t : ℝ) :
    Opens (Parameters e × (Vector 3 × Vector 3)) :=
  ⟨timeSlice e t ⁻¹' (domain e r f g hf hg s z c : Set _),
    (domain e r f g hf hg s z c).isOpen.preimage (contDiff_timeSlice e t).continuous⟩

def spatialDifference (s z : SourceChart) (c : TargetChart n M) (t : ℝ)
    (q : Parameters e × (Vector 3 × Vector 3)) : Vector n :=
  difference e r f g s z c (timeSlice e t q)

include hf hg in
theorem contDiffOn_spatialDifference (s z : SourceChart) (c : TargetChart n M) (t : ℝ) :
    ContDiffOn ℝ ∞ (spatialDifference e r f g s z c t) (spatialDomain e r f g hf hg s z c t) :=
  (contDiffOn_difference e r f g hf hg s z c).comp (contDiff_timeSlice e t).contDiffOn
    (fun _ hq ↦ hq)

theorem surjective_fderiv_spatialDifference (s z : SourceChart) (c : TargetChart n M)
    (t : ℝ) (q : Parameters e × (Vector 3 × Vector 3))
    (hq : q ∈ spatialDomain e r f g hf hg s z c t) :
    Surjective (fderiv ℝ (spatialDifference e r f g s z c t) q) := by
  have hp := surjective_fderiv_difference_parameter e r f g hf hg s z c (timeSlice e t q) hq
  change Surjective (fderiv ℝ
    (fun p : Parameters e ↦ spatialDifference e r f g s z c t (p, q.2)) q.1) at hp
  have hD := ((contDiffOn_spatialDifference e r f g hf hg s z c t).contDiffAt
    ((spatialDomain e r f g hf hg s z c t).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) (Vector 3 × Vector 3)) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hD.hasFDerivAt.comp q.1 hi).fderiv
  change fderiv ℝ (fun p : Parameters e ↦
    spatialDifference e r f g s z c t (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro w
  obtain ⟨v, hv⟩ := hp w
  exact ⟨(v, 0), hv⟩

theorem ae_regular_spatial_intersections [MeasurableSpace (Parameters e)]
    [BorelSpace (Parameters e)] (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (s z : SourceChart) (c : TargetChart n M) (t : ℝ) :
    ∀ᵐ p ∂μ, ∀ x : Vector 3 × Vector 3,
      (p, x) ∈ spatialDomain e r f g hf hg s z c t →
      spatialDifference e r f g s z c t (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ spatialDifference e r f g s z c t (p, y)) x) :=
  ParametricRegular.ae_parameters_on μ (spatialDifference e r f g s z c t)
    (spatialDomain e r f g hf hg s z c t) (contDiffOn_spatialDifference e r f g hf hg s z c t)
    (fun q hq _ ↦ surjective_fderiv_spatialDifference e r f g hf hg s z c t q hq)

def SpatialGenericInCharts (S : Set SourceChart) (C : Set (TargetChart n M))
    (t : ℝ) (p : Parameters e) : Prop :=
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : Vector 3 × Vector 3,
    (p, x) ∈ spatialDomain e r f g hf hg s z c t →
    spatialDifference e r f g s z c t (p, x) = 0 →
    Surjective (fderiv ℝ (fun y ↦ spatialDifference e r f g s z c t (p, y)) x)

theorem ae_spatial_generic_in_charts [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable)
    (t : ℝ) : ∀ᵐ p ∂μ, SpatialGenericInCharts e r f g hf hg S C t p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ p ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : Vector 3 × Vector 3,
      (p, x) ∈ spatialDomain e r f g hf hg s.val z.val c.val t →
      spatialDifference e r f g s.val z.val c.val t (p, x) = 0 →
      Surjective (fderiv ℝ
        (fun y ↦ spatialDifference e r f g s.val z.val c.val t (p, y)) x) :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun z ↦ ae_all_iff.mpr fun c ↦
      ae_regular_spatial_intersections e r f g hf hg μ s.val z.val c.val t
  exact h.mono fun p hp s hs z hz c hc ↦ hp ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩

theorem exists_small_spatial_generic_in_charts (S : Set SourceChart) (hS : S.Countable)
    (C : Set (TargetChart n M)) (hC : C.Countable) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧ SpatialGenericInCharts e r f g hf hg S C t p := by
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have hdense := Measure.dense_of_ae
    (ae_spatial_generic_in_charts e r f g hf hg addHaar S hS C hC t)
  obtain ⟨p, hp, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨p, by simpa only [dist_zero_left] using hsmall, hp⟩

end NoExoticSixSphere.ManifoldIntersectionFamily
