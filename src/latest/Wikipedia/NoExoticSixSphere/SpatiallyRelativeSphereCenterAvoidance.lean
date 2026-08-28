import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereChartDomain
import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereParameterSubmersion
import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Generic avoidance of the chosen center away from the protected set

The active source-time domain has dimension four, less than the six-dimensional
target. Parametric regularity of the actual coordinate equation therefore
excludes its zeros. This gives avoidance at every interior time, not merely
at a selected time, wherever the spatial cutoff is nonzero.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SpatiallyRelativeSphereFamily

open GLOrthonormalization RelativeDoublePointPerturbation EuclideanEmbedding
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)

def centerDifference (s : SourceChart) (c : TargetChart n M) (b : M)
    (q : Parameters e × (ℝ × Vector 3)) : Vector n :=
  chartCoordinates e r f χ s c q - c b

theorem contDiffOn_centerDifference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) (b : M) :
    ContDiffOn ℝ ∞ (centerDifference e r f χ s c b)
      (activeChartDomain e r f χ hf hχ s c) :=
  ((contDiffOn_chartCoordinates e r f χ hf hχ s c).mono inter_subset_left).sub
    contDiffOn_const

theorem surjective_fderiv_centerDifference_parameter
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) (b : M)
    (q : Parameters e × (ℝ × Vector 3)) (hq : q ∈ activeChartDomain e r f χ hf hχ s c) :
    Surjective (fderiv ℝ
      (fun p : Parameters e ↦ centerDifference e r f χ s c b (p, q.2)) q.1) := by
  have hd := hasFDerivAt_chart_parameter e r f χ c q.1 q.2.1 (s.symm q.2.2)
    hq.1.1.2 hq.1.2
  have he := (hd.sub_const (c b)).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ centerDifference e r f χ s c b (p, q.2)) q.1 = _
    at he
  rw [he]
  have hsurj := surjective_fderiv_chart_parameter e r f χ c q.1 q.2.1 (s.symm q.2.2)
    hq.1.1.1.2 hq.2 hq.1.1.2 hq.1.2
  rwa [hd.fderiv] at hsurj

theorem surjective_fderiv_centerDifference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) (b : M)
    (q : Parameters e × (ℝ × Vector 3)) (hq : q ∈ activeChartDomain e r f χ hf hχ s c) :
    Surjective (fderiv ℝ (centerDifference e r f χ s c b) q) := by
  have hp := surjective_fderiv_centerDifference_parameter e r f χ hf hχ s c b q hq
  have hD := ((contDiffOn_centerDifference e r f χ hf hχ s c b).contDiffAt
    ((activeChartDomain e r f χ hf hχ s c).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) (ℝ × Vector 3)) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hD.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ centerDifference e r f χ s c b (p, q.2)) q.1 = _
    at he
  rw [he] at hp
  intro w
  obtain ⟨v, hv⟩ := hp w
  exact ⟨(v, 0), hv⟩

theorem ae_avoids_center_in_chart
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (hn : n = 6)
    (s : SourceChart) (c : TargetChart n M) (b : M) :
    ∀ᵐ p ∂μ, ∀ x : ℝ × Vector 3, (p, x) ∈ activeChartDomain e r f χ hf hχ s c →
      chartCoordinates e r f χ s c (p, x) ≠ c b := by
  have h := ParametricRegular.ae_parameters_on μ (centerDifference e r f χ s c b)
    (activeChartDomain e r f χ hf hχ s c) (contDiffOn_centerDifference e r f χ hf hχ s c b)
    (fun q hq _ ↦ surjective_fderiv_centerDifference e r f χ hf hχ s c b q hq)
  apply h.mono
  intro p hp x hx he
  have hzero : centerDifference e r f χ s c b (p, x) = 0 := sub_eq_zero.mpr he
  have hsurj := hp x hx hzero
  let L : (ℝ × Vector 3) →L[ℝ] Vector n :=
    fderiv ℝ (fun y : ℝ × Vector 3 ↦ centerDifference e r f χ s c b (p, y)) x
  have hle := LinearMap.finrank_le_finrank_of_surjective (f := L.toLinearMap) hsurj
  norm_num [Module.finrank_prod, GLOrthonormalization.Vector, hn] at hle

end NoExoticSixSphere.SpatiallyRelativeSphereFamily
