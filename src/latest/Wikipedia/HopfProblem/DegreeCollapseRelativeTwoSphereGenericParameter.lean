import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereKernelAvoidance
import Wikipedia.NoExoticSixSphere.FiniteDiffeomorphChartCover

/-!
# One small parameter removes all active two-sphere collisions and kernels

Intersect the actual almost-everywhere conditions over finite native chart
covers. The selected parameter is arbitrarily small and fixes the entire
cutoff zero set exactly. Geometry inside that protected set is retained
as input to the subsequent global embedding argument.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

def EmbeddingInCharts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (S : Set SourceChart) (C : Set (TargetChart n M)) (p : Parameters e) : Prop :=
  (∀ s ∈ S, ∀ c ∈ C, ∀ x : ℝ × Vector 2,
    (p, x) ∈ activeChartDomain e r f χ hf hχ s c → Injective (chartJet e r f χ s c (p, x))) ∧
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : ℝ × (Vector 2 × Vector 2),
    (p, x) ∈ activePairDomain e r f χ hf hχ s z c → chartDifference e r f χ s z c (p, x) ≠ 0

theorem ae_embedding_in_charts [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) (hdim : 5 < n)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, EmbeddingInCharts e r f χ hf hχ S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have hJ : ∀ᵐ p ∂μ, ∀ s : S, ∀ c : C, ∀ x : ℝ × Vector 2,
      (p, x) ∈ activeChartDomain e r f χ hf hχ s.val c.val →
        Injective (chartJet e r f χ s.val c.val (p, x)) :=
    ae_all_iff.mpr fun s => ae_all_iff.mpr fun c =>
      ae_injective_chart_jets e r f χ μ hf hχ hdim s.val c.val
  have hD : ∀ᵐ p ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : ℝ × (Vector 2 × Vector 2),
      (p, x) ∈ activePairDomain e r f χ hf hχ s.val z.val c.val →
        chartDifference e r f χ s.val z.val c.val (p, x) ≠ 0 :=
    ae_all_iff.mpr fun s => ae_all_iff.mpr fun z => ae_all_iff.mpr fun c =>
      ae_no_chart_double_points e r f χ μ hf hχ hdim s.val z.val c.val
  exact (hJ.and hD).mono fun p hp =>
    ⟨fun s hs c hc => hp.1 ⟨s, hs⟩ ⟨c, hc⟩,
      fun s hs z hz c hc => hp.2 ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩⟩

theorem exists_small_embedding_in_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) (hdim : 5 < n)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧ EmbeddingInCharts e r f χ hf hχ S C p := by
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have hdense := Measure.dense_of_ae
    (ae_embedding_in_charts e r f χ addHaar hf hχ hdim S hS C hC)
  obtain ⟨p, hp, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨p, by simpa only [dist_zero_left] using hsmall, hp⟩

theorem exists_small_manifold_family_with_embedding_charts
    [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) (hbound : ∀ x, ‖χ x‖ ≤ 1)
    (hdim : 5 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set SourceChart, ∃ C : Set (TargetChart n M), ∃ p : Parameters e,
      S.Finite ∧ (∀ x : Sphere 2, ∃ s ∈ S, x ∈ s.source) ∧
      C.Finite ∧ (∀ x : M, ∃ c ∈ C, x ∈ c.source) ∧ ‖p‖ < ε ∧
      EmbeddingInCharts e r f χ hf hχ S C p ∧
      (∀ t x, ambient e f χ p t x ∈ r.domain) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry (map e r f χ p)) ∧
      (∀ t x, χ x = 0 → map e r f χ p t x = f t x) ∧
      ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, map e r f χ p t x = f t x := by
  obtain ⟨S, hS, hScov⟩ := ManifoldAffineSphereFamily.exists_finite_chart_cover 2 (Sphere 2)
  obtain ⟨C, hC, hCcov⟩ := ManifoldAffineSphereFamily.exists_finite_chart_cover n M
  obtain ⟨δ, hδ, hmem, hsmooth⟩ := exists_smooth_parameter_ball e r f χ hf hχ hbound
  obtain ⟨p, hp, hgen⟩ := exists_small_embedding_in_charts e r f χ hf hχ hdim
    S hS.countable C hC.countable (lt_min hε hδ)
  have hpε : ‖p‖ < ε := hp.trans_le (min_le_left _ _)
  have hpδ : ‖p‖ < δ := hp.trans_le (min_le_right _ _)
  refine ⟨S, C, p, hS, hScov, hC, hCcov, hpε, hgen, hmem p hpδ, ?_, ?_, ?_⟩
  · exact hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ => hpδ)
  · exact fun t x hx => map_eq_zero_cutoff e r f χ p t x hx
  · exact fun _ ht x => map_eq_outside e r f χ p ht x

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
