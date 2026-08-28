import Wikipedia.NoExoticSixSphere.ManifoldAffineGenericJets
import Wikipedia.NoExoticSixSphere.ManifoldAffineGenericDoublePoints
import Wikipedia.NoExoticSixSphere.FiniteDiffeomorphChartCover

/-!
# One small manifold perturbation is generic across actual finite chart covers

The exceptional sets for spatial jets and distinct-pair equations are null
for the same affine parameter. Countable intersection controls all charts.
Compactness constructs finite genuine source and target chart covers and a
uniform tubular parameter ball, yielding an actual smooth endpoint-relative
manifold family with all these properties for one arbitrarily small parameter.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)

def GenericInCharts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (S : Set SourceChart) (C : Set (TargetChart n M)) (p : Parameters e) : Prop :=
  (∀ s ∈ S, ∀ c ∈ C, OperatorRank.RegularThreeSixOn
    (fun x : ℝ × Vector 3 ↦ chartJet e r f s c (p, x))
    {x | (p, x) ∈ chartDomain e r f hf s c}) ∧
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : ℝ × (Vector 3 × Vector 3),
    (p, x) ∈ pairDomain e r f hf s z c → chartDifference e r f s z c (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ chartDifference e r f s z c (p, y)) x)

theorem ae_generic_in_charts [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f)) (hn : n = 6)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, GenericInCharts e r f hf S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have hJ : ∀ᵐ p ∂μ, ∀ s : S, ∀ c : C, OperatorRank.RegularThreeSixOn
      (fun x : ℝ × Vector 3 ↦ chartJet e r f s.val c.val (p, x))
      {x | (p, x) ∈ chartDomain e r f hf s.val c.val} :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun c ↦
      ae_regular_chart_jets e r f μ hf hn s.val c.val
  have hD : ∀ᵐ p ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : ℝ × (Vector 3 × Vector 3),
      (p, x) ∈ pairDomain e r f hf s.val z.val c.val →
        chartDifference e r f s.val z.val c.val (p, x) = 0 →
          Surjective (fderiv ℝ (fun y ↦ chartDifference e r f s.val z.val c.val (p, y)) x) :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun z ↦ ae_all_iff.mpr fun c ↦
      ae_regular_chart_double_points e r f μ hf s.val z.val c.val
  exact (hJ.and hD).mono fun p hp ↦
    ⟨fun s hs c hc ↦ hp.1 ⟨s, hs⟩ ⟨c, hc⟩,
      fun s hs z hz c hc ↦ hp.2 ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩⟩

theorem exists_small_generic_in_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f)) (hn : n = 6)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧ GenericInCharts e r f hf S C p := by
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have hdense := Measure.dense_of_ae (ae_generic_in_charts e r f addHaar hf hn S hS C hC)
  obtain ⟨p, hp, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨p, by simpa only [dist_zero_left] using hsmall, hp⟩

theorem exists_small_generic_manifold_family [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f)) (hn : n = 6)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set SourceChart, ∃ C : Set (TargetChart n M), ∃ p : Parameters e,
      S.Finite ∧ (∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source) ∧
      C.Finite ∧ (∀ x : M, ∃ c ∈ C, x ∈ c.source) ∧ ‖p‖ < ε ∧
      GenericInCharts e r f hf S C p ∧
      (∀ t s, ambient e f p t s ∈ r.domain) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f p)) ∧
      ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ s, map e r f p t s = f t s := by
  obtain ⟨S, hS, hScov⟩ := exists_finite_chart_cover 3 (Sphere 3)
  obtain ⟨C, hC, hCcov⟩ := exists_finite_chart_cover n M
  obtain ⟨δ, hδ, hmem, hsmooth⟩ := exists_smooth_parameter_ball e r f hf
  obtain ⟨p, hp, hgen⟩ := exists_small_generic_in_charts e r f hf hn
    S hS.countable C hC.countable (lt_min hε hδ)
  have hpε : ‖p‖ < ε := hp.trans_le (min_le_left _ _)
  have hpδ : ‖p‖ < δ := hp.trans_le (min_le_right _ _)
  refine ⟨S, C, p, hS, hScov, hC, hCcov, hpε, hgen, hmem p hpδ, ?_, ?_⟩
  · exact hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ hpδ)
  · exact fun _ ht s ↦ map_eq_outside e r f p ht s

end NoExoticSixSphere.ManifoldAffineSphereFamily
