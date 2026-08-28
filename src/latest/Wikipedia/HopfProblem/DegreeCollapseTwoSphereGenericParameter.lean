import Wikipedia.HopfProblem.DegreeCollapseTwoSphereKernelAvoidance
import Wikipedia.NoExoticSixSphere.FiniteDiffeomorphChartCover

/-!
# One actual parameter removes all two-sphere collision and kernel tests

Intersect the almost-everywhere sets for all charts of genuine finite
source and target covers. A single arbitrarily small affine parameter
then gives injective spatial chart derivatives and no same-time pair
collisions everywhere in their coupled open domains. The original
manifold-valued family is jointly smooth and keeps both endpoint maps.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 2 → M)

def EmbeddingInCharts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (S : Set SourceChart) (C : Set (TargetChart n M)) (p : Parameters e) : Prop :=
  (∀ s ∈ S, ∀ c ∈ C, ∀ x : ℝ × Vector 2,
    (p, x) ∈ chartDomain e r f hf s c → Injective (chartJet e r f s c (p, x))) ∧
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : ℝ × (Vector 2 × Vector 2),
    (p, x) ∈ pairDomain e r f hf s z c → chartDifference e r f s z c (p, x) ≠ 0

theorem ae_embedding_in_charts [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f)) (hdim : 5 < n)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, EmbeddingInCharts e r f hf S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have hJ : ∀ᵐ p ∂μ, ∀ s : S, ∀ c : C, ∀ x : ℝ × Vector 2,
      (p, x) ∈ chartDomain e r f hf s.val c.val →
        Injective (chartJet e r f s.val c.val (p, x)) :=
    ae_all_iff.mpr fun s => ae_all_iff.mpr fun c =>
      ae_injective_chart_jets e r f μ hf hdim s.val c.val
  have hD : ∀ᵐ p ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : ℝ × (Vector 2 × Vector 2),
      (p, x) ∈ pairDomain e r f hf s.val z.val c.val →
        chartDifference e r f s.val z.val c.val (p, x) ≠ 0 :=
    ae_all_iff.mpr fun s => ae_all_iff.mpr fun z => ae_all_iff.mpr fun c =>
      ae_no_chart_double_points e r f μ hf hdim s.val z.val c.val
  exact (hJ.and hD).mono fun p hp =>
    ⟨fun s hs c hc => hp.1 ⟨s, hs⟩ ⟨c, hc⟩,
      fun s hs z hz c hc => hp.2 ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩⟩

theorem exists_small_embedding_in_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f)) (hdim : 5 < n)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧ EmbeddingInCharts e r f hf S C p := by
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have hdense := Measure.dense_of_ae (ae_embedding_in_charts e r f addHaar hf hdim S hS C hC)
  obtain ⟨p, hp, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨p, by simpa only [dist_zero_left] using hsmall, hp⟩

theorem exists_small_manifold_family_with_embedding_charts
    [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f)) (hdim : 5 < n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set SourceChart, ∃ C : Set (TargetChart n M), ∃ p : Parameters e,
      S.Finite ∧ (∀ x : Sphere 2, ∃ s ∈ S, x ∈ s.source) ∧
      C.Finite ∧ (∀ x : M, ∃ c ∈ C, x ∈ c.source) ∧ ‖p‖ < ε ∧
      EmbeddingInCharts e r f hf S C p ∧
      (∀ t s, ambient e f p t s ∈ r.domain) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry (map e r f p)) ∧
      ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ s, map e r f p t s = f t s := by
  obtain ⟨S, hS, hScov⟩ := ManifoldAffineSphereFamily.exists_finite_chart_cover 2 (Sphere 2)
  obtain ⟨C, hC, hCcov⟩ := ManifoldAffineSphereFamily.exists_finite_chart_cover n M
  obtain ⟨δ, hδ, hmem, hsmooth⟩ := exists_smooth_parameter_ball e r f hf
  obtain ⟨p, hp, hgen⟩ := exists_small_embedding_in_charts e r f hf hdim
    S hS.countable C hC.countable (lt_min hε hδ)
  have hpε : ‖p‖ < ε := hp.trans_le (min_le_left _ _)
  have hpδ : ‖p‖ < δ := hp.trans_le (min_le_right _ _)
  refine ⟨S, C, p, hS, hScov, hC, hCcov, hpε, hgen, hmem p hpδ, ?_, ?_⟩
  · exact hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ => hpδ)
  · exact fun _ ht s => map_eq_outside e r f p ht s

end Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation
