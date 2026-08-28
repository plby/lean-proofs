import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereGenericJets
import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereGenericDoublePoints
import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereCenterAvoidance
import Wikipedia.NoExoticSixSphere.FiniteDiffeomorphChartCover

/-!
# One small relative family with simultaneous genericity and center avoidance

Countable intersection gives a single parameter satisfying the jet, double-point,
and center-avoidance conclusions in all chosen charts. Compactness supplies
finite genuine chart covers and uniform tubular control. The actual family
fixes the cutoff zero set exactly and avoids the chosen center elsewhere at
every interior time. Selecting an immersed self-transverse slice is separate.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SpatiallyRelativeSphereFamily

open GLOrthonormalization EuclideanEmbedding
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart exists_finite_chart_cover)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)

def GenericInCharts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (S : Set SourceChart) (C : Set (TargetChart n M)) (p : Parameters e) : Prop :=
  (∀ s ∈ S, ∀ c ∈ C, OperatorRank.RegularThreeSixOn
    (fun x : ℝ × Vector 3 ↦ chartJet e r f χ s c (p, x))
    {x | (p, x) ∈ activeChartDomain e r f χ hf hχ s c}) ∧
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : ℝ × (Vector 3 × Vector 3),
    (p, x) ∈ activePairDomain e r f χ hf hχ s z c →
      chartDifference e r f χ s z c (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ chartDifference e r f χ s z c (p, y)) x)

def AvoidsCenterInCharts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (S : Set SourceChart) (C : Set (TargetChart n M)) (b : M) (p : Parameters e) : Prop :=
  ∀ s ∈ S, ∀ c ∈ C, ∀ x : ℝ × Vector 3,
    (p, x) ∈ activeChartDomain e r f χ hf hχ s c →
      chartCoordinates e r f χ s c (p, x) ≠ c b

theorem ae_generic_in_charts [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (hn : n = 6)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, GenericInCharts e r f χ hf hχ S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have hJ : ∀ᵐ p ∂μ, ∀ s : S, ∀ c : C, OperatorRank.RegularThreeSixOn
      (fun x : ℝ × Vector 3 ↦ chartJet e r f χ s.val c.val (p, x))
      {x | (p, x) ∈ activeChartDomain e r f χ hf hχ s.val c.val} :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun c ↦
      ae_regular_chart_jets e r f χ μ hf hχ hn s.val c.val
  have hD : ∀ᵐ p ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : ℝ × (Vector 3 × Vector 3),
      (p, x) ∈ activePairDomain e r f χ hf hχ s.val z.val c.val →
        chartDifference e r f χ s.val z.val c.val (p, x) = 0 →
          Surjective (fderiv ℝ (fun y ↦ chartDifference e r f χ s.val z.val c.val (p, y)) x) :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun z ↦ ae_all_iff.mpr fun c ↦
      ae_regular_chart_double_points e r f χ μ hf hχ s.val z.val c.val
  exact (hJ.and hD).mono fun p hp ↦
    ⟨fun s hs c hc ↦ hp.1 ⟨s, hs⟩ ⟨c, hc⟩,
      fun s hs z hz c hc ↦ hp.2 ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩⟩

theorem ae_avoids_center_in_charts [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (hn : n = 6)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable)
    (b : M) : ∀ᵐ p ∂μ, AvoidsCenterInCharts e r f χ hf hχ S C b p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ p ∂μ, ∀ s : S, ∀ c : C, ∀ x : ℝ × Vector 3,
      (p, x) ∈ activeChartDomain e r f χ hf hχ s.val c.val →
        chartCoordinates e r f χ s.val c.val (p, x) ≠ c.val b :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun c ↦
      ae_avoids_center_in_chart e r f χ μ hf hχ hn s.val c.val b
  exact h.mono fun p hp s hs c hc ↦ hp ⟨s, hs⟩ ⟨c, hc⟩

theorem exists_small_generic_avoiding_in_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (hn : n = 6)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable)
    (b : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧ GenericInCharts e r f χ hf hχ S C p ∧
      AvoidsCenterInCharts e r f χ hf hχ S C b p := by
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have hdense := Measure.dense_of_ae
    ((ae_generic_in_charts e r f χ addHaar hf hχ hn S hS C hC).and
      (ae_avoids_center_in_charts e r f χ addHaar hf hχ hn S hS C hC b))
  obtain ⟨p, hp, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨p, by simpa only [dist_zero_left] using hsmall, hp⟩

theorem map_ne_center_of_avoids_in_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (S : Set SourceChart) (C : Set (TargetChart n M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (b : M) (p : Parameters e) (ha : AvoidsCenterInCharts e r f χ hf hχ S C b p)
    (t : ℝ) (x : Sphere 3) (ht : t ∈ Ioo (0 : ℝ) 1) (hx : χ x ≠ 0)
    (hp : ambient e f χ p t x ∈ r.domain) : map e r f χ p t x ≠ b := by
  obtain ⟨s, hs, hxs⟩ := hS x
  obtain ⟨c, hc, hxc⟩ := hC (map e r f χ p t x)
  have he : s.symm (s x) = x := s.left_inv hxs
  have hq : (p, (t, s x)) ∈ activeChartDomain e r f χ hf hχ s c := by
    change ((((s x ∈ s.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f χ p t (s.symm (s x)) ∈ r.domain) ∧
      map e r f χ p t (s.symm (s x)) ∈ c.source) ∧ χ (s.symm (s x)) ≠ 0)
    rw [he]
    exact ⟨⟨⟨⟨s.map_source hxs, ht⟩, hp⟩, hxc⟩, hx⟩
  have hne := ha s hs c hc (t, s x) hq
  change c (map e r f χ p t (s.symm (s x))) ≠ c b at hne
  rw [he] at hne
  exact fun h ↦ hne (congrArg c h)

theorem exists_small_generic_avoiding_manifold_family
    [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (hbound : ∀ s, ‖χ s‖ ≤ 1) (hn : n = 6)
    (b : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set SourceChart, ∃ C : Set (TargetChart n M), ∃ p : Parameters e,
      S.Finite ∧ (∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source) ∧
      C.Finite ∧ (∀ x : M, ∃ c ∈ C, x ∈ c.source) ∧ ‖p‖ < ε ∧
      GenericInCharts e r f χ hf hχ S C p ∧
      (∀ t s, ambient e f χ p t s ∈ r.domain) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f χ p)) ∧
      (∀ t s, χ s = 0 → map e r f χ p t s = f t s) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ s, map e r f χ p t s = f t s) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ s, χ s ≠ 0 → map e r f χ p t s ≠ b := by
  obtain ⟨S, hS, hScov⟩ := exists_finite_chart_cover 3 (Sphere 3)
  obtain ⟨C, hC, hCcov⟩ := exists_finite_chart_cover n M
  obtain ⟨δ, hδ, hmem, hsmooth⟩ := exists_smooth_parameter_ball e r f χ hf hχ hbound
  obtain ⟨p, hp, hgen, ha⟩ := exists_small_generic_avoiding_in_charts e r f χ hf hχ hn
    S hS.countable C hC.countable b (lt_min hε hδ)
  have hpε : ‖p‖ < ε := hp.trans_le (min_le_left _ _)
  have hpδ : ‖p‖ < δ := hp.trans_le (min_le_right _ _)
  refine ⟨S, C, p, hS, hScov, hC, hCcov, hpε, hgen, hmem p hpδ, ?_, ?_, ?_, ?_⟩
  · exact hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ hpδ)
  · exact fun t s hs ↦ map_eq_zero_cutoff e r f χ p t s hs
  · exact fun t ht s ↦ map_eq_outside e r f χ p ht s
  · exact fun t ht s hs ↦ map_ne_center_of_avoids_in_charts e r f χ hf hχ
      S C hScov hCcov b p ha t s ht hs (hmem p hpδ t s)

end NoExoticSixSphere.SpatiallyRelativeSphereFamily
