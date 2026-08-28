import Wikipedia.NoExoticSixSphere.ManifoldIntersectionSubmersion
import Wikipedia.NoExoticSixSphere.FiniteDiffeomorphChartCover
import Wikipedia.NoExoticSixSphere.IntersectionTraceInteriorChart

/-!
# One small perturbation is regular at every interior intersection

Parametric Sard is applied simultaneously on finite covers by genuine source
and target charts. A uniform tubular parameter ball gives an actual globally
smooth perturbed first family. The second family and both endpoint slices
are unchanged. Every interior coincidence satisfies the chart regularity
used by the previously constructed intersection-trace atlas.

The perturbation fixes endpoint slices, not whole time collars. Preservation
of collars and the ordinary-homotopy parity theorem remain separate steps.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldIntersectionFamily

open GLOrthonormalization EuclideanEmbedding ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))

def GenericInCharts (S : Set SourceChart) (C : Set (TargetChart n M)) (p : Parameters e) : Prop :=
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : ℝ × (Vector 3 × Vector 3),
    (p, x) ∈ domain e r f g hf hg s z c → difference e r f g s z c (p, x) = 0 →
    Surjective (fderiv ℝ (fun y ↦ difference e r f g s z c (p, y)) x)

theorem ae_generic_in_charts [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, GenericInCharts e r f g hf hg S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ p ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : ℝ × (Vector 3 × Vector 3),
      (p, x) ∈ domain e r f g hf hg s.val z.val c.val →
      difference e r f g s.val z.val c.val (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ difference e r f g s.val z.val c.val (p, y)) x) :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun z ↦ ae_all_iff.mpr fun c ↦
      ae_regular_intersections e r f g hf hg s.val z.val c.val μ
  exact h.mono fun p hp s hs z hz c hc ↦ hp ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩

theorem exists_small_generic_in_charts (S : Set SourceChart) (hS : S.Countable)
    (C : Set (TargetChart n M)) (hC : C.Countable) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧ GenericInCharts e r f g hf hg S C p := by
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have hdense := Measure.dense_of_ae (ae_generic_in_charts e r f g hf hg addHaar S hS C hC)
  obtain ⟨p, hp, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨p, by simpa only [dist_zero_left] using hsmall, hp⟩

end NoExoticSixSphere.ManifoldIntersectionFamily

namespace NoExoticSixSphere.ManifoldIntersectionFamily

open GLOrthonormalization EuclideanEmbedding ManifoldAffineSphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

theorem chartRegular_of_generic (S : Set SourceChart) (C : Set (TargetChart 6 M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source) (p : Parameters e)
    (hp : ∀ t x, ambient e f p t x ∈ r.domain)
    (hgen : GenericInCharts e r f g hf hg S C p) :
    IntersectionTrace.ChartRegular (ManifoldAffineSphereFamily.map e r f p) g := by
  intro a hta
  obtain ⟨s, hs, hxs⟩ := hS a.val.2.1
  obtain ⟨z, hz, hyz⟩ := hS a.val.2.2
  obtain ⟨c, hc, hxc⟩ := hC (ManifoldAffineSphereFamily.map e r f p a.val.1 a.val.2.1)
  have hyc : g a.val.1 a.val.2.2 ∈ c.source := a.property.2 ▸ hxc
  let q := (a.val.1, (s a.val.2.1, z a.val.2.2))
  have hq : (p, q) ∈ domain e r f g hf hg s z c :=
    mem_domain_of_charts e r f g hf hg s z c p a.val.1 a.val.2.1 a.val.2.2
      hta hxs hyz (hp _ _) hxc hyc
  have hzero : difference e r f g s z c (p, q) = 0 := by
    rw [difference_apply]
    change c (ManifoldAffineSphereFamily.map e r f p a.val.1
      (s.symm (s a.val.2.1))) - c (g a.val.1 (z.symm (z a.val.2.2))) = 0
    have hx : s.symm (s a.val.2.1) = a.val.2.1 := s.left_inv hxs
    have hy : z.symm (z a.val.2.2) = a.val.2.2 := z.left_inv hyz
    rw [hx, hy, a.property.2, sub_self]
  have hd := hgen s hs z hz c hc q hq hzero
  have heq : (fun y ↦ difference e r f g s z c (p, y)) =
      IntersectionTrace.coordinateDifference (ManifoldAffineSphereFamily.map e r f p) g s z c := by
    funext y
    exact difference_apply e r f g s z c (p, y)
  rw [heq] at hd
  exact ⟨s, z, c, hxs, hyz, hxc, hd⟩

include hf hg in
theorem exists_small_regular_manifold_intersections [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧
      (∀ t x, ambient e f p t x ∈ r.domain) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞
        (uncurry (ManifoldAffineSphereFamily.map e r f p)) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, ManifoldAffineSphereFamily.map e r f p t x = f t x) ∧
      IntersectionTrace.ChartRegular (ManifoldAffineSphereFamily.map e r f p) g := by
  obtain ⟨S, hS, hScov⟩ := exists_finite_chart_cover 3 (Sphere 3)
  obtain ⟨C, hC, hCcov⟩ := exists_finite_chart_cover 6 M
  obtain ⟨δ, hδ, hmem, hsmooth⟩ := exists_smooth_parameter_ball e r f hf
  obtain ⟨p, hp, hgen⟩ := exists_small_generic_in_charts e r f g hf hg S hS.countable
    C hC.countable (lt_min hε hδ)
  have hpε := hp.trans_le (min_le_left ε δ)
  have hpδ := hp.trans_le (min_le_right ε δ)
  refine ⟨p, hpε, hmem p hpδ, ?_, ?_, ?_⟩
  · exact hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ hpδ)
  · exact fun _ ht x ↦ map_eq_outside e r f p ht x
  · exact chartRegular_of_generic e r f g hf hg S C hScov hCcov p (hmem p hpδ) hgen

end NoExoticSixSphere.ManifoldIntersectionFamily
