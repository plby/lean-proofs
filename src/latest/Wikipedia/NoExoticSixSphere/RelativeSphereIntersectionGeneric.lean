import Wikipedia.NoExoticSixSphere.RelativeSphereIntersectionSubmersion
import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereGenericParameter

/-!
# One parameter controls relative self-intersections and mutual intersections

Countable intersection over actual charts combines jet and self-double-point
regularity, center avoidance, and intersections with the fixed sphere. The
same arbitrarily small affine parameter satisfies all three requirements.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RelativeSphereIntersectionFamily

open GLOrthonormalization EuclideanEmbedding
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f g : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
  (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)

def GenericInCharts (S : Set SourceChart) (C : Set (TargetChart n M)) (p : Parameters e) : Prop :=
  ∀ s ∈ S, ∀ z ∈ S, ∀ c ∈ C, ∀ x : ℝ × (Vector 3 × Vector 3),
    (p, x) ∈ domain e r f g χ hf hg hχ s z c →
    difference e r f g χ s z c (p, x) = 0 →
    Surjective (fderiv ℝ (fun y ↦ difference e r f g χ s z c (p, y)) x)

theorem ae_generic_in_charts [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, GenericInCharts e r f g χ hf hg hχ S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ p ∂μ, ∀ s : S, ∀ z : S, ∀ c : C, ∀ x : ℝ × (Vector 3 × Vector 3),
      (p, x) ∈ domain e r f g χ hf hg hχ s.val z.val c.val →
      difference e r f g χ s.val z.val c.val (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ difference e r f g χ s.val z.val c.val (p, y)) x) :=
    ae_all_iff.mpr fun s ↦ ae_all_iff.mpr fun z ↦ ae_all_iff.mpr fun c ↦
      ae_regular_intersections e r f g χ hf hg hχ s.val z.val c.val μ
  exact h.mono fun p hp s hs z hz c hc ↦ hp ⟨s, hs⟩ ⟨z, hz⟩ ⟨c, hc⟩

theorem exists_small_simultaneous_in_charts (hn : n = 6)
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart n M)) (hC : C.Countable)
    (b : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧
      SpatiallyRelativeSphereFamily.GenericInCharts e r f χ hf hχ S C p ∧
      SpatiallyRelativeSphereFamily.AvoidsCenterInCharts e r f χ hf hχ S C b p ∧
      GenericInCharts e r f g χ hf hg hχ S C p := by
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have hrel := SpatiallyRelativeSphereFamily.ae_generic_in_charts e r f χ addHaar
    hf hχ hn S hS C hC
  have hav := SpatiallyRelativeSphereFamily.ae_avoids_center_in_charts e r f χ addHaar
    hf hχ hn S hS C hC b
  have hmut := ae_generic_in_charts e r f g χ hf hg hχ addHaar S hS C hC
  have hdense := Measure.dense_of_ae (hrel.and (hav.and hmut))
  obtain ⟨p, hp, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨p, by simpa only [dist_zero_left] using hsmall, hp⟩

end NoExoticSixSphere.RelativeSphereIntersectionFamily
