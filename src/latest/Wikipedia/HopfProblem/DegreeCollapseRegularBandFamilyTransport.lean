import Wikipedia.HopfProblem.DegreeCollapseMiddleFamilyStep

/-!
# Entire native basin families cross a regular band

Absence of critical values forces every source point to cross the lower
cut. A single partial flow diffeomorphism transports the whole family,
including its full backward-basin images. The target level point is
constructed from an actual source orbit, rather than supplied separately.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {ι E M F H X : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X]

theorem AdaptedSurgeryWindows.reaches_lower_in_regular_band
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : b < a) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgap : ∀ q ∈ criticalPoints E f, f q ∉ Icc b a)
    (x : {y : M // f y = a}) :
    x.val ∈ FlowCancellation.levelBasin S.flow f b := by
  obtain ⟨q, hq, r, hr, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
      S.zero S.descent S.distinct x.val
  have hra : f r < a := by simpa only [x.property] using (hheights (ha x.val x.property)).1
  have haq : a < f q := by simpa only [x.property] using (hheights (ha x.val x.property)).2
  have hrb : f r < b := by
    by_contra h
    exact hgap r hr ⟨le_of_not_gt h, hra.le⟩
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hback hforward (hab.trans haq) hrb

theorem AdaptedSurgeryWindows.exists_regular_band_family_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : b < a) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (hgap : ∀ q ∈ criticalPoints E f, f q ∉ Icc b a)
    (za : {x : M // f x = a}) (α : ι → X → {x : M // f x = a}) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
    (∀ j, Injective (α j)) →
    (∀ j x, Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
    Pairwise (fun i j => Disjoint (range (α i)) (range (α j))) →
    ∃ β : ι → X → {x : M // f x = b},
      (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (β j)) ∧
      (∀ j, IsClosedEmbedding (β j)) ∧
      (∀ j x, Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (β j) x)) ∧
      Pairwise (fun i j => Disjoint (range (β i)) (range (β j))) ∧
      (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
      ∀ j q, a < f q →
        (∀ x : {y : M // f y = a}, x ∈ range (α j) ↔
          Tendsto (fun t => S.flow t x.val) atBot (𝓝 q)) →
        ∀ y : {x : M // f x = b}, y ∈ range (β j) ↔
          Tendsto (fun t => S.flow t y.val) atBot (𝓝 q) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  dsimp only
  intro hα hαinj hαimm hpair
  obtain ⟨t, ht⟩ := S.reaches_lower_in_regular_band hf hab ha hgap za
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ := S.exists_native_family_level_transport
    hf ha hb za ⟨S.flow t za.val, ht⟩ α hα hαinj hαimm hpair
      (fun j x => S.reaches_lower_in_regular_band hf hab ha hgap (α j x))
  refine ⟨β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j q hq hfull
  exact S.transported_backward_basin_image hf hab hb q hq (α j) (β j) hfull (horbit j)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
