import Wikipedia.HopfProblem.DegreeCollapseNativeBeltBasinImage
import Wikipedia.HopfProblem.DegreeCollapseRegularBandLevelBasins

/-!
# Compact entire endpoint sections and transport on original orbits

The original belt and attaching maps parametrize the entire corresponding
endpoint sections, hence those sections are compact. A homeomorphism of
levels that moves every point along its original orbit preserves every
orbit-invariant predicate and transports compact sections to compact
sections. No closedness of a global stable or unstable set is assumed.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem image_flow_invariant_section {X A B : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B] (F : Flow ℝ X) (e : A ≃ₜ B)
    (ι : A → X) (κ : B → X) (horbit : ∀ x, ∃ t, F t (ι x) = κ (e x))
    {P : X → Prop} (hP : ∀ t x, P (F t x) ↔ P x) :
    e '' {x | P (ι x)} = {y | P (κ y)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := horbit x
    have hh := (hP t (ι x)).mpr hx
    rwa [ht] at hh
  · intro hy
    obtain ⟨t, ht⟩ := horbit (e.symm y)
    have heq : e (e.symm y) = y := e.apply_symm_apply y
    rw [heq] at ht
    refine ⟨e.symm y, ?_, heq⟩
    apply (hP t (ι (e.symm y))).mp
    rwa [ht]

theorem isCompact_flow_invariant_section {X A B : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B] (F : Flow ℝ X) (e : A ≃ₜ B)
    (ι : A → X) (κ : B → X) (horbit : ∀ x, ∃ t, F t (ι x) = κ (e x))
    {P : X → Prop} (hP : ∀ t x, P (F t x) ↔ P x)
    (hcompact : IsCompact {x : A | P (ι x)}) : IsCompact {y : B | P (κ y)} := by
  rw [← image_flow_invariant_section F e ι κ horbit hP]
  exact hcompact.image e.continuous

theorem isCompact_flow_invariant_section_iff {X A B : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B] (F : Flow ℝ X) (e : A ≃ₜ B)
    (ι : A → X) (κ : B → X) (horbit : ∀ x, ∃ t, F t (ι x) = κ (e x))
    {P : X → Prop} (hP : ∀ t x, P (F t x) ↔ P x) :
    IsCompact {y : B | P (κ y)} ↔ IsCompact {x : A | P (ι x)} := by
  rw [← image_flow_invariant_section F e ι κ horbit hP]
  exact e.isCompact_image

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

open Classical in
theorem isCompact_native_belt_basin (c : SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (r : ℝ) (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsCompact {x : {y : M // f y = f p + r ^ 2} |
      Tendsto (fun t => F t (x : M)) atTop (𝓝 p)} := by
  have heq : {x : {y : M // f y = f p + r ^ 2} |
      Tendsto (fun t => F t (x : M)) atTop (𝓝 p)} = range (c.beltCoreMap r hr hblock) := by
    ext x
    simpa only [mem_setOf_eq, mem_range, Subtype.ext_iff] using
      native_belt_core_basin_iff c hf hV F hF r hr hblock hfield hboundary x.property
  rw [heq]
  exact isCompact_range (c.beltCoreMap r hr hblock).continuous

open Classical in
theorem isCompact_native_attaching_basin (c : SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (r : ℝ) (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsCompact {x : {y : M // f y = f p - r ^ 2} |
      Tendsto (fun t => F t (x : M)) atBot (𝓝 p)} := by
  have heq : {x : {y : M // f y = f p - r ^ 2} |
      Tendsto (fun t => F t (x : M)) atBot (𝓝 p)} = range (c.attachingCoreMap r hr hblock) := by
    ext x
    simpa only [mem_setOf_eq, mem_range, Subtype.ext_iff] using
      native_attaching_core_basin_iff c hf hV F hF r hr hblock hfield hboundary x.property
  rw [heq]
  exact isCompact_range (c.attachingCoreMap r hr hblock).continuous

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
