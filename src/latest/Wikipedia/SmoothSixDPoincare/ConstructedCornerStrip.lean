import Wikipedia.SmoothSixDPoincare.ParametrizedCornerStrip
import Wikipedia.SmoothSixDPoincare.NativeCornerNormalGerm
import Wikipedia.SmoothSixDPoincare.NativeStripGerms
import Wikipedia.SmoothSixDPoincare.StripReflection
import Wikipedia.SmoothSixDPoincare.StripEndpointObstacle
import Wikipedia.SmoothSixDPoincare.StripNormalData

/-!
# Assemble a native strip along the specified arc and two actual corner maps

The ambient chart is constructed along the given embedded immersive arc and
retains its endpoint germs. The supplied native corner maps, which can be
shared by the two boundary arcs, determine both full endpoint germs. Native
transversality supplies their nonzero normal derivatives. The assembled strip
meets the first full sheet exactly on its center and the second full sheet
exactly on its two vertical endpoint axes.
-/

noncomputable section

open Set Function Filter Module Metric Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]
  [T2Space N] [CompactSpace N] [CompactSpace P]

/-- Construct the native two-sheet-clean strip from the specified arc and shared corner data. -/
theorem exists_strip_along_arc_matching_native_corners {F : N → M} {G : P → M} {f : ℝ → N}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f) (hinjf : InjOn f (Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t))
    {x₀ x₁ : N} {y₀ y₁ : P} (hf₀ : f 0 = x₀) (hf₁ : f 1 = x₁)
    (hcross₀ : G y₀ = F x₀) (hcross₁ : G y₁ = F x₁)
    (ht₀ : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x₀).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y₀)))
    (ht₁ : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x₁).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y₁)))
    (n : ℕ) (hsheet : 1 + n = finrank ℝ D)
    (hcodim : finrank ℝ D + finrank ℝ Z = finrank ℝ E) (hdimZ : 2 ≤ finrank ℝ Z)
    {u₀ u₁ : D} {v₀ v₁ : Z} (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    (hfg₀ : f =ᶠ[𝓝 (0 : ℝ)] fun t => NativeParametrization.centered (D := D) x₀ (t • u₀))
    (hfg₁ : f =ᶠ[𝓝 (1 : ℝ)] fun t =>
      NativeParametrization.centered (D := D) x₁ ((1 - t) • u₁))
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, F (f t) ∉ range G)
    {k₀ k₁ : (ℝ × ℝ) → M} {U₀ U₁ : Set (ℝ × ℝ)}
    (hk₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₀ U₀)
    (hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0U₀ : (0 : ℝ × ℝ) ∈ U₀) (h0U₁ : (0 : ℝ × ℝ) ∈ U₁)
    (hl₀ : ∀ t, (t, 0) ∈ U₀ →
      k₀ (t, 0) = F (NativeParametrization.centered (D := D) x₀ (t • u₀)))
    (hl₁ : ∀ t, (t, 0) ∈ U₁ →
      k₁ (t, 0) = F (NativeParametrization.centered (D := D) x₁ (t • u₁)))
    (hr₀ : ∀ s, (0, s) ∈ U₀ →
      k₀ (0, s) = G (NativeParametrization.centered (D := Z) y₀ (s • v₀)))
    (hr₁ : ∀ s, (0, s) ∈ U₁ →
      k₁ (0, s) = G (NativeParametrization.centered (D := Z) y₁ (s • v₁)))
    (hcG₀ : ∀ p ∈ U₀, k₀ p ∈ range G ↔ p.1 = 0)
    (hcG₁ : ∀ p ∈ U₁, k₁ p ∈ range G ↔ p.1 = 0)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo (F ∘ f) (Icc (0 : ℝ) 1) O) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set (ℝ × ℝ), IsOpen W ∧
      Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ W ∧ ∃ k : (ℝ × ℝ) → M,
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧ InjOn k W ∧ MapsTo k W O ∧
        IsClosedEmbedding (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε => k p) ∧
        (∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
        (∀ p ∈ W, k p ∈ range F ↔ p.2 = 0) ∧
        (∀ p ∈ W, k p ∈ range G ↔ p.1 = 0 ∨ p.1 = 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, k (t, 0) = F (f t)) ∧
        (k =ᶠ[𝓝 (0, 0)] k₀) ∧ (k =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse) ∧
        Nonempty (StripNormalData (EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℝ (Fin (finrank ℝ Z))) (E := E) (range F) k) := by
  let c₀ := NativeParametrization.centered (D := Z) y₀
  let c₁ := NativeParametrization.centered (D := Z) y₁
  have hc₀ : (0 : Z) ∈ c₀.source := NativeParametrization.zero_mem_centered_source y₀
  have hc₁ : (0 : Z) ∈ c₁.source := NativeParametrization.zero_mem_centered_source y₁
  have hcy₀ : c₀ 0 = y₀ := NativeParametrization.centered_zero y₀
  have hcy₁ : c₁ 0 = y₁ := NativeParametrization.centered_zero y₁
  have hcross₀' : G (c₀ 0) = F (f 0) := by rw [hcy₀, hf₀]; exact hcross₀
  have hcross₁' : G (c₁ 0) = F (f 1) := by rw [hcy₁, hf₁]; exact hcross₁
  have ht₀' : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₀ 0))) := by
    rw [hf₀, hcy₀]
    exact ht₀
  have ht₁' : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₁ 0))) := by
    rw [hf₁, hcy₁]
    exact ht₁
  have hleft₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] (F ∘ f) := by
    have haxis := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (hU₀.mem_nhds h0U₀)
    filter_upwards [haxis, hfg₀] with t ht hft
    change k₀ (t, 0) = F (f t)
    rw [hl₀ t ht, hft]
  have hrev : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 1) := by
    have he : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 (1 - 0)) :=
      (show Continuous (fun t : ℝ => 1 - t) by fun_prop).continuousAt
    simpa only [sub_zero] using he
  have hleft₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 0] fun t => F (f (1 - t)) := by
    have haxis := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (hU₁.mem_nhds h0U₁)
    filter_upwards [haxis, hfg₁.comp_tendsto hrev] with t ht hft
    change f (1 - t) = NativeParametrization.centered (D := D) x₁
      ((1 - (1 - t)) • u₁) at hft
    rw [hl₁ t ht, hft]
    have he : 1 - (1 - t) = t := by ring
    rw [he]
  exact exists_strip_along_arc_matching_parametrized_corners hF hG hembF hiF hf hinjf hif
    c₀ c₁ hc₀ hc₁ hcross₀' hcross₁' ht₀' ht₁' n hsheet hcodim hdimZ hv₀ hv₁ havoid
    hk₀ hk₁ hU₀ hU₁ h0U₀ h0U₁ hleft₀ hleft₁ hr₀ hr₁ hcG₀ hcG₁ hO hfO

end Wikipedia.SmoothSixDPoincare
