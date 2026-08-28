import Wikipedia.SmoothSixDPoincare.NativeArcEndpointGerms
import Wikipedia.SmoothSixDPoincare.FiniteTransverseIntersections

/-!
# Two native connecting arcs with the prescribed corner boundary germs

Construct one embedded immersive arc in each compact transverse sheet. Each
interior misses the entire other sheet, so their ambient images meet exactly
at the two selected crossings. Both arcs retain the native chart germs used
by the clean corner construction. This constructs the boundary arcs, not a
complete smooth boundary neighborhood or a Whitney framing.
-/

noncomputable section

open Set Function Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]
  [T2Space N] [CompactSpace N] [T2Space P] [CompactSpace P]

/-- Both embedded sheet arcs retain exact native endpoint germs and have no extra intersections. -/
theorem exists_native_whitney_arc_pair {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Injective F) (hinjG : Injective G)
    (hdimD : 3 ≤ Module.finrank ℝ D) (hdimZ : 3 ≤ Module.finrank ℝ Z)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : ∀ x y, G y = F x → Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {x₀ x₁ : N} {y₀ y₁ : P} (hcross₀ : G y₀ = F x₀) (hcross₁ : G y₁ = F x₁)
    (hxy : x₀ ≠ x₁) (γ : Path x₀ x₁) (η : Path y₀ y₁)
    {u₀ u₁ : D} {v₀ v₁ : Z} (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0)
    (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0) :
    ∃ f : C(ℝ, N), ∃ g : C(ℝ, P),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) ∞ g ∧
      f 0 = x₀ ∧ f 1 = x₁ ∧ g 0 = y₀ ∧ g 1 = y₁ ∧
      (f =ᶠ[𝓝 (0 : ℝ)] fun t => NativeParametrization.centered (D := D) x₀ (t • u₀)) ∧
      (f =ᶠ[𝓝 (1 : ℝ)] fun t => NativeParametrization.centered (D := D) x₁ ((1 - t) • u₁)) ∧
      (g =ᶠ[𝓝 (0 : ℝ)] fun t => NativeParametrization.centered (D := Z) y₀ (t • v₀)) ∧
      (g =ᶠ[𝓝 (1 : ℝ)] fun t => NativeParametrization.centered (D := Z) y₁ ((1 - t) • v₁)) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) g t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, F (f t) ∉ range G) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, G (g t) ∉ range F) ∧
      range (fun t : unitInterval => F (f t)) ∩ range (fun t : unitInterval => G (g t)) =
        {F x₀, F x₁} := by
  have hfinite : (range F ∩ range G).Finite :=
    finite_transverse_intersections hF hG hinjF hinjG hcodim ht
  have hSF : (F ⁻¹' range G).Finite := by
    have hpre : F ⁻¹' (range F ∩ range G) = F ⁻¹' range G := by
      ext z
      simp only [mem_preimage, mem_inter_iff]
      exact and_iff_right (mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjF.injOn
  have hSG : (G ⁻¹' range F).Finite := by
    have hpre : G ⁻¹' (range F ∩ range G) = G ⁻¹' range F := by
      ext z
      simp only [mem_preimage, mem_inter_iff]
      exact and_iff_left (mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjG.injOn
  have hy : y₀ ≠ y₁ := by
    intro heq
    apply hxy
    exact hinjF (hcross₀.symm.trans ((congrArg G heq).trans hcross₁))
  obtain ⟨f, hf, hf0, hf1, hfg0, hfg1, hembf, hif, havoidf⟩ :=
    exists_embedded_arc_with_native_endpoint_germs (D := D) γ hxy hdimD hu₀ hu₁ hSF
  obtain ⟨g, hg, hg0, hg1, hgg0, hgg1, hembg, hig, havoidg⟩ :=
    exists_embedded_arc_with_native_endpoint_germs (D := Z) η hy hdimZ hv₀ hv₁ hSG
  refine ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hfg0, hfg1, hgg0, hgg1,
    hembf, hembg, hif, hig, havoidf, havoidg, ?_⟩
  ext w
  constructor
  · rintro ⟨⟨t, rfl⟩, ⟨s, hs⟩⟩
    by_cases ht0 : (t : ℝ) = 0
    · simp only [ht0, hf0]
      exact mem_insert _ _
    by_cases ht1 : (t : ℝ) = 1
    · simp only [ht1, hf1]
      exact mem_insert_of_mem _ (mem_singleton _)
    have hti : (t : ℝ) ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
    exact (havoidf t hti ⟨g s, hs⟩).elim
  · intro hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact ⟨⟨0, congrArg F hf0⟩, ⟨0, (congrArg G hg0).trans hcross₀⟩⟩
    · exact ⟨⟨1, congrArg F hf1⟩, ⟨1, (congrArg G hg1).trans hcross₁⟩⟩

end Wikipedia.SmoothSixDPoincare
