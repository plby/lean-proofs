import Wikipedia.SmoothSixDPoincare.ManifoldCriticalPoints

/-!
# A compact regular time function has a protected Morse band at zero

The native critical set is compact and avoids the regular zero fiber.
Its actual time values are therefore uniformly separated from zero.
Inside a smaller closed band every point is regular, hence Morse. This
supplies the protected starting region for relative Morse perturbation.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse

open Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}

theorem regular_zero_not_critical
    (hreg : ∀ p, f p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p))
    (p : M) (hp : f p = 0) : p ∉ criticalPoints E f := by
  intro hcrit
  have hs : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p : E →L[ℝ] ℝ) := hreg p hp
  obtain ⟨v, hv⟩ := hs (1 : ℝ)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0 at hcrit
  rw [hcrit] at hv
  exact (zero_ne_one : (0 : ℝ) ≠ 1) hv

theorem isMorseAt_of_not_critical (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : M) (hp : p ∉ criticalPoints E f) : IsMorseAt E f p := by
  refine ⟨chartAt E p, IsManifold.chart_mem_maximalAtlas p, mem_chart_source E p, Or.inl ?_⟩
  intro h
  exact hp ((mem_criticalPoints_iff hf (IsManifold.chart_mem_maximalAtlas p)
    (mem_chart_source E p)).mpr h)

theorem exists_regular_zero_band [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ p, f p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : M, |f p| ≤ δ → p ∉ criticalPoints E f := by
  by_cases hK : (criticalPoints E f).Nonempty
  · obtain ⟨p, hp, hmin⟩ := (criticalPoints_isClosed hf).isCompact.exists_isMinOn hK
      hf.continuous.abs.continuousOn
    have hp0 : 0 < |f p| := abs_pos.mpr (fun h ↦ regular_zero_not_critical hreg p h hp)
    refine ⟨|f p| / 2, half_pos hp0, ?_⟩
    intro q hq hcrit
    have hmin' : |f p| ≤ |f q| := hmin hcrit
    exact (not_le_of_gt (half_lt_self hp0)) (hmin'.trans hq)
  · exact ⟨1, zero_lt_one, fun p _ hp ↦ hK ⟨p, hp⟩⟩

theorem exists_morse_zero_band [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ p, f p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p)) :
    ∃ δ : ℝ, 0 < δ ∧ IsMorseOn E f {p : M | |f p| ≤ δ} := by
  obtain ⟨δ, hδ, hband⟩ := exists_regular_zero_band hf hreg
  exact ⟨δ, hδ, fun p hp ↦ isMorseAt_of_not_critical hf p (hband p hp)⟩

end Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse
