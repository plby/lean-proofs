import Wikipedia.NoExoticSixSphere.FamilyEmbeddedCollar

/-!
# Uniform collars for immersive families with selected embedded slices

Immersion is required throughout the compact parameter set; injectivity is
required only on a compact selected subset. A common collar satisfies both
conditions. Intermediate slices may have self-intersections.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.ManifoldImmersion

namespace NoExoticSixSphere.FamilyEmbedding

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ F] in
theorem exists_uniform_immersive_annulus {K : Set P} (hK : IsCompact K)
    (f : P → E → F) (hf : ContDiff ℝ ∞ (uncurry f))
    (hd : ∀ t ∈ K, ∀ x ∈ sphere (0 : E) 1, Injective (fderiv ℝ (f t) x))
    {U : Set (P × E)} (hU : IsOpen U) (hSU : K ×ˢ sphere (0 : E) 1 ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      K ×ˢ (closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖}) ⊆ U ∧
      ∀ t ∈ K, ∀ x ∈ closedBall (0 : E) 1,
        r ≤ ‖x‖ → Injective (fderiv ℝ (f t) x) := by
  let O : Set (P × E) := {q | Injective (fderiv ℝ (f q.1) q.2)}
  have hO : IsOpen O := ContinuousLinearMap.isOpen_injective.preimage
    (DiskHomotopy.continuous_spatial_fderiv f hf)
  have hKO : K ×ˢ sphere (0 : E) 1 ⊆ O := by
    intro q hq
    exact hd q.1 hq.1 q.2 hq.2
  obtain ⟨W, T, _, hT, hKW, hST, hWT⟩ :=
    generalized_tube_lemma hK (isCompact_sphere (0 : E) 1) (hO.inter hU)
      (fun q hq ↦ ⟨hKO hq, hSU hq⟩)
  obtain ⟨r, hr, hr1, hRT⟩ := exists_annulus_subset_sphere_neighborhood hT hST
  have hR : K ×ˢ (closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖}) ⊆ O ∩ U :=
    fun q hq ↦ hWT ⟨hKW hq.1, hRT hq.2⟩
  refine ⟨r, hr, hr1, fun q hq ↦ (hR hq).2, ?_⟩
  intro t ht x hx hrx
  have htx : (t, x) ∈ O ∩ U := hR ⟨ht, hx, hrx⟩
  exact htx.1

theorem exists_uniform_regular_annulus {K B : Set P} (hK : IsCompact K) (hB : IsCompact B)
    (hBK : B ⊆ K) (f : P → E → F) (hf : ContDiff ℝ ∞ (uncurry f))
    (hi : ∀ t ∈ B, InjOn (f t) (sphere (0 : E) 1))
    (hd : ∀ t ∈ K, ∀ x ∈ sphere (0 : E) 1, Injective (fderiv ℝ (f t) x))
    {U : Set (P × E)} (hU : IsOpen U) (hSU : K ×ˢ sphere (0 : E) 1 ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      K ×ˢ (closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖}) ⊆ U ∧
      (∀ t ∈ B, InjOn (f t) (closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖})) ∧
      ∀ t ∈ K, ∀ x ∈ closedBall (0 : E) 1,
        r ≤ ‖x‖ → Injective (fderiv ℝ (f t) x) := by
  obtain ⟨r, hr, hr1, hRU, hRd⟩ := exists_uniform_immersive_annulus hK f hf hd hU hSU
  obtain ⟨s, _, hs1, _, hSi, _⟩ := exists_uniform_embedded_immersive_annulus hB f hf hi
    (fun t ht ↦ hd t (hBK ht)) isOpen_univ (subset_univ _)
  refine ⟨max r s, lt_of_lt_of_le hr (le_max_left _ _), max_lt hr1 hs1, ?_, ?_, ?_⟩
  · intro q hq
    exact hRU ⟨hq.1, hq.2.1, show r ≤ ‖q.2‖ from (le_max_left r s).trans hq.2.2⟩
  · intro t ht
    apply (hSi t ht).mono
    intro x hx
    exact ⟨hx.1, show s ≤ ‖x‖ from (le_max_right r s).trans hx.2⟩
  · intro t ht x hx hrx
    exact hRd t ht x hx ((le_max_left r s).trans hrx)

end NoExoticSixSphere.FamilyEmbedding
