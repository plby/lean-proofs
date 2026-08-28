import Wikipedia.HopfProblem.HolomorphicCousinGlobal

/-!
# Infinity extensions on every member of a Cousin cover

The proved Cousin solver supplies an analytic infinity expression on one
distinguished patch. On any other patch meeting infinity, its actual
overlap coefficient supplies the extension by addition. The construction
uses the original cocycle and the solver's equations, rather than an
assumed analytic continuation or a refined-cover comparison theorem.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

open HolomorphicCousin

/-- Transport the constructed infinity extension across an actual
holomorphic overlap coefficient. -/
theorem infinity_extension_of_overlap {ι : Type*} {U : ι → Set ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution U h i₀ R) (i : ι)
    {r : ℝ} (hr : 0 < r) (k : ℂ → ℂ)
    (hk : AnalyticOnNhd ℂ k (ball 0 r))
    (hi : ∀ u ∈ ball (0 : ℂ) r, u ≠ 0 → u⁻¹ ∈ U i)
    (hi₀ : ∀ u ∈ ball (0 : ℂ) r, u ≠ 0 → u⁻¹ ∈ U i₀)
    (he : ∀ u ∈ ball (0 : ℂ) r, u ≠ 0 → h i i₀ u⁻¹ = k u) :
    ∃ t : ℝ, 0 < t ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (ball 0 t) ∧ F 0 = k 0 ∧
      ∀ u ∈ ball (0 : ℂ) t, u ≠ 0 → s.localPart i u⁻¹ = F u := by
  refine ⟨min r R⁻¹, lt_min hr (inv_pos.mpr hR),
    fun u => k u + s.infinityPart u, ?_, ?_, ?_⟩
  · exact (hk.mono (ball_subset_ball (min_le_left _ _))).add
      (s.infinity_analytic.mono (ball_subset_ball (min_le_right _ _)))
  · simp only [s.infinity_zero, add_zero]
  · intro u hu hu₀
    have hur : u ∈ ball (0 : ℂ) r :=
      ball_subset_ball (min_le_left _ _) hu
    have huR : ‖u‖ < R⁻¹ := by
      simpa only [mem_ball, dist_zero_right] using
        (ball_subset_ball (min_le_right r R⁻¹) hu)
    have hlarge : R < ‖u⁻¹‖ := by
      rw [norm_inv]
      exact (lt_inv_comm₀ hR (norm_pos_iff.mpr hu₀)).mpr huR
    have hc := s.equation i i₀ u⁻¹ (hi u hur hu₀) (hi₀ u hur hu₀)
    rw [s.atInfinity u⁻¹ hlarge, inv_inv, he u hur hu₀] at hc
    exact sub_eq_iff_eq_add.mp hc

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
