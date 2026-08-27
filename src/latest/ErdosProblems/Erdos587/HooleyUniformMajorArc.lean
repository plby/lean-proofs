import ErdosProblems.Erdos587.HooleyUniformChirp
import ErdosProblems.Erdos587.HooleyMajorArc

/-! # Smooth major arcs with a common constant for a bounded Schwartz family -/

open scoped FourierTransform SchwartzMap

namespace Erdos587

theorem exists_delta_family_smooth_major_arc_norm_bound {S : Set 𝓢(ℝ, ℂ)}
    (hS : Bornology.IsVonNBounded ℝ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ S, ∀ q : ℕ, 0 < q →
      ∀ a : ℤ, IsUnit (a : ZMod q) →
      ∀ K A θ : ℝ, 0 < K → (q : ℝ) * (1 + |A|) ≤ 4 * K →
      ‖∑' n : ℤ, quadraticResiduePhase q a n *
        (phase (θ * n) * (phase (A * (K⁻¹ * n) ^ 2) * f (K⁻¹ * n)))‖ ≤
          C * K * Real.sqrt (2 * (q : ℝ)) / ((q : ℝ) * Real.sqrt (1 + |A|)) := by
  obtain ⟨C₀, hC₀, hdecay⟩ := exists_delta_family_chirp_fourier_decay hS
  refine ⟨41 * C₀, by positivity, ?_⟩
  intro f hf
  exact delta_smooth_major_arc_norm_bound_of_decay f hC₀ (hdecay f hf)

theorem exists_delta_family_smooth_major_arc_sq_bound {S : Set 𝓢(ℝ, ℂ)}
    (hS : Bornology.IsVonNBounded ℝ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ S, ∀ q : ℕ, 0 < q →
      ∀ a : ℤ, IsUnit (a : ZMod q) →
      ∀ K β θ : ℝ, 0 < K → (q : ℝ) ≤ K → |β| ≤ 2 / ((q : ℝ) * K) →
      ‖∑' n : ℤ, phase ((((a : ℝ) / q + β) * (n : ℝ) ^ 2) + θ * n) *
        f (K⁻¹ * n)‖ ^ 2 ≤ C * K ^ 2 / ((q : ℝ) * (1 + K ^ 2 * |β|)) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_delta_family_smooth_major_arc_norm_bound hS
  refine ⟨2 * C₀ ^ 2, by positivity, ?_⟩
  intro f hf
  exact delta_smooth_major_arc_sq_bound_of_norm f hC₀ (hbound f hf)

end Erdos587
