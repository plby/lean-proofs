import Util.Bernays.GenusCountBounds
import Util.Bernays.SquareSeriesApproximation
import Util.Bernays.LogKernelUniformBound

/-!
# Unconditional smoothed cancellation for every nontrivial genus character
-/

open Filter Topology

namespace Bernays

theorem LSeries_square_W21_cancellation_of_logCountBound (a : ℕ → ℂ) (F : ℂ → ℂ)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (had : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (LSeries a) s)
    (hF : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s)
    (heq : ∀ s : ℂ, 1 < s.re → F s = LSeries a s ^ 2)
    (hne : ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ F s ≠ 0)
    (hcheby : cheby a) (hbound : ∀ n : ℕ, ‖a n‖ ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ)))) (ψ : W21) :
    Tendsto (fun δ : ℝ => ‖smoothedSeries a ψ δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
  apply LSeries_square_W21_cancellation a F ha had hF heq hne hcheby
    (K := 32 * Real.pi ^ 2 + 2 * C * (1 + 2 * Real.pi ^ 2)) (by positivity)
  exact logarithmicKernelMass_eventually_scaled_bound hbound hcheby hC hcount

theorem genusLocal_smoothed_cancellation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
    ∀ φ : W21,
      Tendsto (fun δ : ℝ => ‖smoothedSeries (genusLocalAF hD ψ) φ δ‖ / Real.sqrt δ)
        (𝓝[>] 0) (𝓝 0) := by
  let := quadraticOrderIsDomain hD
  intro ψ hψ φ
  obtain ⟨F, hF, heq, hne⟩ := genusLocalLSeries_continuation_nonzero hD ψ hψ
  obtain ⟨C, hC, hcount⟩ := genusLocalAF_logCountBound hD
  exact LSeries_square_W21_cancellation_of_logCountBound (genusLocalAF hD ψ) F
    (genusLocalAF_summable hD ψ) (genusLocalLSeries_differentiableAt hD ψ)
    hF heq hne (genusLocalAF_cheby hD ψ) (genusLocalAF_norm_le_one hD ψ) hC.le (hcount ψ) φ

end Bernays
