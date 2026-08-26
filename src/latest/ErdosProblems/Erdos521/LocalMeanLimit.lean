/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The expected number of roots on a short logarithmic interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogIntervalMoments
import ErdosProblems.Erdos521.LogGridExpectation
import ErdosProblems.Erdos521.LogGridDisagreement
import ErdosProblems.Erdos521.RootGridError
import ErdosProblems.Erdos521.RefinementError
import ErdosProblems.Erdos521.ApproximationLimits

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem local_logarithmic_mean_limit :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ → ℕ) (s : ℕ → ℝ),
      Tendsto n atTop atTop → Tendsto s atTop atTop →
      Tendsto (fun j ↦ ((n j + 1 : ℕ) : ℝ) / s j) atTop atTop →
      ∀ a ℓ : ℝ, 0 < a → 0 < ℓ → Real.exp ℓ - 1 ≤ 1 / 8 →
      (∀ᶠ j : ℕ in atTop, logGrid (s j) a ℓ 1 ≤ endpointCenter C (n j)) →
      Tendsto (fun j ↦ ∫ ε,
        (intervalRootCount ε (n j) (logGrid (s j) a ℓ 0) (logGrid (s j) a ℓ 1) : ℝ) ∂sequenceLaw)
        atTop (𝓝 (ℓ / (2 * Real.pi))) := by
  obtain ⟨C₀, hC₀, hdis⟩ := logGrid_disagreement_probability
  let C := max C₀ (localMomentBulkConstant 8)
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n s hn hs hdegree a ℓ ha hℓ hwidth hbulk
  let f := fun j ↦ ∫ ε,
    (intervalRootCount ε (n j) (logGrid (s j) a ℓ 0) (logGrid (s j) a ℓ 1) : ℝ) ∂sequenceLaw
  let v := fun N : ℕ ↦ (N : ℝ) * (gaussianPair (logScaleCorrelation (ℓ / N))).real pairSignFlip
  let e := fun N : ℕ ↦ (N : ℝ) ^ (1 / 6 : ℝ) * N * (normalizedSmallBallConstant + 96) *
    (Real.exp (ℓ / N) - 1) ^ (4 / 3 : ℝ) + localMomentBoundConstant 8 / ((N : ℝ) ^ (1 / 6 : ℝ)) ^ 7
  have hv : Tendsto v atTop (𝓝 (ℓ / (2 * Real.pi))) := gaussian_grid_refinement_limit hℓ
  have he : Tendsto e atTop (𝓝 0) := by
    have hK : 0 ≤ normalizedSmallBallConstant + 96 := by have := normalizedSmallBallConstant_pos; linarith
    simpa only [e, add_zero] using
      (refinement_probability_error_tendsto_zero hℓ hK).add
        (refinement_moment_error_tendsto_zero (localMomentBoundConstant 8))
  change Tendsto f atTop (𝓝 (ℓ / (2 * Real.pi)))
  apply tendsto_of_refined_approximations hv he
  intro N hN η hη
  let δ := ℓ / (N : ℝ)
  let R := (N : ℝ) ^ (1 / 6 : ℝ)
  let D := (N : ℝ) * ((normalizedSmallBallConstant + 96) * (Real.exp δ - 1) ^ (4 / 3 : ℝ))
  let g := fun j ↦ ∫ ε, (gridSignChanges ε (n j) (logGrid (s j) a δ) N : ℝ) ∂sequenceLaw
  let M := fun j ↦ ∫ ε,
    (intervalRootCount ε (n j) (logGrid (s j) a ℓ 0) (logGrid (s j) a ℓ 1) : ℝ) ^ 8 ∂sequenceLaw
  let P := fun j ↦ sequenceLaw.real {ε |
    intervalRootCount ε (n j) (logGrid (s j) a ℓ 0) (logGrid (s j) a ℓ 1) ≠
      gridSignChanges ε (n j) (logGrid (s j) a δ) N}
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ : 0 < δ := div_pos hℓ hN₀
  have hR : 0 < R := Real.rpow_pos_of_pos hN₀ _
  have hM : ∀ᶠ j : ℕ in atTop, M j ≤ localMomentBoundConstant 8 :=
    eventually_logInterval_eighth_moment n s hn hs (le_max_right _ _) ha hwidth hbulk
  have hbulk₀ : ∀ᶠ j : ℕ in atTop, logGrid (s j) a δ N ≤ endpointCenter C₀ (n j) := by
    filter_upwards [hbulk, hn.eventually_ge_atTop 1] with j hj hjn
    rw [show δ = ℓ / (N : ℝ) from rfl, refined_logGrid_end _ _ _ _ hN]
    exact hj.trans (endpointCenter_antitone_constant (le_max_left _ _) hjn)
  have hP : ∀ e' : ℝ, 0 < e' → ∀ᶠ j : ℕ in atTop, P j ≤ D + e' := by
    intro e' he'
    have h := hdis n s hn hs hdegree a δ ha hδ N hbulk₀ e' he'
    simpa only [P, D, δ, refined_logGrid_end _ _ _ _ hN, logGrid_zero] using h
  have herror : ∀ᶠ j : ℕ in atTop, 0 ≤ f j - g j ∧ f j - g j ≤ R * P j + M j / R ^ 7 := by
    filter_upwards [hs.eventually_gt_atTop 0] with j hsj
    have h := root_grid_expectation_error (n j) N (logGrid (s j) a δ)
      (logGrid_mono hsj ha.le hδ.le) hR
    simpa only [f, g, P, M, δ, refined_logGrid_end _ _ _ _ hN, logGrid_zero] using h
  have hg : Tendsto g atTop (𝓝 (v N)) := logGrid_sign_expectation_tendsto n s hn hs hdegree ha δ N
  have h := eventually_approximation_bounds hR herror hM hP hg hη
  have heq : R * D + localMomentBoundConstant 8 / R ^ 7 = e N := by
    dsimp [R, D, e, δ]
    ring
  simpa only [heq] using h

end Erdos521
