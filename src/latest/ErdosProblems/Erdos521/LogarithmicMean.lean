/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The local expectation limit for arbitrary fixed logarithmic lengths.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LocalMeanLimit
import ErdosProblems.Erdos521.PartitionExpectation
import ErdosProblems.Erdos521.LogGridPartition

namespace Erdos521

open MeasureTheory Filter
open scoped Topology BigOperators

theorem logarithmic_mean_limit :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ → ℕ) (s : ℕ → ℝ),
      Tendsto n atTop atTop → Tendsto s atTop atTop →
      Tendsto (fun j ↦ ((n j + 1 : ℕ) : ℝ) / s j) atTop atTop →
      ∀ a ℓ : ℝ, 0 < a → 0 < ℓ →
      (∀ᶠ j : ℕ in atTop, logGrid (s j) a ℓ 1 ≤ endpointCenter C (n j)) →
      Tendsto (fun j ↦ ∫ ε,
        (intervalRootCount ε (n j) (logGrid (s j) a ℓ 0) (logGrid (s j) a ℓ 1) : ℝ) ∂sequenceLaw)
        atTop (𝓝 (ℓ / (2 * Real.pi))) := by
  obtain ⟨C, hC, hshort⟩ := local_logarithmic_mean_limit
  refine ⟨C, hC, ?_⟩
  intro n s hn hs hdegree a ℓ ha hℓ hbulk
  obtain ⟨N, hN, hwidth⟩ := exists_short_logarithmic_subdivision hℓ
  let δ := ℓ / (N : ℝ)
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ : 0 < δ := div_pos hℓ hN₀
  have hcell : ∀ i ∈ Finset.range N, Tendsto (fun j ↦ ∫ ε,
      (intervalRootCount ε (n j) (logGrid (s j) a δ i) (logGrid (s j) a δ (i + 1)) : ℝ) ∂sequenceLaw)
      atTop (𝓝 (δ / (2 * Real.pi))) := by
    intro i hi
    have hcellbulk : ∀ᶠ j : ℕ in atTop,
        logGrid (s j) (logGridCoefficient a δ i) δ 1 ≤ endpointCenter C (n j) := by
      filter_upwards [hbulk, hs.eventually_gt_atTop 0] with j hj hsj
      rw [← logGrid_shift]
      apply le_trans ((logGrid_mono hsj ha.le hδ.le) (by simpa using Finset.mem_range.mp hi))
      simpa only [δ, refined_logGrid_end _ _ _ _ hN] using hj
    have h := hshort n s hn hs hdegree (logGridCoefficient a δ i) δ
      (logGridCoefficient_pos ha δ i) hδ hwidth hcellbulk
    simpa only [← logGrid_shift, Nat.add_zero] using h
  have hsum : Tendsto (fun j ↦ ∑ i ∈ Finset.range N, ∫ ε,
      (intervalRootCount ε (n j) (logGrid (s j) a δ i) (logGrid (s j) a δ (i + 1)) : ℝ) ∂sequenceLaw)
      atTop (𝓝 (ℓ / (2 * Real.pi))) := by
    have h := tendsto_finsetSum (Finset.range N) hcell
    have heq : (∑ _i ∈ Finset.range N, δ / (2 * Real.pi)) = ℓ / (2 * Real.pi) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [δ]
      field_simp
    simpa only [heq] using h
  have hzero (i : ℕ) : Tendsto (fun j ↦ sequenceLaw.real
      {ε | powerSum ε (n j + 1) (logGrid (s j) a δ i) = 0}) atTop (𝓝 0) :=
    polynomial_zero_probability_tendsto_zero n _ hn (logGrid_point_tendsto s hs a δ i)
      ((eventually_logGrid_point_bounds s hs ha δ i).mono (fun _ h ↦ h.2.le))
  have hzeroSum := tendsto_finsetSum (Finset.range N) (fun i _ ↦ hzero i)
  have hlimit := (hsum.add (hzero 0)).sub hzeroSum
  simp only [Finset.sum_const_zero, add_zero, sub_zero] at hlimit
  apply hlimit.congr'
  filter_upwards [hs.eventually_gt_atTop 0] with j hsj
  have h := integral_intervalRootCount_grid_identity (n j) N (logGrid (s j) a δ)
    (logGrid_mono hsj ha.le hδ.le)
  simp only [δ, refined_logGrid_end _ _ _ _ hN, logGrid_zero] at h ⊢
  linarith

end Erdos521
