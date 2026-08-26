/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform moments on bulk intervals of any fixed logarithmic length.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PartitionMoments
import ErdosProblems.Erdos521.LogGridPartition

namespace Erdos521

open MeasureTheory Filter

theorem eventually_logarithmic_moments (p : ℕ) (hp : 1 ≤ p) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop, ∀ s a : ℝ, 0 < s → 0 < a →
      9 / 10 ≤ logGrid s a ℓ 0 →
      logGrid s a ℓ 1 ≤ endpointCenter (localMomentBulkConstant p) n →
      (∫ ε, (intervalRootCount ε n (logGrid s a ℓ 0) (logGrid s a ℓ 1) : ℝ) ^ p ∂sequenceLaw) ≤ B := by
  obtain ⟨N, hN, hwidth⟩ := exists_short_logarithmic_subdivision hℓ
  let δ := ℓ / (N : ℝ)
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ : 0 < δ := div_pos hℓ hN₀
  refine ⟨(N : ℝ) ^ p * localMomentBoundConstant p,
    mul_pos (pow_pos hN₀ _) (localMomentBoundConstant_pos p), ?_⟩
  filter_upwards [eventually_bulk_interval_moments p] with n hn
  intro s a hs ha hlower hupper
  have hg := logGrid_mono hs ha.le hδ.le
  have hcell (i : ℕ) (hi : i ∈ Finset.range N) :
      (∫ ε, (intervalRootCount ε n (logGrid s a δ i) (logGrid s a δ (i + 1)) : ℝ) ^ p ∂sequenceLaw) ≤
        localMomentBoundConstant p := by
    have hiN : i + 1 ≤ N := by simpa using Finset.mem_range.mp hi
    have hi₁ : logGrid s a δ (i + 1) < 1 :=
      sub_lt_self _ (div_pos (logGridCoefficient_pos ha δ (i + 1)) hs)
    apply hn _ _
    · constructor
      · have hlow₀ : 9 / 10 ≤ logGrid s a δ 0 := by simpa only [logGrid_zero] using hlower
        exact hlow₀.trans (hg (Nat.zero_le (i + 1)))
      · exact (hg hiN).trans (by simpa only [δ, refined_logGrid_end _ _ _ _ hN] using hupper)
    · rw [logGrid_width]
      have h := mul_le_mul_of_nonneg_right hwidth (sub_nonneg.mpr hi₁.le)
      dsimp only [δ]
      nlinarith
  have h := integral_intervalRootCount_partition_pow_le n N p hN hp (logGrid s a δ) hg hcell
  simpa only [δ, refined_logGrid_end _ _ _ _ hN, logGrid_zero] using h

end Erdos521
