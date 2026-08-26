/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Concentration for all capped dyadic-window counts, grouped by residues.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ColoredWindows
import ErdosProblems.Erdos521.BoundedSumMGF
import ErdosProblems.Erdos521.ResidueSums

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem colored_window_grid_concentration (n q T : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ)
    (S : Finset ℕ) {t : ℝ} (ht : 0 ≤ t) :
    sequenceLaw.real {ε | t ≤ |∑ k ∈ S,
      ((min (windowGridSignChanges ε (dyadicCoefficientWindow n k q) (g k) (N k)) T : ℝ) -
        ∫ ζ, (min (windowGridSignChanges ζ (dyadicCoefficientWindow n k q) (g k) (N k)) T : ℝ) ∂sequenceLaw)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((2 * q + 1 : ℕ) : ℝ) ^ 2 * (S.card : ℝ) * ((T : ℝ) / 2) ^ 2)) := by
  let X := fun k (ε : ℕ → ℝ) ↦
    (min (windowGridSignChanges ε (dyadicCoefficientWindow n k q) (g k) (N k)) T : ℝ)
  let Y := fun c k (ε : ℕ → ℝ) ↦ if k % (2 * q + 1) = c then X k ε else 0
  let B := fun c (ε : ℕ → ℝ) ↦ ∑ k ∈ S, (Y c k ε - ∫ ζ, Y c k ζ ∂sequenceLaw)
  have hX (k : ℕ) : Measurable (X k) :=
    ((measurable_of_countable (fun m : ℕ ↦ (m : ℝ))).comp
      (measurable_windowGridSignChanges (dyadicCoefficientWindow n k q) (g k) (N k))).min measurable_const
  have hY (c k : ℕ) : Measurable (Y c k) := by
    by_cases h : k % (2 * q + 1) = c
    · simpa only [Y, if_pos h] using hX k
    · simpa only [Y, if_neg h] using (measurable_const : Measurable (fun _ : ℕ → ℝ ↦ (0 : ℝ)))
  have hbound (c k : ℕ) : ∀ᵐ ε ∂sequenceLaw, Y c k ε ∈ Set.Icc 0 (T : ℝ) := by
    filter_upwards [] with ε
    by_cases h : k % (2 * q + 1) = c
    · simp only [Y, if_pos h, X, Set.mem_Icc]
      exact ⟨le_min (Nat.cast_nonneg _) (Nat.cast_nonneg T), min_le_right _ _⟩
    · simp only [Y, if_neg h, Set.mem_Icc]
      exact ⟨le_rfl, Nat.cast_nonneg T⟩
  have hB (c : ℕ) : HasSubgaussianMGF (B c) ((S.card : ℝ≥0) * (‖(T : ℝ)‖₊ / 2) ^ 2) sequenceLaw :=
    bounded_independent_sum_subGaussian sequenceLaw S
      (independent_colored_window_counts n q c T g N) (fun k ↦ (hY c k).aemeasurable)
      (fun k _ ↦ hbound c k)
  have h := subGaussian_block_sum_probability sequenceLaw (Finset.range (2 * q + 1)) (fun c _ ↦ hB c) ht
  have heq (ε : ℕ → ℝ) : (∑ c ∈ Finset.range (2 * q + 1), B c ε) =
      ∑ k ∈ S, (X k ε - ∫ ζ, X k ζ ∂sequenceLaw) :=
    centered_residue_sum sequenceLaw (2 * q + 1) (by omega) S X ε
  simp_rw [heq] at h
  simpa only [X, Finset.card_range, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg T : (0 : ℝ) ≤ T),
    ← mul_assoc] using h

end Erdos521
