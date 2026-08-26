import ErdosProblems.Erdos421.LogDifferenceUniform

/-! # Iterating finite differencing with an explicit terminal estimate -/

namespace Erdos421

noncomputable def differenceRootBound (M H : ℕ) (B : ℝ) : ℕ → ℝ
  | 0 => B
  | k + 1 => Real.sqrt (2 * (M : ℝ) ^ 2 / H + 2 * M * differenceRootBound M H B k)

theorem differenceRootBound_nonneg (M H : ℕ) {B : ℝ} (hB : 0 ≤ B) (k : ℕ) :
    0 ≤ differenceRootBound M H B k := by
  cases k with
  | zero => exact hB
  | succ k => exact Real.sqrt_nonneg _

theorem iteratedLogarithmic_sum_iterated_bound {M N H : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (hH : 0 < H) (hHM : H ≤ M)
    (r k : ℕ) (hs : List ℝ) (hlen : hs.length + k = r)
    (hhs : ∀ h ∈ hs, 1 ≤ h ∧ h ≤ H) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ‖∑ n ∈ Finset.range N, oscillatoryPhase 1 (iteratedLogarithmicPhase M hs τ n)‖ ≤
      differenceRootBound M H (logDifferenceLeafBound M H r τ δ) k := by
  induction k generalizing hs N with
  | zero =>
    exact iteratedLogarithmic_sum_uniform_bound hM hN hs (by omega) hhs hτ hδ
  | succ k ih =>
    have hB : 0 ≤ differenceRootBound M H (logDifferenceLeafBound M H r τ δ) k :=
      differenceRootBound_nonneg M H (logDifferenceLeafBound_nonneg M H r hτ.le hδ.le) k
    have hcorr : ∀ h, 0 < h → h < H →
        ‖finiteCorrelation (fun n ↦ oscillatoryPhase 1 (iteratedLogarithmicPhase M hs τ n)) N h‖ ≤
          differenceRootBound M H (logDifferenceLeafBound M H r τ δ) k := by
      intro h hh hhH
      rw [iteratedLogarithmic_finiteCorrelation_eq]
      have hnew : ∀ a ∈ (h : ℝ) :: hs, 1 ≤ a ∧ a ≤ H := by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · constructor
          · exact_mod_cast hh
          · exact_mod_cast hhH.le
        · exact hhs a ha
      exact ih (N := N - h) (hN := (Nat.sub_le N h).trans hN)
        (hs := (h : ℝ) :: hs) (hlen := by simp only [List.length_cons]; omega) (hhs := hnew)
    have hb := vanDerCorput_uniform_length_bound
      (fun n ↦ oscillatoryPhase 1 (iteratedLogarithmicPhase M hs τ n)) hH hN hHM hB
      (fun n _ ↦ by simp) hcorr
    exact Real.le_sqrt_of_sq_le hb

/-- A fully explicit arbitrary-order estimate for the original logarithmic
sum. All terminal phase estimates and all differencing steps are proved. -/
theorem logarithmicSum_iterated_difference_bound {M N H : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (hH : 0 < H) (hHM : H ≤ M)
    (r : ℕ) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ‖logarithmicSum M N τ‖ ≤
      differenceRootBound M H (logDifferenceLeafBound M H r τ δ) r := by
  have h := iteratedLogarithmic_sum_iterated_bound hM hN hH hHM r r [] (by simp) (by simp) hτ hδ
  rw [logarithmicSum_eq_phase_sum]
  simpa only [iteratedLogarithmicPhase, iteratedDifference] using h

end Erdos421
