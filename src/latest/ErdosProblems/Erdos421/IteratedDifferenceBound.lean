import ErdosProblems.Erdos421.IteratedVanDerCorput

/-! # A nonrecursive form of the arbitrary-order logarithmic-sum bound -/

namespace Erdos421

theorem differenceRootBound_normalized_sq {M H : ℕ} (hM : 0 < M) (hH : 0 < H)
    {B : ℝ} (hB : 0 ≤ B) (r : ℕ) :
    (differenceRootBound M H B (r + 1) / (4 * M)) ^ 2 =
      (1 / (H : ℝ)) / 8 + (differenceRootBound M H B r / (4 * M)) / 2 := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hb := differenceRootBound_nonneg M H hB r
  rw [differenceRootBound, div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem differenceRootBound_normalized_power {M H : ℕ} (hM : 0 < M) (hH : 0 < H)
    {B : ℝ} (hB : 0 ≤ B) (r : ℕ) :
    (differenceRootBound M H B r / (4 * M)) ^ (2 ^ r) ≤ 1 / (H : ℝ) + B / M := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have ha0 : 0 ≤ 1 / (H : ℝ) := by positivity
  have ha1 : 1 / (H : ℝ) ≤ 1 := (div_le_one hHp).mpr hH1
  have hBM : 0 ≤ B / M := by positivity
  induction r with
  | zero =>
    simp only [differenceRootBound, pow_zero, pow_one]
    have hdiv : B / (4 * M) ≤ B / M :=
      div_le_div_of_nonneg_left hB hMp (by linarith)
    linarith
  | succ r ih =>
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; ring
    rw [hpow, pow_mul, differenceRootBound_normalized_sq hM hH hB r]
    have hb0 : 0 ≤ differenceRootBound M H B r / (4 * M) := by
      have hb := differenceRootBound_nonneg M H hB r
      positivity
    have hleft0 : 0 ≤ (1 / (H : ℝ)) / 8 + (differenceRootBound M H B r / (4 * M)) / 2 := by
      positivity
    rcases le_total (1 / (H : ℝ)) (differenceRootBound M H B r / (4 * M)) with hab | hba
    · have hstep : (1 / (H : ℝ)) / 8 + (differenceRootBound M H B r / (4 * M)) / 2 ≤
          differenceRootBound M H B r / (4 * M) := by linarith
      exact (pow_le_pow_left₀ hleft0 hstep (2 ^ r)).trans ih
    · have hstep : (1 / (H : ℝ)) / 8 + (differenceRootBound M H B r / (4 * M)) / 2 ≤
          1 / (H : ℝ) := by linarith
      have hp : (1 / (H : ℝ)) ^ (2 ^ r) ≤ 1 / H := by
        simpa only [pow_one] using pow_le_pow_of_le_one ha0 ha1
          (show 1 ≤ 2 ^ r from one_le_pow₀ (by norm_num))
      exact ((pow_le_pow_left₀ hleft0 hstep (2 ^ r)).trans hp).trans
        (le_add_of_nonneg_right hBM)

/-- An explicit higher-derivative estimate with no unevaluated analytic
inputs: the only free choices are the order, differencing length, and
positive phase-band parameter. -/
theorem logarithmicSum_arbitrary_order_bound {M N H : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (hH : 0 < H) (hHM : H ≤ M)
    (r : ℕ) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    (‖logarithmicSum M N τ‖ / (4 * M)) ^ (2 ^ r) ≤
      1 / (H : ℝ) + logDifferenceLeafBound M H r τ δ / M := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hb := logarithmicSum_iterated_difference_bound hM hN hH hHM r hτ hδ
  have hdiv := div_le_div_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ 4 * M)
  exact (pow_le_pow_left₀ (by positivity) hdiv (2 ^ r)).trans
    (differenceRootBound_normalized_power hM hH (logDifferenceLeafBound_nonneg M H r hτ.le hδ.le) r)

end Erdos421
