import ErdosProblems.Erdos4.FGKMTPropagation

/-!
# An explicit finite iteration budget

All exponents are natural numbers. Choosing the initial sparsity below
`τ^(4*8^m)` gives a valid `m`-round budget with final error `τ^4`.
-/

namespace Erdos4.FGKMT

noncomputable def iterationThreshold (τ : ℝ) (m j : ℕ) : ℝ := τ ^ (8 ^ (m - j))

noncomputable def iterationError (τ : ℝ) (m j : ℕ) : ℝ := τ ^ (4 * 8 ^ (m - j))

theorem iterationError_eq_fourth (τ : ℝ) (m j : ℕ) :
    iterationError τ m j = iterationThreshold τ m j ^ 4 := by
  unfold iterationError iterationThreshold
  rw [Nat.mul_comm 4, pow_mul]

theorem iterationThreshold_pos {τ : ℝ} (hτ : 0 < τ) (m j : ℕ) :
    0 < iterationThreshold τ m j := pow_pos hτ _

theorem iterationThreshold_le {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (m j : ℕ) :
    iterationThreshold τ m j ≤ τ := by
  have hexp : 1 ≤ 8 ^ (m - j) := Nat.one_le_pow _ _ (by decide)
  unfold iterationThreshold
  simpa only [pow_one] using pow_le_pow_of_le_one hτ0 hτ1 hexp

theorem iterationError_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (m j : ℕ) :
    0 ≤ iterationError τ m j := pow_nonneg hτ _

theorem iterationError_le {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (m j : ℕ) :
    iterationError τ m j ≤ τ := by
  have hp : 1 ≤ 8 ^ (m - j) := Nat.one_le_pow _ _ (by decide)
  have hexp : 1 ≤ 4 * 8 ^ (m - j) := by omega
  unfold iterationError
  simpa only [pow_one] using pow_le_pow_of_le_one hτ0 hτ1 hexp

theorem iterationError_mono {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (m : ℕ)
    {i j : ℕ} (hij : i ≤ j) : iterationError τ m i ≤ iterationError τ m j := by
  have he : m - j ≤ m - i := Nat.sub_le_sub_left hij m
  have hp : 8 ^ (m - j) ≤ 8 ^ (m - i) := Nat.pow_le_pow_right (by decide) he
  exact pow_le_pow_of_le_one hτ0 hτ1 (Nat.mul_le_mul_left 4 hp)

theorem iterationThreshold_eq_next_sq (τ : ℝ) (m j : ℕ) (hj : j < m) :
    iterationThreshold τ m j = iterationError τ m (j + 1) ^ 2 := by
  have he : m - j = (m - (j + 1)) + 1 := by omega
  unfold iterationThreshold iterationError
  rw [he, pow_succ, ← pow_mul]
  congr 1
  omega

theorem iterationBudget_step (r A m : ℕ) {κ δ D τ : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hsmall : propagationCoefficient r A κ D * τ ≤ 1)
    (hδsmall : δ ≤ τ ^ (4 * 8 ^ m)) {j : ℕ} (hj : j < m) :
    roundNextError r A κ δ (iterationError τ m j) (iterationThreshold τ m j) D ≤
      iterationError τ m (j + 1) := by
  have hτle : τ ≤ 1 := by linarith
  have hq0 := iterationThreshold_pos hτ0 m j
  have hq1 := (iterationThreshold_le hτ0.le hτle m j).trans hτ1
  have heq := iterationError_eq_fourth τ m j
  have hδq : δ ≤ iterationThreshold τ m j ^ 4 := by
    rw [← heq]
    apply hδsmall.trans
    have hh := iterationError_mono hτ0.le hτle m (Nat.zero_le j)
    simpa [iterationError] using hh
  have hprop := roundNextError_fourth r A hκ hδ (iterationError_nonneg hτ0.le m j) hD
    hq0 hq1 heq.le hδq
  apply hprop.trans
  rw [iterationThreshold_eq_next_sq τ m j hj]
  have hH0 : 0 ≤ propagationCoefficient r A κ D :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (propagationCoefficient_ge_one r A hκ hD)
  have he := iterationError_le hτ0.le hτle m (j + 1)
  have hprod : propagationCoefficient r A κ D * iterationError τ m (j + 1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left he hH0).trans hsmall
  have hnonneg := iterationError_nonneg hτ0.le m (j + 1)
  have hh := mul_le_mul_of_nonneg_right hprod hnonneg
  nlinarith

end Erdos4.FGKMT
