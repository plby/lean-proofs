import ErdosProblems.Erdos421.MeanValueRootScale

/-! # An integer short-shift length at the logarithmic Taylor scale -/

namespace Erdos421

noncomputable def logarithmicShiftRoot (k : ℕ) (A T : ℝ) : ℝ :=
  (A ^ (k + 1) / T) ^ (((k + 1 : ℕ) : ℝ)⁻¹)

noncomputable def logarithmicShiftLength (k : ℕ) (A T : ℝ) : ℕ :=
  ⌊logarithmicShiftRoot k A T⌋₊

theorem logarithmicShiftRoot_pos (k : ℕ) {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    0 < logarithmicShiftRoot k A T := by
  unfold logarithmicShiftRoot
  positivity

theorem logarithmicShiftRoot_pow (k : ℕ) {A T : ℝ} (hA : 0 ≤ A) (hT : 0 < T) :
    logarithmicShiftRoot k A T ^ (k + 1) = A ^ (k + 1) / T :=
  Real.rpow_inv_natCast_pow (by positivity) (Nat.succ_ne_zero k)

theorem one_le_logarithmicShiftRoot (k : ℕ) {A T : ℝ}
    (hA : 1 ≤ A) (hT : 0 < T) (hTA : T ≤ A ^ k) :
    1 ≤ logarithmicShiftRoot k A T := by
  apply Real.one_le_rpow _ (by positivity)
  apply (one_le_div hT).mpr
  exact hTA.trans (pow_le_pow_right₀ hA (Nat.le_succ k))

theorem logarithmicShiftLength_pos (k : ℕ) {A T : ℝ}
    (hA : 1 ≤ A) (hT : 0 < T) (hTA : T ≤ A ^ k) :
    0 < logarithmicShiftLength k A T :=
  Nat.floor_pos.mpr (one_le_logarithmicShiftRoot k hA hT hTA)

theorem logarithmicShiftLength_le_root (k : ℕ) {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    (logarithmicShiftLength k A T : ℝ) ≤ logarithmicShiftRoot k A T :=
  Nat.floor_le (logarithmicShiftRoot_pos k hA hT).le

theorem logarithmicShiftRoot_le_two_length (k : ℕ) {A T : ℝ}
    (hA : 1 ≤ A) (hT : 0 < T) (hTA : T ≤ A ^ k) :
    logarithmicShiftRoot k A T ≤ 2 * (logarithmicShiftLength k A T : ℝ) := by
  have h := Nat.div_two_lt_floor (one_le_logarithmicShiftRoot k hA hT hTA)
  change logarithmicShiftRoot k A T / 2 < (logarithmicShiftLength k A T : ℝ) at h
  linarith

theorem logarithmicShiftLength_scale_upper (k : ℕ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) :
    T * (logarithmicShiftLength k A T : ℝ) ^ (k + 1) ≤ A ^ (k + 1) := by
  have h := pow_le_pow_left₀ (Nat.cast_nonneg _) (logarithmicShiftLength_le_root k hA hT) (k + 1)
  rw [logarithmicShiftRoot_pow k hA.le hT] at h
  have h' := (le_div_iff₀ hT).mp h
  simpa only [mul_comm] using h'

theorem logarithmicShiftLength_scale_lower (k : ℕ) {A T : ℝ}
    (hA : 1 ≤ A) (hT : 0 < T) (hTA : T ≤ A ^ k) :
    A ^ (k + 1) ≤ T * (2 * (logarithmicShiftLength k A T : ℝ)) ^ (k + 1) := by
  have h := pow_le_pow_left₀ (zero_le_one.trans (one_le_logarithmicShiftRoot k hA hT hTA))
    (logarithmicShiftRoot_le_two_length k hA hT hTA) (k + 1)
  rw [logarithmicShiftRoot_pow k (by linarith) hT] at h
  have h' := (div_le_iff₀ hT).mp h
  simpa only [mul_comm] using h'

theorem logarithmicShiftRoot_le_power {k : ℕ} (hk : 0 < k) {A T : ℝ}
    (hA : 1 ≤ A) (hT : 0 < T) (hAT : A ^ (k - 1) ≤ T) :
    logarithmicShiftRoot k A T ≤ A ^ (2 / ((k + 1 : ℕ) : ℝ)) := by
  have hAp : 0 < A := by linarith
  have hpow : A ^ (k + 1) = A ^ 2 * A ^ (k - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hdiv : A ^ (k + 1) / T ≤ A ^ 2 := by
    apply (div_le_iff₀ hT).mpr
    rw [hpow]
    exact mul_le_mul_of_nonneg_left hAT (sq_nonneg A)
  calc
    _ ≤ (A ^ 2) ^ (((k + 1 : ℕ) : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hdiv (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast A 2, ← Real.rpow_mul hAp.le]
      norm_num only [Nat.cast_ofNat, div_eq_mul_inv]

theorem logarithmicShiftLength_le_power {k : ℕ} (hk : 0 < k) {A T : ℝ}
    (hA : 1 ≤ A) (hT : 0 < T) (hAT : A ^ (k - 1) ≤ T) :
    (logarithmicShiftLength k A T : ℝ) ≤ A ^ (2 / ((k + 1 : ℕ) : ℝ)) :=
  (logarithmicShiftLength_le_root k (by linarith) hT).trans
    (logarithmicShiftRoot_le_power hk hA hT hAT)

end Erdos421
