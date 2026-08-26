import ErdosProblems.Erdos421.TwoFactorLargeValueCases

/-! # Converting the four large-value cases to a common bound -/

namespace Erdos421

theorem twoFactor_numeric_saving {u w R M H T η : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hR : 0 ≤ R) (hM : 0 ≤ M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hη : 0 ≤ η) {k : ℕ} (hk : 2 ≤ k) (huM : u ≤ M) (hwH : w ≤ η ^ 2 * H)
    (hmeanM : R * u ≤ M + T) (hhalaszM : R * u ^ 3 ≤ M * u ^ 2 + M * T)
    (hmeanH : R * w ^ k ≤ H ^ k + T)
    (hhalaszH : R * w ^ (3 * k) ≤ H ^ k * w ^ (2 * k) + H ^ k * T)
    (hsizeB : T ^ (2 * k) * M ≤ (η * M * H) ^ (2 * k))
    (hsizeC : H ^ k * T ≤ (η * H) ^ (3 * k))
    (hsizeD : M * T ^ (2 * k - 2) ≤ (η * M) ^ (2 * k)) :
    u * w * R ≤ 2 * η * M * H := by
  have htarget : 0 ≤ 2 * η * M * H := by positivity
  rcases twoFactor_largeValue_four_cases hu hw hR hM hH hT hk huM
    hmeanM hhalaszM hmeanH hhalaszH with ha | hb | hc | hd
  · have hpow : (u * w * R) ^ (2 * k) ≤ (2 * η * M * H) ^ (2 * k) := by
      apply ha.trans
      have hwk := pow_le_pow_left₀ hw hwH k
      apply (mul_le_mul_of_nonneg_left hwk (by positivity : 0 ≤ (2 * M) ^ (2 * k) * H ^ k)).trans_eq
      simp only [mul_pow, ← pow_mul]
      ring
    exact le_of_pow_le_pow_left₀ (by omega : 2 * k ≠ 0) htarget hpow
  · have hpow : (u * w * R) ^ (2 * k) ≤ (2 * η * M * H) ^ (2 * k) := by
      apply hb.trans
      calc
        _ = 2 ^ (2 * k) * (T ^ (2 * k) * M) := by rw [mul_pow]; ring
        _ ≤ 2 ^ (2 * k) * (η * M * H) ^ (2 * k) :=
          mul_le_mul_of_nonneg_left hsizeB (by positivity)
        _ = _ := by rw [← mul_pow]; congr 1; ring
    exact le_of_pow_le_pow_left₀ (by omega : 2 * k ≠ 0) htarget hpow
  · have hpow : (u * w * R) ^ (3 * k) ≤ (2 * η * M * H) ^ (3 * k) := by
      apply hc.trans
      calc
        _ = (2 * M) ^ (3 * k) * (H ^ k * T) := by ring
        _ ≤ (2 * M) ^ (3 * k) * (η * H) ^ (3 * k) :=
          mul_le_mul_of_nonneg_left hsizeC (by positivity)
        _ = _ := by rw [← mul_pow]; congr 1; ring
    exact le_of_pow_le_pow_left₀ (by omega : 3 * k ≠ 0) htarget hpow
  · have hpow : (u * w * R) ^ (2 * k) ≤ (2 * η * M * H) ^ (2 * k) := by
      apply hd.trans
      calc
        _ = (2 * H) ^ (2 * k) * (M * T ^ (2 * k - 2)) := by rw [mul_pow]; ring
        _ ≤ (2 * H) ^ (2 * k) * (η * M) ^ (2 * k) :=
          mul_le_mul_of_nonneg_left hsizeD (by positivity)
        _ = _ := by rw [← mul_pow]; congr 1; ring
    exact le_of_pow_le_pow_left₀ (by omega : 2 * k ≠ 0) htarget hpow

end Erdos421
