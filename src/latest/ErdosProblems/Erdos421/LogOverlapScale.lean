import ErdosProblems.Erdos421.LogMeanValueBound

/-! # Bounding the logarithmic box multiplicity at the chosen short scale -/

namespace Erdos421

theorem logarithmic_overlap_factor_le {k M N : ℕ} (hk : 0 < k) (hM : 0 < M)
    {A t : ℝ} (hA : 0 < A) (ht : t ≠ 0) (hNA : (N : ℝ) ≤ A)
    (hscale : A ^ (k + 1) ≤ |t| * (2 * (M : ℝ)) ^ (k + 1)) :
    1 + 2 * (A + N) ^ (k + 1) / ((k : ℝ) ^ 2 * |t| * (M : ℝ) ^ k) ≤
      (2 : ℝ) ^ (2 * k + 4) * M := by
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hksq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkR
  have hpower : (A + N) ^ (k + 1) ≤
      (2 : ℝ) ^ (k + 1) * (|t| * (2 * (M : ℝ)) ^ (k + 1)) := by
    calc
      _ ≤ (2 * A) ^ (k + 1) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (2 : ℝ) ^ (k + 1) * A ^ (k + 1) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)
  have hratio : 2 * (A + N) ^ (k + 1) / ((k : ℝ) ^ 2 * |t| * (M : ℝ) ^ k) ≤
      (2 : ℝ) ^ (2 * k + 3) * M := by
    calc
      _ ≤ 2 * (A + N) ^ (k + 1) / (|t| * (M : ℝ) ^ k) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have h := le_mul_of_one_le_left (by positivity : 0 ≤ |t| * (M : ℝ) ^ k) hksq
        simpa only [mul_assoc] using h
      _ ≤ (2 * ((2 : ℝ) ^ (k + 1) * (|t| * (2 * (M : ℝ)) ^ (k + 1)))) /
          (|t| * (M : ℝ) ^ k) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpower (by norm_num)) (by positivity)
      _ = _ := by
        have htwoPower : (2 : ℝ) ^ (2 * k + 3) = (2 : ℝ) ^ k * (2 : ℝ) ^ k * 8 := by
          rw [show 2 * k + 3 = (k + k) + 3 by omega, pow_add, pow_add]
          norm_num
        rw [htwoPower]
        simp only [mul_pow, pow_succ]
        field_simp
        ring
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * k + 3) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ (M : ℝ) + (2 : ℝ) ^ (2 * k + 3) * M := add_le_add hMR hratio
    _ ≤ (2 : ℝ) ^ (2 * k + 3) * M + (2 : ℝ) ^ (2 * k + 3) * M :=
      add_le_add (le_mul_of_one_le_left hMp.le htwo) le_rfl
    _ = _ := by
      rw [show 2 * k + 4 = (2 * k + 3) + 1 by omega, pow_succ (2 : ℝ) (2 * k + 3)]
      ring

end Erdos421
