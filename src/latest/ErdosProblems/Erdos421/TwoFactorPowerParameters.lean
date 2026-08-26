import ErdosProblems.Erdos421.TwoFactorExponentArithmetic
import ErdosProblems.Erdos421.TwoFactorNumericSaving

/-! # Numerical size conditions from polynomial factor and time ranges -/

namespace Erdos421

theorem twoFactor_size_b {X M H T η e d : ℝ} (hX : 1 ≤ X) (hM : 0 ≤ M)
    (hMX : M ≤ X) (hprod : M * H = X) (hT : 0 ≤ T)
    (hThi : T ≤ X ^ (9 / 10 - e)) (hη : X ^ (-d) ≤ η)
    (he : 0 ≤ e) (hd : d ≤ e / 2) {k : ℕ} (hk : 5 ≤ k) :
    T ^ (2 * k) * M ≤ (η * M * H) ^ (2 * k) := by
  have hXp : 0 < X := by linarith
  have hkr : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hηX : X ^ (1 - d) ≤ η * X := by
    calc
      _ = X ^ (-d) * X := by rw [sub_eq_add_neg, Real.rpow_add hXp, Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hη hXp.le
  calc
    _ ≤ (X ^ (9 / 10 - e)) ^ (2 * k) * X :=
      mul_le_mul (pow_le_pow_left₀ hT hThi _) hMX hM (by positivity)
    _ = X ^ ((2 * k : ℕ) * (9 / 10 - e) + 1) := by
      rw [← Real.rpow_mul_natCast hXp.le, Real.rpow_add hXp, Real.rpow_one]
      congr 2
      ring
    _ ≤ X ^ ((1 - d) * (2 * k : ℕ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hX
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using twoFactor_exponent_b hkr he hd
    _ = (X ^ (1 - d)) ^ (2 * k) := Real.rpow_mul_natCast hXp.le _ _
    _ ≤ (η * X) ^ (2 * k) := pow_le_pow_left₀ (by positivity) hηX _
    _ = _ := by rw [mul_assoc η M H, hprod]

theorem twoFactor_size_c {X H T η e d : ℝ} (hX : 1 ≤ X) (hH : 0 ≤ H)
    (hThi : T ≤ X ^ (9 / 10 - e)) (hη : X ^ (-d) ≤ η) (he : 0 ≤ e)
    {k : ℕ} (hk : 1 ≤ k) (hd : d ≤ 1 / (60 * k))
    (hHlo : X ^ (1 / ((k : ℝ) + 1)) ≤ H) :
    H ^ k * T ≤ (η * H) ^ (3 * k) := by
  have hXp : 0 < X := by linarith
  have hηp : 0 < η := (Real.rpow_pos_of_pos hXp _).trans_le hη
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hHpow : X ≤ H ^ (2 * k) := by
    calc
      X = X ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ X ^ ((1 / ((k : ℝ) + 1)) * (2 * k)) :=
        Real.rpow_le_rpow_of_exponent_le hX (twoFactor_lower_length_exponent hkr)
      _ = (X ^ (1 / ((k : ℝ) + 1))) ^ (2 * k) := by
        rw [show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by push_cast; rfl,
          Real.rpow_mul_natCast hXp.le]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hHlo _
  have hTpow : T ≤ η ^ (3 * k) * H ^ (2 * k) := by
    calc
      T ≤ X ^ (9 / 10 - e) := hThi
      _ ≤ X ^ ((-d) * (3 * k) + 1) :=
        Real.rpow_le_rpow_of_exponent_le hX (twoFactor_exponent_c hkr he hd)
      _ = (X ^ (-d)) ^ (3 * k) * X := by
        rw [Real.rpow_add hXp, Real.rpow_one,
          show (3 : ℝ) * k = ((3 * k : ℕ) : ℝ) by push_cast; rfl,
          Real.rpow_mul_natCast hXp.le]
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (by positivity) hη _) hHpow hXp.le (by positivity)
  calc
    _ ≤ H ^ k * (η ^ (3 * k) * H ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left hTpow (pow_nonneg hH _)
    _ = _ := by
      rw [mul_pow, show 3 * k = k + 2 * k by omega, pow_add H]
      ring

theorem twoFactor_cofactor_lower {X M H : ℝ} (hX : 1 ≤ X) (hM : 0 ≤ M)
    (hprod : M * H = X) {k : ℕ} (hHhi : H ≤ X ^ (1 / (k : ℝ))) :
    X ^ (1 - 1 / (k : ℝ)) ≤ M := by
  have hXp : 0 < X := by linarith
  have hp : 0 < X ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hXp _
  have hb : X / X ^ (1 / (k : ℝ)) ≤ M := by
    apply (div_le_iff₀ hp).mpr
    calc
      X = M * H := hprod.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hHhi hM
  have he : X / X ^ (1 / (k : ℝ)) = X ^ (1 - 1 / (k : ℝ)) := by
    rw [Real.rpow_sub hXp, Real.rpow_one]
  rwa [he] at hb

theorem twoFactor_size_d {X M T η e d : ℝ} (hX : 1 ≤ X) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hThi : T ≤ X ^ (9 / 10 - e)) (hη : X ^ (-d) ≤ η) (he : 0 ≤ e) (hd : d ≤ e / 2)
    {k : ℕ} (hk : 5 ≤ k) (hMlo : X ^ (1 - 1 / (k : ℝ)) ≤ M) :
    M * T ^ (2 * k - 2) ≤ (η * M) ^ (2 * k) := by
  have hXp : 0 < X := by linarith
  have hηp : 0 < η := (Real.rpow_pos_of_pos hXp _).trans_le hη
  have hkr : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hn2 : ((2 * k - 2 : ℕ) : ℝ) = 2 * k - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]
    norm_num
  have hn1 : ((2 * k - 1 : ℕ) : ℝ) = 2 * k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have ht : T ^ (2 * k - 2) ≤ η ^ (2 * k) * M ^ (2 * k - 1) := by
    calc
      _ ≤ (X ^ (9 / 10 - e)) ^ (2 * k - 2) := pow_le_pow_left₀ hT hThi _
      _ = X ^ ((9 / 10 - e) * (2 * k - 2)) := by
        rw [← Real.rpow_mul_natCast hXp.le, hn2]
      _ ≤ X ^ ((-d) * (2 * k) + (1 - 1 / (k : ℝ)) * (2 * k - 1)) :=
        Real.rpow_le_rpow_of_exponent_le hX (twoFactor_exponent_d hkr he hd)
      _ = (X ^ (-d)) ^ (2 * k) * (X ^ (1 - 1 / (k : ℝ))) ^ (2 * k - 1) := by
        rw [Real.rpow_add hXp, ← Real.rpow_mul_natCast hXp.le,
          ← Real.rpow_mul_natCast hXp.le, hn1]
        push_cast
        rfl
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (by positivity) hη _)
        (pow_le_pow_left₀ (by positivity) hMlo _) (by positivity) (by positivity)
  calc
    _ ≤ M * (η ^ (2 * k) * M ^ (2 * k - 1)) := mul_le_mul_of_nonneg_left ht hM
    _ = _ := by
      have heM : M ^ (2 * k) = M ^ (2 * k - 1) * M := by
        conv_lhs => rw [show 2 * k = (2 * k - 1) + 1 by omega, pow_succ]
      rw [mul_pow, heM]
      ring

/-- The numerical hypotheses for the four-case bound hold in the indicated
factor ranges and below time `X^(9/10-e)`. The input mean-value inequalities
are explicit in `twoFactor_numeric_saving`, not assumptions about primes. -/
theorem twoFactor_power_range_saving {X u w R M H T η e d : ℝ}
    (hX : 1 ≤ X) (hu : 0 ≤ u) (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hT : 0 ≤ T) (hprod : M * H = X)
    {k : ℕ} (hk : 5 ≤ k) (he : 0 ≤ e) (hd : d ≤ e / 2) (hd' : d ≤ 1 / (60 * k))
    (hHlo : X ^ (1 / ((k : ℝ) + 1)) ≤ H) (hHhi : H ≤ X ^ (1 / (k : ℝ)))
    (hThi : T ≤ X ^ (9 / 10 - e)) (hη : X ^ (-d) ≤ η)
    (huM : u ≤ M) (hwH : w ≤ η ^ 2 * H)
    (hmeanM : R * u ≤ M + T) (hhalaszM : R * u ^ 3 ≤ M * u ^ 2 + M * T)
    (hmeanH : R * w ^ k ≤ H ^ k + T)
    (hhalaszH : R * w ^ (3 * k) ≤ H ^ k * w ^ (2 * k) + H ^ k * T) :
    u * w * R ≤ 2 * η * X := by
  have hXp : 0 < X := by linarith
  have hηp : 0 < η := (Real.rpow_pos_of_pos hXp _).trans_le hη
  have hH1 : 1 ≤ H :=
    (Real.one_le_rpow hX (by positivity : 0 ≤ 1 / ((k : ℝ) + 1))).trans hHlo
  have hMX : M ≤ X := by nlinarith
  have hMlo := twoFactor_cofactor_lower hX hM hprod hHhi
  have hB := twoFactor_size_b hX hM hMX hprod hT hThi hη he hd hk
  have hC := twoFactor_size_c hX hH hThi hη he (by omega : 1 ≤ k) hd' hHlo
  have hD := twoFactor_size_d hX hM hT hThi hη he hd hk hMlo
  have hb := twoFactor_numeric_saving hu hw hR hM hH hT hηp.le (by omega : 2 ≤ k)
    huM hwH hmeanM hhalaszM hmeanH hhalaszH hB hC hD
  simpa only [mul_assoc, hprod] using hb

end Erdos421
