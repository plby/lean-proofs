import ErdosProblems.Erdos421.MeanValueRootScale

/-! # Passing the complete-system recurrence to real power bounds -/

namespace Erdos421

theorem root_scale_mixed_power_le {x m : ℝ} {k a : ℕ} {e : ℝ}
    (hx : 0 < x) (hm : 0 < m) (ha : e ≤ a)
    (hscale : m ≤ 2 * x ^ ((k : ℝ)⁻¹)) :
    x ^ k * m ^ a * (2 * x / m) ^ e ≤
      2 ^ a * x ^ ((k : ℝ) + e + ((a : ℝ) - e) * (k : ℝ)⁻¹) := by
  have hsplit : x ^ k * m ^ a * (2 * x / m) ^ e =
      (2 : ℝ) ^ e * x ^ ((k : ℝ) + e) * m ^ ((a : ℝ) - e) := by
    rw [Real.div_rpow (by positivity) hm.le, Real.mul_rpow (by norm_num) hx.le,
      Real.rpow_add hx, Real.rpow_sub hm, Real.rpow_natCast, Real.rpow_natCast]
    ring
  rw [hsplit]
  calc
    _ ≤ (2 : ℝ) ^ e * x ^ ((k : ℝ) + e) *
        (2 * x ^ ((k : ℝ)⁻¹)) ^ ((a : ℝ) - e) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm.le hscale (sub_nonneg.mpr ha))
        (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx.le _),
        ← Real.rpow_mul hx.le]
      calc
        _ = ((2 : ℝ) ^ e * 2 ^ ((a : ℝ) - e)) *
            (x ^ ((k : ℝ) + e) * x ^ ((k : ℝ)⁻¹ * ((a : ℝ) - e))) := by ring
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add hx]
          simp only [add_sub_cancel, Real.rpow_natCast]
          congr 2
          ring

theorem vinogradovCount_power_step {s k N : ℕ} {A e : ℝ}
    (hk : 2 ≤ k) (hs : 0 < s)
    (hN : (4 * ((k + s) * (k + s - 1))) ^ 2 < N)
    (hkN : k ^ k ≤ N) (hA : 0 ≤ A) (he : 0 ≤ e)
    (heupper : e ≤ (2 * s + k * (k - 1) / 2 : ℕ))
    (hJ : ∀ n : ℕ, 0 < n → (vinogradovCount s k n : ℝ) ≤ A * (n : ℝ) ^ e) :
    (vinogradovCount (k + s) k N : ℝ) ≤
      (4 * k ^ 3 * k.factorial : ℕ) *
        (2 : ℝ) ^ ((2 * k ^ 3 + 1) * (2 * s + k * (k - 1) / 2)) * A *
        (N : ℝ) ^ ((k : ℝ) + e +
          (((2 * s + k * (k - 1) / 2 : ℕ) : ℝ) - e) * (k : ℝ)⁻¹) := by
  let M := meanValueRootScale k N
  let a := 2 * s + k * (k - 1) / 2
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hN
  have hkM : k ≤ M := degree_le_meanValueRootScale hkpos hkN
  have hMpos : 0 < M := hkpos.trans_le hkM
  have hMN : M ≤ N := meanValueRootScale_le_endpoint hkpos hNpos
  have hrec := vinogradovCount_scale_recurrence s k N M (by omega) hkpos hs hN
    (by omega) hkM (endpoint_le_meanValueRootScale_pow hkpos N)
  have hrecR : (vinogradovCount (k + s) k N : ℝ) ≤
      (4 * k ^ 3 * k.factorial : ℕ) * (N : ℝ) ^ k *
        ((2 : ℝ) ^ (2 * k ^ 3) * M) ^ a *
          (vinogradovCount s k (N / M + 1) : ℝ) := by exact_mod_cast hrec
  have htail : (vinogradovCount s k (N / M + 1) : ℝ) ≤
      A * (2 * (N : ℝ) / M) ^ e :=
    (hJ (N / M + 1) (Nat.succ_pos _)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (quotient_add_one_real_le hMpos hMN) he) hA)
  have hpower := root_scale_mixed_power_le (Nat.cast_pos.mpr hNpos)
    (Nat.cast_pos.mpr hMpos) heupper (meanValueRootScale_upper k hNpos)
  calc
    _ ≤ (4 * k ^ 3 * k.factorial : ℕ) * (N : ℝ) ^ k *
        ((2 : ℝ) ^ (2 * k ^ 3) * M) ^ a * (A * (2 * (N : ℝ) / M) ^ e) :=
      hrecR.trans (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = ((4 * k ^ 3 * k.factorial : ℕ) * (2 : ℝ) ^ ((2 * k ^ 3) * a) * A) *
        ((N : ℝ) ^ k * (M : ℝ) ^ a * (2 * (N : ℝ) / M) ^ e) := by
      rw [mul_pow, ← pow_mul]
      ring
    _ ≤ ((4 * k ^ 3 * k.factorial : ℕ) * (2 : ℝ) ^ ((2 * k ^ 3) * a) * A) *
        (2 ^ a * (N : ℝ) ^ ((k : ℝ) + e + ((a : ℝ) - e) * (k : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by
      rw [show (2 * k ^ 3 + 1) * a = (2 * k ^ 3) * a + a by ring, pow_add]
      ring

end Erdos421
