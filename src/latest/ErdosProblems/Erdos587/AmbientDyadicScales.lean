import ErdosProblems.Erdos587.DyadicSurplus

/-! Compare the dyadic construction with the final cube-root scale. -/

open Filter

namespace Erdos587

theorem ambient_dyadic_scales {N : ℕ} (hN : 0 < N) :
    let t := Nat.log 4096 N + 1
    N ≤ 2 ^ (12 * t) ∧
      2 ^ (4 * t) ≤ 16 * 4 ^ Nat.log 64 N ∧
      12 * t + 1 ≤ 13 * (Nat.log 2 N + 1) := by
  intro t
  have hpow := Nat.pow_log_le_self 4096 (by omega : N ≠ 0)
  have hambient := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4096) N
  have htwo : 2 ^ Nat.log 4096 N ≤ N :=
    (Nat.pow_le_pow_left (by omega : 2 ≤ 4096) _).trans hpow
  have hlogtwo := Nat.le_log_of_pow_le (by omega : 1 < 2) htwo
  have hsixtyfour : 64 ^ (2 * Nat.log 4096 N) ≤ N := by
    rw [pow_mul]
    norm_num only [show (64 : ℕ) ^ 2 = 4096 by norm_num]
    exact hpow
  have hlog64 := Nat.le_log_of_pow_le (by omega : 1 < 64) hsixtyfour
  refine ⟨?_, ?_, by dsimp [t]; omega⟩
  · have heq : 4096 ^ (Nat.log 4096 N + 1) = 2 ^ (12 * t) := by
      rw [pow_mul]
      norm_num only [show (2 : ℕ) ^ 12 = 4096 by norm_num]
      rfl
    exact hambient.le.trans_eq heq
  · calc
      2 ^ (4 * t) = 16 * 4 ^ (2 * Nat.log 4096 N) := by
        dsimp [t]
        rw [show 4 * (Nat.log 4096 N + 1) = 4 + 4 * Nat.log 4096 N by ring, pow_add]
        norm_num only [show (2 : ℕ) ^ 4 = 16 by norm_num]
        congr 1
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        ring
      _ ≤ 16 * 4 ^ Nat.log 64 N :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hlog64)

theorem tendsto_ambient_dyadic_scale :
    Tendsto (fun N : ℕ => Nat.log 4096 N + 1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (4096 ^ b)] with N hN
  have := Nat.le_log_of_pow_le (by norm_num : 1 < 4096) hN
  omega

theorem ambient_dyadic_threshold_upper (Z d e₀ N : ℕ) (hN : 0 < N) :
    let t := Nat.log 4096 N + 1
    let l := 12 * t + 1
    let e := e₀ + d * (Nat.log 2 l + 1)
    Z * l ^ 2 * 2 ^ (4 * t + e) ≤
      (Z * 2 ^ (e₀ + d) * 16 * 13 ^ (d + 2)) *
        4 ^ Nat.log 64 N * (Nat.log 2 N + 1) ^ (d + 2) := by
  intro t l e
  obtain ⟨_hN, hscale, hlog⟩ := ambient_dyadic_scales hN
  calc
    _ ≤ (Z * 2 ^ (e₀ + d)) * 2 ^ (4 * t) * l ^ (d + 2) :=
      dyadic_threshold_upper Z d e₀ t
    _ ≤ (Z * 2 ^ (e₀ + d)) * (16 * 4 ^ Nat.log 64 N) *
        (13 * (Nat.log 2 N + 1)) ^ (d + 2) := by gcongr
    _ = _ := by rw [mul_pow]; ring

end Erdos587
