import ErdosProblems.Erdos380.IntervalBandSieve

/-! # Choosing the integer order of the sieve without losing a fixed fraction -/

namespace Erdos380

theorem exists_sieve_order {p M : ℕ} (hp : 256 ≤ p)
    (hM : (2 * p) ^ 20 ≤ M) (hsize : 10 * Real.log (M : ℝ) ≤ p) :
    ∃ k : ℕ, 0 < k ∧ (2 * p) ^ (2 * k) ≤ M ∧
      20 * (k : ℝ) * Real.log p ≤ p ∧
      (2 / 5 : ℝ) * Real.log M / Real.log p ≤ k ∧
      (k : ℝ) ≤ Real.log M / (2 * Real.log (2 * p : ℕ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hMpos : 0 < M := lt_of_lt_of_le (pow_pos (by omega : 0 < 2 * p) 20) hM
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hlogq : 0 < Real.log (2 * p : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p))
  have hlogpq : Real.log (p : ℝ) ≤ Real.log (2 * p : ℕ) :=
    Real.log_le_log hpR (by exact_mod_cast (by omega : p ≤ 2 * p))
  have hlogqp : Real.log (2 * p : ℕ) ≤ (9 / 8 : ℝ) * Real.log p := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 256)
      (show (256 : ℝ) ≤ p by exact_mod_cast hp)
    have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    rw [h256] at h
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hpR.ne']
    linarith
  have hlogM : 20 * Real.log (2 * p : ℕ) ≤ Real.log (M : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 * p : ℕ) : ℝ) ^ 20)
      (show (((2 * p : ℕ) : ℝ) ^ 20) ≤ M by exact_mod_cast hM)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  let t := Real.log (M : ℝ) / (2 * Real.log (2 * p : ℕ))
  let k := ⌊t⌋₊
  have ht : 10 ≤ t := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have ht0 : 0 ≤ t := by linarith
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht0
  have htk : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  have hk : 0 < k := by
    have hkR : (0 : ℝ) < k := by linarith
    exact_mod_cast hkR
  have hklog : (k : ℝ) * (2 * Real.log (2 * p : ℕ)) ≤ Real.log M :=
    (le_div_iff₀ (by positivity)).mp hkt
  refine ⟨k, hk, ?_, ?_, ?_, hkt⟩
  · have hR : (((2 * p) ^ (2 * k) : ℕ) : ℝ) ≤ M := by
      apply (Real.log_le_log_iff (by exact_mod_cast (pow_pos (by omega : 0 < 2 * p) (2 * k))) hMR).mp
      rw [Nat.cast_pow, Real.log_pow]
      push_cast
      push_cast at hklog
      nlinarith
    exact_mod_cast hR
  · have h := mul_le_mul_of_nonneg_left hlogpq (show (0 : ℝ) ≤ k by positivity)
    nlinarith
  · have hktlower : (9 / 10 : ℝ) * t ≤ k := by linarith
    have hmul := mul_le_mul_of_nonneg_right hktlower (show 0 ≤ 2 * Real.log (2 * p : ℕ) by positivity)
    have hcancel : t * (2 * Real.log (2 * p : ℕ)) = Real.log M :=
      div_mul_cancel₀ _ (by positivity)
    have hcompare := mul_le_mul_of_nonneg_left hlogqp (show (0 : ℝ) ≤ k by positivity)
    apply (div_le_iff₀ hlogp).mpr
    nlinarith

theorem exists_interval_sieve_order {p N : ℕ} (hp : 256 ≤ p)
    (hN : (2 * p) ^ 24 ≤ N) (hsize : 10 * Real.log (2 * N : ℕ) ≤ p) :
    ∃ k : ℕ, 0 < k ∧ (2 * p) ^ (2 * k) ≤ 2 * N / p ^ 2 ∧
      20 * (k : ℝ) * Real.log p ≤ p ∧
      Real.log N / (3 * Real.log p) ≤ k ∧
      (k : ℝ) ≤ Real.log (2 * N : ℕ) / (2 * Real.log (2 * p : ℕ)) := by
  have hp0 : 0 < p := by omega
  have hq1 : 1 ≤ 2 * p := by omega
  have hp2q4 : p ^ 2 ≤ (2 * p) ^ 4 :=
    (Nat.pow_le_pow_left (by omega : p ≤ 2 * p) 2).trans
      (Nat.pow_le_pow_right hq1 (by decide : 2 ≤ 4))
  have hp2N : p ^ 2 ≤ N := hp2q4.trans ((Nat.pow_le_pow_right hq1 (by decide : 4 ≤ 24)).trans hN)
  let M := 2 * N / p ^ 2
  have hM : (2 * p) ^ 20 ≤ M := by
    apply (Nat.le_div_iff_mul_le (pow_pos hp0 2)).mpr
    calc
      (2 * p) ^ 20 * p ^ 2 ≤ (2 * p) ^ 20 * (2 * p) ^ 4 := Nat.mul_le_mul_left _ hp2q4
      _ = (2 * p) ^ 24 := by rw [← pow_add]
      _ ≤ N := hN
      _ ≤ 2 * N := by omega
  have hMpos : 0 < M := lt_of_lt_of_le (pow_pos (by omega : 0 < 2 * p) 20) hM
  have hNpos : 0 < N := lt_of_lt_of_le (pow_pos hp0 2) hp2N
  have hMle : M ≤ 2 * N := Nat.div_le_self _ _
  have hNM : N ≤ p ^ 2 * M := by
    have h := Nat.mod_lt (2 * N) (pow_pos hp0 2)
    have h' := Nat.mod_add_div (2 * N) (p ^ 2)
    change 2 * N % p ^ 2 + p ^ 2 * M = 2 * N at h'
    omega
  have hlogMle : Real.log (M : ℝ) ≤ Real.log (2 * N : ℕ) :=
    Real.log_le_log (by exact_mod_cast hMpos) (by exact_mod_cast hMle)
  obtain ⟨k, hk, hkpow, hkp, hklo, hkhi⟩ := exists_sieve_order hp hM (by linarith)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hlogq : 0 < Real.log (2 * p : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p))
  have hlogN : 24 * Real.log (p : ℝ) ≤ Real.log N := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (p : ℝ) ^ 24)
      (show (p : ℝ) ^ 24 ≤ N by
        exact_mod_cast (Nat.pow_le_pow_left (by omega : p ≤ 2 * p) 24).trans hN)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogNM : Real.log (N : ℝ) ≤ 2 * Real.log p + Real.log M := by
    have h := Real.log_le_log (by exact_mod_cast hNpos : (0 : ℝ) < N)
      (show (N : ℝ) ≤ (p : ℝ) ^ 2 * M by exact_mod_cast hNM)
    rw [Real.log_mul (pow_ne_zero 2 hpR.ne') (by exact_mod_cast hMpos.ne'), Real.log_pow] at h
    norm_num at h
    exact h
  refine ⟨k, hk, hkpow, hkp, ?_, hkhi.trans ?_⟩
  · have hklog := (div_le_iff₀ hlogp).mp hklo
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  · exact div_le_div_of_nonneg_right hlogMle (by positivity)

end Erdos380
