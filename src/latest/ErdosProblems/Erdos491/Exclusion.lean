import ErdosProblems.Erdos491.Growth

/-! # Low-slope primes exclude high-slope affine divisors -/

namespace Erdos491

theorem exclude_affine_divisor {h : ℕ → ℝ} (hh : PosCompletelyAdditive h)
    (hnonneg : ∀ n : ℕ, 0 < n → 0 ≤ h n)
    {K C b : ℝ} (hC : 0 ≤ C) (hb : 0 < b)
    (hgap : ∀ n : ℕ, 0 < n → |h (n + 1) - h n| ≤ K)
    (hgrowth : ∀ n : ℕ, 0 < n → |h n| ≤ C * Real.log (n : ℝ))
    {k L X p q u : ℕ} (hL : 0 < L) (hX : 2 ≤ X)
    (hCk : C < b * k / 4)
    (hbig : b / 8 * Real.log (L : ℝ) + K < b * k / 4 * Real.log (X : ℝ))
    (hp : 0 < p) (hpL : p ≤ L * (X ^ k) ^ 4)
    (hplow : h p < b / 8 * Real.log (p : ℝ))
    (hq : 0 < q) (hqX : X ^ k ≤ q) (hqhigh : b * Real.log (q : ℝ) < h q)
    (hu : 0 < u) (huX : u ≤ X) : ¬ q ∣ p * u + 1 := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hlogp : Real.log (p : ℝ) ≤
      Real.log (L : ℝ) + 4 * (k : ℝ) * Real.log (X : ℝ) := by
    have h := Real.log_le_log (by exact_mod_cast hp)
      (show (p : ℝ) ≤ ((L * (X ^ k) ^ 4 : ℕ) : ℝ) by exact_mod_cast hpL)
    push_cast at h
    rw [Real.log_mul (by exact_mod_cast hL.ne') (by positivity), Real.log_pow,
      Real.log_pow] at h
    norm_num at h
    nlinarith
  have hlogu : Real.log (u : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast hu) (by exact_mod_cast huX)
  have hlogq : (k : ℝ) * Real.log (X : ℝ) ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((X ^ k : ℕ) : ℝ))
      (show ((X ^ k : ℕ) : ℝ) ≤ (q : ℝ) by exact_mod_cast hqX)
    simpa only [Nat.cast_pow, Real.log_pow] using h
  have hstep := (abs_le.mp (hgap (p * u) (Nat.mul_pos hp hu))).2
  rw [hh hp hu] at hstep
  have huval : h u ≤ C * Real.log (X : ℝ) :=
    ((le_abs_self _).trans (hgrowth u hu)).trans (mul_le_mul_of_nonneg_left hlogu hC)
  have hpval : h p ≤ b / 8 *
      (Real.log (L : ℝ) + 4 * (k : ℝ) * Real.log (X : ℝ)) :=
    hplow.le.trans (mul_le_mul_of_nonneg_left hlogp (by positivity))
  have hCmul := mul_lt_mul_of_pos_right hCk hlogX
  have hsmall : h (p * u + 1) < b * ((k : ℝ) * Real.log (X : ℝ)) := by
    nlinarith
  have hhigh : b * ((k : ℝ) * Real.log (X : ℝ)) < h q :=
    (mul_le_mul_of_nonneg_left hlogq hb.le).trans_lt hqhigh
  intro hdvd
  have hdiv := hh.le_of_dvd hnonneg hq (by omega : 0 < p * u + 1) hdvd
  linarith

end Erdos491
