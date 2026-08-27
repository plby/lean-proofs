import Arxiv.Arxiv2411_18291.ColourCollisionNumerics
import Arxiv.Arxiv2411_18291.FiniteTypicalHostNumerics

/-! # Finite collision budgets for the small rainbow extension patterns -/

namespace Arxiv2411_18291

theorem colour_collision_coefficient_bound {q h m M : ℕ} (hq : 2 ≤ q)
    (hm : m ≤ (4 * q) ^ (2 * q)) (hM : M ≤ h) :
    2 * m ^ 2 * 16 ^ M ≤ (4 * q) ^ (10 * (q + h)) := by
  calc
    _ ≤ (4 * q) ^ 1 * ((4 * q) ^ (2 * q)) ^ 2 * ((4 * q) ^ 2) ^ M :=
      Nat.mul_le_mul (Nat.mul_le_mul (by simp only [pow_one]; omega)
        (Nat.pow_le_pow_left hm 2))
        (Nat.pow_le_pow_left (by nlinarith only [hq] : 16 ≤ (4 * q) ^ 2) M)
    _ = (4 * q) ^ (1 + (2 * q) * 2 + 2 * M) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem colour_collision_bound_at_exponents_paper_threshold {q r n h m M : ℕ}
    (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hm : m ≤ (4 * q) ^ (2 * q)) (hM : M ≤ h)
    {a β : ℝ} (hgap : a + 2 * β * M + paperAlpha q (r + 1) / 24 ≤ 39 / 40)
    (A p : ℝ) (hA : ((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) * (n : ℝ) ^ m ≤ A)
    (hp : (1 / 4 : ℝ) * (n : ℝ) ^ (-β) ≤ p) :
    (m : ℝ) ^ 2 * (n : ℝ) ^ (m - 1) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) * A * p ^ (2 * M) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hcNat := colour_collision_coefficient_bound (by omega : 2 ≤ q) hm hM
  have hc : (2 * m ^ 2 * 16 ^ M : ℝ) ≤
      (n : ℝ) ^ (1 - paperAlpha q (r + 1) / 24 - a - 2 * β * M) := by
    have hb : (2 * m ^ 2 * 16 ^ M : ℝ) ≤ (4 * q : ℝ) ^ (10 * (q + h)) := by
      exact_mod_cast hcNat
    exact (hb.trans (paper_host_configuration_growth hqr hn hh hH)).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hgap]))
  have hprod : (16 : ℝ) ^ M * (1 / 4 : ℝ) ^ (2 * M) = 1 := by
    rw [pow_mul, ← mul_pow]
    norm_num
  have hcoef : (2 * m ^ 2 * 16 ^ M : ℝ) * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ (2 * M)) =
      (3 / 2 : ℝ) * (m : ℝ) ^ 2 := by
    calc
      _ = (3 / 2 : ℝ) * (m : ℝ) ^ 2 * (16 ^ M * (1 / 4 : ℝ) ^ (2 * M)) := by ring
      _ = _ := by rw [hprod, mul_one]
  have hmul := mul_le_mul_of_nonneg_right hc
    (by positivity : 0 ≤ (3 / 4 : ℝ) * (1 / 4 : ℝ) ^ (2 * M))
  rw [hcoef] at hmul
  have hsmall : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) *
      ((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) * n *
        ((1 / 4 : ℝ) * (n : ℝ) ^ (-β)) ^ (2 * M) := by
    rw [colour_collision_scale hn0]
    nlinarith only [hmul, sq_nonneg (m : ℝ)]
  have hAnonneg : 0 ≤ A :=
    (by positivity : 0 ≤ ((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) * (n : ℝ) ^ m).trans hA
  have hpbase : 0 ≤ (1 / 4 : ℝ) * (n : ℝ) ^ (-β) := by positivity
  have hδ : 0 ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := Real.rpow_nonneg hn0.le _
  by_cases hm0 : m = 0
  · subst m
    have hp0 := hpbase.trans hp
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
    positivity
  · have hpow : (n : ℝ) ^ (m - 1) * n = (n : ℝ) ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    calc
      _ ≤ ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) *
          ((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) * n *
          ((1 / 4 : ℝ) * (n : ℝ) ^ (-β)) ^ (2 * M)) *
            (n : ℝ) ^ (m - 1) := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hn0.le _)
      _ = (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) *
          (((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) * (n : ℝ) ^ m) *
          ((1 / 4 : ℝ) * (n : ℝ) ^ (-β)) ^ (2 * M) := by
        rw [← hpow]
        ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hA hδ)
        (pow_le_pow_left₀ hpbase hp _) (pow_nonneg hpbase _) (mul_nonneg hδ hAnonneg)

theorem colour_collision_bound_paper_threshold {q r n h m M : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hm : m ≤ (4 * q) ^ (2 * q)) (hM : M ≤ h)
    (A p : ℝ) (hA : (3 / 4 : ℝ) * (n : ℝ) ^ m ≤ A)
    (hp : (1 / 4 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ p) :
    (m : ℝ) ^ 2 * (n : ℝ) ^ (m - 1) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) * A * p ^ (2 * M) := by
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hαM : paperAlpha q (r + 1) * M ≤ 1 / 12 :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hM) (paperAlpha_pos hqr).le).trans
      (paperAlpha_mul_configuration_le hqr hH)
  exact colour_collision_bound_at_exponents_paper_threshold hqr hn hh hH hm hM
    (a := 0) (by linarith only [hα, hαM]) A p
    (by simpa only [neg_zero, Real.rpow_zero, mul_one] using hA) hp

end Arxiv2411_18291
