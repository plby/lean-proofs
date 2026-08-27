import Arxiv.Arxiv2411_18291.ExplicitReserveTail
import Arxiv.Arxiv2411_18291.AsymptoticPrescribedGreedy

/-! # The greedy cover's finite density margin -/

namespace Arxiv2411_18291

theorem cover_smallness_constant_le {q K d : ℕ} (hq : 2 ≤ q) (hK : 1 ≤ K)
    (hd : d ≤ q) : 2 * (K + 4 * K ^ 2 * d.factorial) ≤
      (4 * q) ^ (10 * (q + K)) := by
  have hfac : 1 ≤ d.factorial := Nat.factorial_pos d
  have hKK : K ≤ K ^ 2 := by nlinarith only [hK]
  have hKKF : K ≤ K ^ 2 * d.factorial := hKK.trans
    (by simpa using Nat.mul_le_mul_left (K ^ 2) hfac)
  have hKpow : K ≤ (4 * q) ^ K :=
    (Nat.lt_two_pow_self (n := K)).le.trans (Nat.pow_le_pow_left (by omega) K)
  have hf : d.factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hd).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  have hten : 10 ≤ (4 * q) ^ 2 := by nlinarith only [hq]
  calc
    _ ≤ 10 * K ^ 2 * d.factorial := by nlinarith only [hKKF]
    _ ≤ (4 * q) ^ 2 * ((4 * q) ^ K) ^ 2 * (4 * q) ^ q :=
      Nat.mul_le_mul (Nat.mul_le_mul hten (Nat.pow_le_pow_left hKpow 2)) hf
    _ = (4 * q) ^ (2 + K * 2 + q) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem paper_cover_smallness {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let K := q.choose (r + 1)
    let a : ℝ := K * paperRho q (r + 1)
    (K : ℝ) * ((n : ℝ) ^ (-(3 * a)) + K *
      (4 * (r + 1).factorial * (n : ℝ) ^ (-(3 * a)) / (n : ℝ) ^ (-a))) ≤
      (n : ℝ) ^ (-a) / 2 := by
  dsimp only
  let K := q.choose (r + 1)
  let a : ℝ := K * paperRho q (r + 1)
  have hK : 1 ≤ K := Nat.choose_pos hqr.le
  have hρ : 0 < paperRho q (r + 1) := paperRho_pos hqr
  have hρa : paperRho q (r + 1) ≤ a := by
    have hh := mul_le_mul_of_nonneg_right (by exact_mod_cast hK : (1 : ℝ) ≤ K) hρ.le
    simpa only [one_mul] using hh
  have ha : 0 < a := hρ.trans_le hρa
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hconst := cover_smallness_constant_le (by omega : 2 ≤ q) hK hqr.le
  have hbound : (2 * (K + 4 * K ^ 2 * (r + 1).factorial) : ℝ) ≤ (n : ℝ) ^ a := by
    calc
      _ ≤ (4 * q : ℝ) ^ (10 * (q + K)) := by exact_mod_cast hconst
      _ ≤ _ := paper_threshold_reserve_growth_le_rpow hqr hn hρa
  have hη : 0 < (n : ℝ) ^ (-a) := Real.rpow_pos_of_pos hn0 _
  have hmul := mul_le_mul_of_nonneg_right hbound hη.le
  rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hmul
  have hdecay : (n : ℝ) ^ (-(2 * a)) ≤ (n : ℝ) ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [ha])
  have hscaled : (K : ℝ) * ((n : ℝ) ^ (-(2 * a)) + K *
      (4 * (r + 1).factorial * (n : ℝ) ^ (-a))) ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg K)
    nlinarith only [hmul, hh]
  have hdiv : ((K : ℝ) * ((n : ℝ) ^ (-(3 * a)) + K *
      (4 * (r + 1).factorial * (n : ℝ) ^ (-(3 * a)) / (n : ℝ) ^ (-a)))) /
        (n : ℝ) ^ (-a) ≤ 1 / 2 := by
    rw [prescribed_smallness_scale hn0]
    have heq1 : 3 * a - a = 2 * a := by ring
    have heq2 : 3 * a - 2 * a = a := by ring
    rw [heq1, heq2]
    exact hscaled
  have hh := (div_le_iff₀ hη).mp hdiv
  change (K : ℝ) * ((n : ℝ) ^ (-(3 * a)) + K *
    (4 * (r + 1).factorial * (n : ℝ) ^ (-(3 * a)) / (n : ℝ) ^ (-a))) ≤
      (n : ℝ) ^ (-a) / 2
  linarith only [hh]

end Arxiv2411_18291
