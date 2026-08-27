import Arxiv.Arxiv2411_18291.FiniteTypicalHostNumerics
import Arxiv.Arxiv2411_18291.NearFrameCandidates
import Arxiv.Arxiv2411_18291.ExplicitBoostSize

/-! # Explicit budgets for the near frame of a small exchange -/

noncomputable section

namespace Arxiv2411_18291

theorem q_le_choose_succ {q r : ℕ} (hqr : r + 1 < q) : q ≤ q.choose (r + 1) := by
  induction q with
  | zero => omega
  | succ q ih =>
    by_cases heq : r + 1 = q
    · rw [heq, Nat.choose_succ_self_right]
    · have hlt : r + 1 < q := by omega
      have hh := ih hlt
      have hp := Nat.choose_pos (show r ≤ q by omega)
      rw [Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one]
      omega

theorem near_frame_reciprocal_bound {q r h : ℕ} (hqr : r + 1 < q)
    (hsq : q.choose (r + 1) * q.choose (r + 1) ≤ h) :
    (4 * (q - (r + 1)).factorial * 2 ^ (q.choose (r + 1) - 1)) ^ q.choose (r + 1) ≤
      (4 * q) ^ (10 * (q + h)) := by
  have hk := Nat.choose_pos hqr.le
  have hqk := q_le_choose_succ hqr
  have hfac : (q - (r + 1)).factorial ≤ (4 * q) ^ q :=
    ((Nat.factorial_le (Nat.sub_le q (r + 1))).trans (Nat.factorial_le_pow q)).trans
      (Nat.pow_le_pow_left (by omega) q)
  have hbase : 4 * (q - (r + 1)).factorial * 2 ^ (q.choose (r + 1) - 1) ≤
      (4 * q) ^ (q + q.choose (r + 1)) := by
    calc
      _ ≤ (4 * q) ^ 1 * (4 * q) ^ q * (4 * q) ^ (q.choose (r + 1) - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by simp only [pow_one]; omega) hfac)
          (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hqkh := (Nat.mul_le_mul_right (q.choose (r + 1)) hqk).trans hsq
  calc
    _ ≤ ((4 * q) ^ (q + q.choose (r + 1))) ^ q.choose (r + 1) :=
      Nat.pow_le_pow_left hbase _
    _ = (4 * q) ^ ((q + q.choose (r + 1)) * q.choose (r + 1)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith only [hsq, hqkh])

theorem near_frame_collision_coefficient_bound {q r h : ℕ} (hqr : r + 1 < q)
    (hsq : q.choose (r + 1) * q.choose (r + 1) ≤ h) :
    4 * (q + q.choose (r + 1) * q) * (q - (r + 1)).factorial *
      2 ^ (q.choose (r + 1) - 1) ≤ (4 * q) ^ (10 * (q + h)) := by
  have hk := Nat.choose_pos hqr.le
  have hqk := q_le_choose_succ hqr
  have hkh : q.choose (r + 1) ≤ h :=
    (Nat.le_mul_of_pos_right _ hk).trans hsq
  have hU : q + q.choose (r + 1) * q ≤ 2 * h := by
    have hqkh := (Nat.mul_le_mul_left (q.choose (r + 1)) hqk).trans hsq
    omega
  have hhpow : h ≤ (4 * q) ^ h :=
    (Nat.lt_two_pow_self (n := h)).le.trans (Nat.pow_le_pow_left (by omega) h)
  have hfac : (q - (r + 1)).factorial ≤ (4 * q) ^ q :=
    ((Nat.factorial_le (Nat.sub_le q (r + 1))).trans (Nat.factorial_le_pow q)).trans
      (Nat.pow_le_pow_left (by omega) q)
  have h8 : 8 * h ≤ (4 * q) ^ 1 * (4 * q) ^ h :=
    Nat.mul_le_mul (by simp only [pow_one]; omega) hhpow
  calc
    _ ≤ ((4 * q) ^ 1 * (4 * q) ^ h) * (4 * q) ^ q *
        (4 * q) ^ (q.choose (r + 1) - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by nlinarith only [hU, h8]) hfac)
        (Nat.pow_le_pow_left (by omega) _)
    _ = (4 * q) ^ (1 + h + q + (q.choose (r + 1) - 1)) := by
      rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem near_frame_density_constant_paper_threshold {q r n h : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hsq : q.choose (r + 1) * q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    (3 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 40 : ℝ)) ≤
      nearFrameDensityConstant (1 / 2) q (r + 1) := by
  have hk := Nat.choose_pos hqr.le
  have hh : 1 ≤ h := by nlinarith only [hk, hsq]
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  let C : ℝ := 4 * (q - (r + 1)).factorial * 2 ^ (q.choose (r + 1) - 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hcbase : C ^ q.choose (r + 1) ≤ (4 * q : ℝ) ^ (10 * (q + h)) := by
    dsimp only [C]
    exact_mod_cast near_frame_reciprocal_bound hqr hsq
  have hc := hcbase.trans (paper_host_configuration_growth hqr hn hh hH)
  have hm := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg hn0.le (-(1 / 40 : ℝ)))
  rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hm
  have hi : (n : ℝ) ^ (-(1 / 40 : ℝ)) ≤ 1 / C ^ q.choose (r + 1) := by
    apply (le_div_iff₀ (pow_pos hC _)).mpr
    simpa only [mul_comm] using hm
  have heq : nearFrameDensityConstant (1 / 2) q (r + 1) =
      (3 / 4 : ℝ) * (1 / C ^ q.choose (r + 1)) := by
    unfold nearFrameDensityConstant
    have hiC : (1 / 2 : ℝ) ^ (q.choose (r + 1) - 1) /
        (4 * (q - (r + 1)).factorial) = 1 / C := by
      dsimp only [C]
      rw [one_div_pow]
      field_simp
    rw [hiC, one_div_pow]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hi (by norm_num)

theorem near_frame_collision_bound_paper_threshold {q r n h : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hsq : q.choose (r + 1) * q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    (q + q.choose (r + 1) * q : ℕ) * (n : ℝ) ^ (q - (r + 1) - 1) ≤
      (((1 / 2 : ℝ) ^ (q.choose (r + 1) - 1) / (2 * (q - (r + 1)).factorial)) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) * ((q.choose (r + 1) - 1 : ℕ) : ℝ))) *
          (n : ℝ) ^ (q - (r + 1))) / 2 := by
  have hk := Nat.choose_pos hqr.le
  have hkh : q.choose (r + 1) ≤ h := (Nat.le_mul_of_pos_right _ hk).trans hsq
  have hh : 1 ≤ h := by omega
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  let c : ℝ := (1 / 2 : ℝ) ^ (q.choose (r + 1) - 1) / (2 * (q - (r + 1)).factorial)
  let γ := paperAlpha q (r + 1) * ((q.choose (r + 1) - 1 : ℕ) : ℝ)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hγ : γ ≤ 1 / 12 :=
    (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr ((Nat.sub_le _ _).trans hkh)) (paperAlpha_pos hqr).le).trans
      (paperAlpha_mul_configuration_le hqr hH)
  have hcoef : (2 : ℝ) * (q + q.choose (r + 1) * q : ℕ) / c ≤
      (4 * q : ℝ) ^ (10 * (q + h)) := by
    have heq : (2 : ℝ) * (q + q.choose (r + 1) * q : ℕ) / c =
        (4 * (q + q.choose (r + 1) * q) * (q - (r + 1)).factorial *
          2 ^ (q.choose (r + 1) - 1) : ℕ) := by
      dsimp only [c]
      push_cast
      rw [one_div_pow]
      field_simp
      ring
    rw [heq]
    exact_mod_cast near_frame_collision_coefficient_bound hqr hsq
  have hlarge : (2 : ℝ) * (q + q.choose (r + 1) * q : ℕ) / c ≤
      (n : ℝ) ^ (1 - γ) :=
    (hcoef.trans (paper_host_configuration_growth hqr hn hh hH)).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hγ]))
  have hsmall : (2 : ℝ) * (q + q.choose (r + 1) * q : ℕ) ≤
      c * (n : ℝ) ^ (-γ) * n := by
    have hb := (div_le_iff₀ hc).mp hlarge
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add_one hn0.ne'] at hb
    nlinarith only [hb]
  have hp := mul_le_mul_of_nonneg_right hsmall
    (pow_nonneg hn0.le (q - (r + 1) - 1))
  have hpow : (n : ℝ) * (n : ℝ) ^ (q - (r + 1) - 1) = (n : ℝ) ^ (q - (r + 1)) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q - (r + 1))]
  rw [mul_assoc (c * (n : ℝ) ^ (-γ)) (n : ℝ), hpow] at hp
  change _ ≤ (c * (n : ℝ) ^ (-γ) * (n : ℝ) ^ (q - (r + 1))) / 2
  linarith only [hp]

end Arxiv2411_18291
