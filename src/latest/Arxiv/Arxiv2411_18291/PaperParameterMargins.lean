import Arxiv.Arxiv2411_18291.PaperSizeParameters

/-! # The configuration and density margins discussed in Section 10 -/

noncomputable section

namespace Arxiv2411_18291

def paperColourCount (q r M : ℕ) : ℕ := 20 * q ^ 2 * paperInverseAlpha q r * M

theorem twelve_mul_configuration_le_inverseAlpha (q r M : ℕ)
    (hM : M ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2) :
    12 * M ≤ paperInverseAlpha q r := by
  calc
    _ ≤ 12 * (3 * (2 * q) ^ r * (q.choose r) ^ 2) := Nat.mul_le_mul_left 12 hM
    _ = _ := by unfold paperInverseAlpha; ring

theorem configuration_lt_inverseAlpha {q r M : ℕ} (hqr : r < q)
    (hM : M ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2) : M < paperInverseAlpha q r := by
  have h := twelve_mul_configuration_le_inverseAlpha q r M hM
  have hp := paperInverseAlpha_pos hqr
  omega

theorem paperAlpha_mul_configuration_le {q r M : ℕ} (hqr : r < q)
    (hM : M ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2) :
    paperAlpha q r * M ≤ 1 / 12 := by
  have hm : (12 : ℝ) * M ≤ paperInverseAlpha q r := by
    exact_mod_cast twelve_mul_configuration_le_inverseAlpha q r M hM
  have hh := mul_le_mul_of_nonneg_left hm (paperAlpha_pos hqr).le
  rw [paperAlpha_mul_inverse hqr] at hh
  linarith only [hh]

theorem two_mul_choose_lt_two_mul_pow {q r : ℕ} (hr : 2 ≤ r) (hqr : r < q) :
    2 * q.choose r < (2 * q) ^ r := by
  have hq : 0 < q := by omega
  have hp : 2 < 2 ^ r := by
    simpa only [pow_one] using Nat.pow_lt_pow_right (by decide : 1 < 2)
      (show 1 < r by omega)
  calc
    _ ≤ 2 * q ^ r := Nat.mul_le_mul_left 2 (Nat.choose_le_pow q r)
    _ < 2 ^ r * q ^ r := Nat.mul_lt_mul_of_pos_right hp (pow_pos hq r)
    _ = _ := (mul_pow 2 q r).symm

theorem paperAlpha_mul_choose_lt_half_rho {q r : ℕ} (hr : 2 ≤ r) (hqr : r < q) :
    (q.choose r : ℝ) * paperAlpha q r < paperRho q r / 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hp : 0 < (2 * q : ℝ) ^ r := by positivity
  have hk : 2 * (q.choose r : ℝ) < (2 * q : ℝ) ^ r := by
    exact_mod_cast two_mul_choose_lt_two_mul_pow hr hqr
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ = (paperRho q r * (2 * q.choose r)) / (2 * q : ℝ) ^ r := by
      unfold paperAlpha
      ring
    _ < _ := (div_lt_iff₀ hp).mpr (mul_lt_mul_of_pos_left hk (paperRho_pos hqr))

/-- In rank one the source's strict margin is an equality; the main rank-one proof is separate. -/
theorem paperAlpha_mul_choose_rankOne {q : ℕ} (hq : 1 < q) :
    (q.choose 1 : ℝ) * paperAlpha q 1 = paperRho q 1 / 2 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [paperAlpha, pow_one, Nat.choose_one_right]
  field_simp

theorem paperColourCount_bound (q r M : ℕ)
    (hM : M ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2) :
    paperColourCount q r M ≤ 2160 * q ^ 2 * (2 * q) ^ (2 * r) * (q.choose r) ^ 4 := by
  calc
    _ ≤ 20 * q ^ 2 * paperInverseAlpha q r *
        (3 * (2 * q) ^ r * (q.choose r) ^ 2) := Nat.mul_le_mul_left _ hM
    _ = _ := by
      unfold paperInverseAlpha
      rw [show 2 * r = r * 2 by omega, pow_mul]
      ring

end Arxiv2411_18291
