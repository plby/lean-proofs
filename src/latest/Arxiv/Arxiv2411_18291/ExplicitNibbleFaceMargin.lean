import Arxiv.Arxiv2411_18291.ExplicitNibbleGrowth

/-! # The coefficient in the nibble's face-concentration margin -/

namespace Arxiv2411_18291

theorem nibble_face_constant_nat_le {q k d f : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hf : 1 ≤ f) (hd : d ≤ q) :
    8 * (4 * d * (1 + 128 * k) * k + (d + 4 * k * f)) ≤ 4168 * q * k ^ 2 * f := by
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk
  have hfirst : 4 * d * (1 + 128 * k) * k ≤ 516 * q * k ^ 2 * f := by
    calc
      _ ≤ 4 * q * (129 * k) * k := Nat.mul_le_mul_right k
        (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hd) (by omega))
      _ = 516 * q * k ^ 2 := by ring
      _ ≤ _ := by simpa using Nat.mul_le_mul_left (516 * q * k ^ 2) hf
  have hmiddle : d ≤ q * k ^ 2 * f := by
    calc
      _ ≤ q := hd
      _ ≤ q * k ^ 2 := by simpa using Nat.mul_le_mul_left q hk2
      _ ≤ _ := by simpa using Nat.mul_le_mul_left (q * k ^ 2) hf
  have hkq : k ≤ q * k ^ 2 := by
    have hh : k ≤ k ^ 2 := by nlinarith only [hk]
    exact hh.trans (by simpa using Nat.mul_le_mul_right (k ^ 2) hq)
  have hlast := Nat.mul_le_mul_right f (Nat.mul_le_mul_left 4 hkq)
  nlinarith only [hfirst, hmiddle, hlast]

theorem paper_nibble_face_constant {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    let k := q.choose r
    let d := q - r + 1
    let cg : ℝ := 1 / (4 * r.factorial)
    8 * (4 * (d : ℝ) * (1 + 128 * k) * k + ((d : ℝ) + k / cg)) ≤
      (n : ℝ) ^ paperRho q r := by
  dsimp only
  have hnat := nibble_face_constant_nat_le (by omega : 1 ≤ q)
    (Nat.choose_pos hqr.le) (Nat.factorial_pos r) (by omega : q - r + 1 ≤ q)
  have hnum := paper_threshold_nibble_monomial (C := 4168) (i := 1) (j := 2)
    (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
  calc
    _ = ((8 * (4 * (q - r + 1) * (1 + 128 * q.choose r) * q.choose r +
        ((q - r + 1) + 4 * q.choose r * r.factorial)) : ℕ) : ℝ) := by
      push_cast
      rw [div_div_eq_mul_div, div_one]
      ring
    _ ≤ (4168 * q * (q.choose r) ^ 2 * r.factorial : ℕ) := by exact_mod_cast hnat
    _ ≤ _ := by simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, pow_one] using hnum

end Arxiv2411_18291
