import ErdosProblems.Erdos67b.MRFiniteRamareFactorization

/-!
# Exact rounded cofactor endpoint inequalities

The finite rectangle has endpoints `X / Q` and `(2 * X) / P`. Its ratio,
logarithmic scale, and available frequency window are controlled without
replacing these natural quotients by real quotients.
-/

namespace Erdos67b

noncomputable section

theorem mrCofactor_rectangle_lower_pos {P Q X : ℕ}
    (hP : 0 < P) (hPQ : P ≤ Q) (hQX : Q ≤ X) : 0 < X / Q :=
  Nat.div_pos hQX (hP.trans_le hPQ)

theorem mrCofactor_rectangle_endpoints_order {P Q X : ℕ}
    (hP : 0 < P) (hPQ : P ≤ Q) : X / Q ≤ (2 * X) / P := by
  apply (Nat.le_div_iff_mul_le hP).2
  calc
    (X / Q) * P ≤ (X / Q) * Q := Nat.mul_le_mul_left _ hPQ
    _ ≤ X := Nat.div_mul_le_self X Q
    _ ≤ 2 * X := by omega

theorem mrCofactor_rectangle_upper_le_eight_lower {P Q X : ℕ}
    (hP : 0 < P) (hPQ : P ≤ Q) (hQP : Q ≤ 2 * P) (hQX : Q ≤ X) :
    (2 * X) / P ≤ 8 * (X / Q) := by
  let Y := X / Q
  have hQ : 0 < Q := hP.trans_le hPQ
  have hY : 0 < Y := Nat.div_pos hQX hQ
  have hXlt : X < (Y + 1) * Q := (Nat.div_lt_iff_lt_mul hQ).1 (Nat.lt_succ_self Y)
  have hupper : (2 * X) / P < 4 * (Y + 1) := by
    apply (Nat.div_lt_iff_lt_mul hP).2
    have hprod := Nat.mul_le_mul_left (Y + 1) hQP
    nlinarith
  omega

theorem mrCofactor_rectangle_lower_sq_ge {Q X : ℕ}
    (hQ : 0 < Q) (hsize : 2 * Q ^ 2 ≤ X) : X ≤ (X / Q) ^ 2 := by
  let Y := X / Q
  have hYQ : 2 * Q ≤ Y := by
    apply (Nat.le_div_iff_mul_le hQ).2
    nlinarith
  have hY : 0 < Y := by omega
  have hXlt : X < (Y + 1) * Q := (Nat.div_lt_iff_lt_mul hQ).1 (Nat.lt_succ_self Y)
  calc
    X ≤ (Y + 1) * Q := hXlt.le
    _ ≤ (2 * Y) * Q := Nat.mul_le_mul_right Q (by omega)
    _ = (2 * Q) * Y := by ring
    _ ≤ Y * Y := Nat.mul_le_mul_right Y hYQ
    _ = (X / Q) ^ 2 := by dsimp only [Y]; ring

theorem mrCofactor_rectangle_log_lower {Q X : ℕ}
    (hQ : 0 < Q) (hsize : 2 * Q ^ 2 ≤ X) :
    Real.log (X : ℝ) ≤ 2 * Real.log (X / Q : ℕ) := by
  have hX : 0 < X := by nlinarith [sq_pos_of_pos hQ]
  have hsq := mrCofactor_rectangle_lower_sq_ge hQ hsize
  have hlog : Real.log (X : ℝ) ≤ Real.log (((X / Q : ℕ) : ℝ) ^ 2) :=
    Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast hsq)
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

theorem mrCofactor_rectangle_upper_twice_le {P X : ℕ} (hP : 4 ≤ P) :
    2 * ((2 * X) / P) ≤ X := by
  have hmul := Nat.div_mul_le_self (2 * X) P
  have hfour := Nat.mul_le_mul_left ((2 * X) / P) hP
  nlinarith

theorem mrCofactor_rectangle_frequency_window {P X : ℕ} (hP : 4 ≤ P)
    {t : ℝ} (ht : |t| ≤ (X : ℝ) / 2) : |t| + (((2 * X) / P : ℕ) : ℝ) ≤ X := by
  have hupper : 2 * (((2 * X) / P : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast mrCofactor_rectangle_upper_twice_le (X := X) hP
  linarith

end

end Erdos67b
