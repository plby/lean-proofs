import Mathlib

/-! # Integer comparisons used in the sparse-cut estimates

Each lemma takes the raw combinatorial charge estimate explicitly. The
graph-theoretic hypotheses producing that estimate are proved separately.
-/

namespace Erdos1010.ChargeArithmetic

lemma balanced_large {r D k q C : ℤ} (hk : 1 ≤ k) (hD : 2 * k + 1 ≤ D)
    (hr : D + 2 ≤ r) (hq : q ≤ r + D - 1)
    (hC : k * C ≤ k ^ 2 * q + D * (D - 1)) : C ≤ r * D := by
  let b := D - 2 * k - 1
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hk0 : 0 ≤ k - 1 := by omega
  have hk2 : 0 ≤ 2 * k ^ 2 - 1 := by nlinarith
  have hpoly : 0 ≤ b ^ 2 * (k - 1) + b * (2 * k ^ 2 - 1) + k ^ 2 + k := by
    positivity
  have hslack : 0 ≤ (r - D - 2) * k * (D - k) := by
    have : 0 ≤ r - D - 2 := by omega
    have : 0 ≤ D - k := by omega
    positivity
  have hid : r * k * (D - k) - (D - 1) * (k ^ 2 + D) =
      b ^ 2 * (k - 1) + b * (2 * k ^ 2 - 1) + k ^ 2 + k +
        (r - D - 2) * k * (D - k) := by dsimp [b]; ring
  have hq' := mul_le_mul_of_nonneg_left hq (sq_nonneg k)
  have hbound : k * C ≤ k * (r * D) := by nlinarith
  exact (mul_le_mul_iff_right₀ (show 0 < k by omega)).mp hbound

lemma balanced_equal {r k q C : ℤ} (hk : 0 ≤ k) (hr : 2 * k + 2 ≤ r)
    (hq : q ≤ r + 2 * k - 1) (hC : C ≤ k * q + 2 * k) : C ≤ r * (2 * k) := by
  have hq' := mul_le_mul_of_nonneg_left hq hk
  have hslack := mul_nonneg hk (show 0 ≤ r - 2 * k - 1 by omega)
  nlinarith

lemma balanced_gap_single {r k q p C : ℤ} (hk : 2 ≤ k) (hr : 2 * k + 1 ≤ r)
    (hq : q ≤ r + 2 * k - 2) (hp : p ≤ r - k)
    (hC : C ≤ (k - 1) * q + p + (k - 1) + (2 * k - 1)) :
    C ≤ r * (2 * k - 1) := by
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ k - 1 by omega)
  have hslack := mul_nonneg (show 0 ≤ k - 1 by omega)
    (show 0 ≤ r - 2 * k by omega)
  nlinarith

lemma balanced_gap_double_two {r q pA pB C : ℤ} (hq : q ≤ r + 2)
    (hpA : pA ≤ r - 2) (hpB : pB ≤ r - 2)
    (hC : C ≤ q + pA + pB + 2) : C ≤ r * 3 := by omega

lemma balanced_gap_double {r k q p C : ℤ} (hk : 3 ≤ k) (hr : 2 * k + 1 ≤ r)
    (hq : q ≤ r + 2 * k - 2) (hp : p ≤ 2 * (r - k))
    (hC : C ≤ 2 * q + (k - 2) * p + 2 * k - 2) :
    C ≤ r * (2 * k - 1) := by
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ k - 2 by omega)
  have hpoly : 0 ≤ 2 * (k - 3) ^ 2 + 4 * (k - 3) + 1 := by positivity
  nlinarith

lemma balanced_dominant {r k h q C : ℤ} (hk : 1 ≤ k) (hh : 1 ≤ h)
    (hhk : h ≤ k - 2) (hr : k + h + 2 ≤ r) (hq : q ≤ r + k + h - 1)
    (hC : C ≤ (h + 1) * q + (k - h - 1) * (r - k) + h + k - 1) :
    C ≤ r * (k + h) := by
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ h + 1 by omega)
  have hslack := mul_nonneg (show 0 ≤ h by omega)
    (show 0 ≤ r - k - h - 2 by omega)
  have hpoly := mul_nonneg (show 0 ≤ k - 1 by omega)
    (show 0 ≤ k - h - 2 by omega)
  nlinarith

lemma balanced_star_large {r D q p C : ℤ} (hD : 4 ≤ D)
    (hq : q ≤ r + D - 1) (hp : p ≤ r - D)
    (hC : C ≤ (D - 2) * p + 2 * q) : C ≤ r * D := by
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ D - 2 by omega)
  have hpoly := mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ D - 4 by omega)
  nlinarith

end Erdos1010.ChargeArithmetic
