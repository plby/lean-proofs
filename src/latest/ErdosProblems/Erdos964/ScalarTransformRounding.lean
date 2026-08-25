import ErdosProblems.Erdos964.ScalarSieveCandidate

/-!
# Rounding the strict endpoint in the transformed coefficient

The logarithmic distance from `(R-1)/r` to `R/r` is at most `log 2`.
The quadratic primitive consequently changes by a bounded amount.
-/

namespace Erdos964

theorem scalar_transform_log_endpoint_bounds (R r : ℕ) (hr : 0 < r) (hrR : r < R) :
    let Q := (R - 1) / r
    0 ≤ Real.log Q ∧ Real.log Q ≤ Real.log (R : ℝ) - Real.log r ∧
      Real.log (R : ℝ) - Real.log r ≤ Real.log R ∧
      (Real.log (R : ℝ) - Real.log r) - Real.log Q ≤ Real.log 2 := by
  let Q := (R - 1) / r
  have hQ : 1 ≤ Q := Nat.div_pos (by omega) hr
  have hprod : r * Q ≤ R - 1 := Nat.mul_div_le (R - 1) r
  have hround : R ≤ 2 * (r * Q) := by
    have hrem := Nat.mod_lt (R - 1) hr
    have hdecomp := Nat.mod_add_div (R - 1) r
    have hmul := Nat.mul_le_mul_left r hQ
    change r * 1 ≤ r * ((R - 1) / r) at hmul
    dsimp only [Q]
    omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hr.trans hrR
  have hlo := Real.log_le_log (mul_pos hrpos hQpos)
    (show (r : ℝ) * Q ≤ R by exact_mod_cast hprod.trans (Nat.sub_le R 1))
  have hhi := Real.log_le_log hRpos
    (show (R : ℝ) ≤ 2 * ((r : ℝ) * Q) by exact_mod_cast hround)
  rw [Real.log_mul hrpos.ne' hQpos.ne'] at hlo
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_pos hrpos hQpos).ne',
    Real.log_mul hrpos.ne' hQpos.ne'] at hhi
  have hlogr := Real.log_natCast_nonneg r
  have hlogQ := Real.log_natCast_nonneg Q
  exact ⟨hlogQ, by linarith, by linarith, by linarith⟩

theorem linear_primitive_truncation_error (L x q e : ℝ) (hL : 0 < L)
    (hq : 0 ≤ q) (hqx : q ≤ x) (hxL : x ≤ L) (hgap : x - q ≤ e) :
    |((1 + 6 * x / L) * q - (3 / L) * q ^ 2) -
      L * ggpyPolynomialPrimitive (x / L)| ≤ 4 * e := by
  have hd : 0 ≤ x - q := sub_nonneg.mpr hqx
  have hdL : x - q ≤ L := by linarith
  have hsquare : (x - q) ^ 2 / L ≤ x - q := by
    apply (div_le_iff₀ hL).mpr
    nlinarith
  have hid : L * ggpyPolynomialPrimitive (x / L) -
      ((1 + 6 * x / L) * q - (3 / L) * q ^ 2) =
      (x - q) + 3 * (x - q) ^ 2 / L := by
    unfold ggpyPolynomialPrimitive
    field_simp
    ring
  rw [abs_sub_comm, hid, abs_of_nonneg (by positivity)]
  rw [mul_div_assoc]
  linarith

theorem scalar_transform_primitive_rounding (R r : ℕ) (hr : 0 < r) (hrR : r < R) :
    let Q := (R - 1) / r
    |((7 - 6 * Real.log r / Real.log R) * Real.log Q -
        (3 / Real.log R) * (Real.log Q) ^ 2) -
      Real.log R * ggpyPolynomialPrimitive (Real.log ((R : ℝ) / r) / Real.log R)| ≤
      4 * Real.log 2 := by
  have hR : (1 : ℝ) < R := by exact_mod_cast (show 1 < R by omega)
  have hlogR := Real.log_pos hR
  have hbounds := scalar_transform_log_endpoint_bounds R r hr hrR
  have h := linear_primitive_truncation_error (Real.log R) (Real.log R - Real.log r)
    (Real.log ((R - 1) / r : ℕ)) (Real.log 2) hlogR hbounds.1 hbounds.2.1
    hbounds.2.2.1 hbounds.2.2.2
  have hlinear : 1 + 6 * (Real.log R - Real.log r) / Real.log R =
      7 - 6 * Real.log r / Real.log R := by
    field_simp
    ring
  rw [hlinear] at h
  rw [Real.log_div (by exact_mod_cast (show R ≠ 0 by omega)) (by exact_mod_cast hr.ne')]
  exact h

end Erdos964
