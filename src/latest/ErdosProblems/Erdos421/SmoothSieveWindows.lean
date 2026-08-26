import ErdosProblems.Erdos421.CanonicalSieveWindowMean

/-! # Pointwise upper and lower bounds for actual smooth rough-number counts -/

namespace Erdos421

noncomputable def additiveRoughWindow (B z : ℕ) (Y x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 B, (additiveIntegerWeight Y x n).re * roughIndicator n z

theorem additiveIntegerWeight_re_nonneg {Y : ℝ} (hY : 0 < Y) (x : ℝ) (n : ℕ) :
    0 ≤ (additiveIntegerWeight Y x n).re := by
  have h := (oneSidedSchwartzWindow_real_nonneg ((x - n) / Y)).2
  simp only [additiveIntegerWeight, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (inv_nonneg.mpr hY.le) h

theorem finite_sieve_window_identity (a : ℕ → ℝ) (M : ℕ) {Y x : ℝ}
    (hY : 0 < Y) (hx : 0 ≤ x) {B : ℕ} (hB : x + Y ≤ B) :
    (∑ m ∈ Finset.Icc 1 M, a m *
      (additiveDivisorWindow oneSidedSchwartzWindow Y x m).re) =
        ∑ n ∈ Finset.Icc 1 B, (additiveIntegerWeight Y x n).re *
          ∑ m ∈ Finset.Icc 1 M, if m ∣ n then a m else 0 := by
  have hwindow (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      (additiveDivisorWindow oneSidedSchwartzWindow Y x m).re =
        ∑ n ∈ Finset.Icc 1 B, if m ∣ n then (additiveIntegerWeight Y x n).re else 0 := by
    rw [additiveDivisorWindow_positive_sum hY hx (Finset.mem_Icc.mp hm).1 hB, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> rfl
  calc
    _ = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 B,
        a m * (if m ∣ n then (additiveIntegerWeight Y x n).re else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hwindow m hm, Finset.mul_sum]
    _ = ∑ n ∈ Finset.Icc 1 B, ∑ m ∈ Finset.Icc 1 M,
        a m * (if m ∣ n then (additiveIntegerWeight Y x n).re else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      split_ifs <;> ring

theorem canonicalUpperSieve_pointwise {D : ℕ} (hD : 1 ≤ D) (z n : ℕ) :
    roughIndicator n z ≤
      ∑ d ∈ Finset.Icc 1 (D ^ 2), if d ∣ n then canonicalUpperSieve D z d else 0 := by
  have h := canonicalUpper_sum_truncate D z (fun d ↦ if d ∣ n then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [← h]
  exact upper_sieve_pointwise _ (canonicalUpperSieve_isUpper hD z) n z

theorem additiveRoughWindow_upper {D : ℕ} (hD : 1 ≤ D) (z : ℕ) {Y x : ℝ}
    (hY : 0 < Y) (hx : 0 ≤ x) {B : ℕ} (hB : x + Y ≤ B) :
    additiveRoughWindow B z Y x ≤
      ∑ m ∈ Finset.Icc 1 (D ^ 2), canonicalUpperSieve D z m *
        (additiveDivisorWindow oneSidedSchwartzWindow Y x m).re := by
  rw [finite_sieve_window_identity _ _ hY hx hB]
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_left (canonicalUpperSieve_pointwise hD z n)
    (additiveIntegerWeight_re_nonneg hY x n)

theorem additiveRoughWindow_lower {D z : ℕ} (hD : 1 ≤ D) (hz : 1 ≤ z) {Y x : ℝ}
    (hY : 0 < Y) (hx : 0 ≤ x) {B : ℕ} (hB : x + Y ≤ B) :
    (∑ m ∈ Finset.Icc 1 (z * D ^ 2), lowerSieveCoefficient D z m *
      (additiveDivisorWindow oneSidedSchwartzWindow Y x m).re) ≤ additiveRoughWindow B z Y x := by
  rw [finite_sieve_window_identity _ _ hY hx hB]
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_left (lowerSieveCoefficient_pointwise hD hz n)
    (additiveIntegerWeight_re_nonneg hY x n)

end Erdos421
