import ErdosProblems.Erdos421.LargePrimeCofactors
import ErdosProblems.Erdos421.PositiveDivisorWindows

/-! # Merging a prime factor into a finite divisor coefficient -/

namespace Erdos421

noncomputable def primeDivisorConvolution (P : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, if p ∣ n then a (n / p) else 0

theorem primeDivisorConvolution_rough (P : Finset ℕ) (z n : ℕ) :
    primeDivisorConvolution P (fun m ↦ roughIndicator m z) n = primeCofactorWeight P z n := rfl

theorem primeDivisorConvolution_action (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (a f : ℕ → ℝ) (B : ℕ) :
    (∑ n ∈ Finset.Icc 1 B, primeDivisorConvolution P a n * f n) =
      ∑ p ∈ P, ∑ d ∈ Finset.Icc 1 (B / p), a d * f (p * d) := by
  simp only [primeDivisorConvolution, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← sum_positive_multiples (fun n ↦ a (n / p) * f n) (hP p hp) B]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.mul_div_right d (hP p hp)]

theorem primeDivisorConvolution_support (P : Finset ℕ) (a : ℕ → ℝ) {Q D n : ℕ}
    (hP : ∀ p ∈ P, p ≤ Q) (ha : ∀ d, D < d → a d = 0) (hn : Q * D < n) :
    primeDivisorConvolution P a n = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  split_ifs with hpn
  · apply ha
    by_contra h
    have hm := Nat.mul_le_mul (hP p hp) (show n / p ≤ D by omega)
    rw [Nat.mul_div_cancel' hpn] at hm
    omega
  · rfl

theorem primeDivisorConvolution_truncated_action (P : Finset ℕ) (a f : ℕ → ℝ)
    {Q D : ℕ} (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (ha : ∀ d, D < d → a d = 0) :
    (∑ n ∈ Finset.Icc 1 (Q * D), primeDivisorConvolution P a n * f n) =
      ∑ p ∈ P, ∑ d ∈ Finset.Icc 1 D, a d * f (p * d) := by
  rw [primeDivisorConvolution_action P (fun p hp ↦ (hP p hp).1)]
  apply Finset.sum_congr rfl
  intro p hp
  have hlen : D ≤ Q * D / p := (Nat.le_div_iff_mul_le (hP p hp).1).mpr
    (by simpa only [mul_comm D p] using Nat.mul_le_mul_right D (hP p hp).2)
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hlen)
  intro d hd hnot
  have hgt : D < d := by
    have hpos := (Finset.mem_Icc.mp hd).1
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨hpos, by omega⟩)
  rw [ha d hgt, zero_mul]

theorem primeDivisorConvolution_main (P : Finset ℕ) (a : ℕ → ℝ) {Q D : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (ha : ∀ d, D < d → a d = 0) :
    (∑ n ∈ Finset.Icc 1 (Q * D), primeDivisorConvolution P a n / (n : ℝ)) =
      (∑ p ∈ P, (p : ℝ)⁻¹) * (∑ d ∈ Finset.Icc 1 D, a d / (d : ℝ)) := by
  simp only [div_eq_mul_inv]
  rw [primeDivisorConvolution_truncated_action P a (fun n ↦ (n : ℝ)⁻¹) hP ha]
  simp only [Nat.cast_mul, mul_inv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro d hd
  ring

end Erdos421
